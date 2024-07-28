//! The memory module contains the [Memory] data structure and its functionality for the emulator.

use super::MEMORY_PROOF_SIZE;
use crate::{
    memory::page,
    types::{Address, DoubleWord, Gindex, Page, SharedCachedPage, Word},
    utils::keccak_concat_hashes,
};
use alloy_primitives::B256;
use anyhow::Result;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::{io::Read, rc::Rc};

/// The [Memory] struct represents the MIPS emulator's memory.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Memory {
    /// Map of generalized index -> the merkle root of each index. None if invalidated.
    pub nodes: FxHashMap<Gindex, Option<B256>>,
    /// Map of page indices to [CachedPage]s.
    pub pages: FxHashMap<u64, SharedCachedPage>,
    /// We store two caches upfront; we often read instructions from one page and reserve another
    /// for scratch memory. This prevents map lookups for each instruction.
    pub last_page: [(u64, Option<SharedCachedPage>); 2],
}

impl Default for Memory {
    fn default() -> Self {
        Self {
            nodes: FxHashMap::default(),
            pages: FxHashMap::default(),
            last_page: [(!0u64, None), (!0u64, None)],
        }
    }
}

impl Memory {
    /// Returns the number of allocated pages in memory.
    pub fn page_count(&self) -> usize {
        self.pages.len()
    }

    /// Invalidate a given memory address
    ///
    /// ### Takes
    /// - `address`: The address to invalidate.
    ///
    /// ### Returns
    /// - A [Result] indicating if the operation was successful.
    pub fn invalidate(&mut self, address: Address) -> Result<()> {
        if address & 0x3 != 0 {
            panic!("Unaligned memory access: {:x}", address);
        }

        // Find the page and invalidate the address within it.
        match self.page_lookup(address as u64 >> page::PAGE_ADDRESS_SIZE) {
            Some(page) => {
                let mut page = page.borrow_mut();
                let prev_valid = !page.valid[1];

                // Invalidate the address within the page.
                page.invalidate(address & page::PAGE_ADDRESS_MASK as u64)?;

                // If the page was already invalid before, then nodes to the memory
                // root will also still be invalid.
                if prev_valid {
                    return Ok(());
                }
            }
            None => {
                // Nothing to invalidate
                return Ok(());
            }
        }

        // Find the generalized index of the first page covering the address
        let mut g_index =
            (1u64 << (64 - page::PAGE_ADDRESS_SIZE)) | (address >> page::PAGE_ADDRESS_SIZE);
        // Invalidate all nodes in the branch
        while g_index > 0 {
            self.nodes.insert(g_index, None);
            g_index >>= 1;
        }

        Ok(())
    }

    /// Lookup a page in the [Memory]. This function will consult the cache before checking the
    /// maps, and will cache the page if it is not already cached.
    ///
    /// ### Takes
    /// - `page_index`: The page index to look up.
    ///
    /// ### Returns
    /// - A reference to the [CachedPage] if it exists.
    pub fn page_lookup(&mut self, page_index: u64) -> Option<SharedCachedPage> {
        // Check caches before maps
        if let Some((_, Some(page))) = self.last_page.iter().find(|(key, _)| *key == page_index) {
            Some(Rc::clone(page))
        } else if let Some(page) = self.pages.get(&page_index) {
            // Cache the page
            self.last_page[1] = self.last_page[0].clone();
            self.last_page[0] = (page_index, Some(page.clone()));

            Some(Rc::clone(page))
        } else {
            None
        }
    }

    pub fn merkleize_subtree(&mut self, g_index: Gindex) -> Result<B256> {
        // Fetch the amount of bits required to represent the generalized index
        let bits = 64 - g_index.leading_zeros() as usize;
        if bits > MEMORY_PROOF_SIZE {
            anyhow::bail!("Gindex is too deep")
        }

        if bits > page::PAGE_KEY_SIZE {
            let depth_into_page = bits - 1 - page::PAGE_KEY_SIZE;
            let page_index = (g_index >> depth_into_page) & page::PAGE_KEY_MASK as u64;
            return self.pages.get(&page_index).map_or(
                Ok(page::ZERO_HASHES[MEMORY_PROOF_SIZE - bits as usize]),
                |page| {
                    let page_g_index =
                        (1 << depth_into_page) | (g_index & ((1 << depth_into_page) - 1));
                    page.borrow_mut().merkleize_subtree(page_g_index)
                },
            );
        }

        if bits > page::PAGE_KEY_SIZE + 1 {
            anyhow::bail!("Cannot jump into intermediate node of page")
        }

        match self.nodes.get(&g_index) {
            Some(Some(node)) => return Ok(*node),
            None => return Ok(page::ZERO_HASHES[MEMORY_PROOF_SIZE - bits as usize]),
            _ => { /* noop */ }
        }

        let left = self.merkleize_subtree(g_index << 1)?;
        let right = self.merkleize_subtree((g_index << 1) | 1)?;
        let result = keccak_concat_hashes(left, right);

        self.nodes.insert(g_index, Some(result));

        Ok(result)
    }

    /// Compute the merkle root of the [Memory].
    ///
    /// ### Returns
    /// - The 32 byte merkle root hash of the [Memory].
    pub fn merkle_root(&mut self) -> Result<B256> {
        self.merkleize_subtree(1)
    }

    /// Compute the merkle proof for the given address in the [Memory].
    ///
    /// ### Takes
    /// - `address`: The address to compute the merkle proof for.
    ///
    /// ### Returns
    /// - The [MEMORY_PROOF_SIZE] byte merkle proof for the given address.
    pub fn merkle_proof(&mut self, address: Address) -> Result<[u8; MEMORY_PROOF_SIZE * 32]> {
        let proof = self.traverse_branch(1, address, 0)?;

        proof
            .into_iter()
            .flatten()
            .collect::<Vec<u8>>()
            .try_into()
            .map_err(|_| anyhow::anyhow!("Failed to convert proof to fixed array"))
    }

    /// Traverse a branch of the merkle tree, generating a proof for the given address.
    ///
    /// ### Takes
    /// - `parent`: The generalized index of the parent node.
    /// - `address`: The address to generate the proof for.
    /// - `depth`: The depth of the branch.
    ///
    /// ### Returns
    /// - The merkle proof for the given address.
    pub fn traverse_branch(
        &mut self,
        parent: Gindex,
        address: Address,
        depth: u8,
    ) -> Result<Vec<B256>> {
        if depth as usize == MEMORY_PROOF_SIZE - 1 {
            let mut proof = Vec::with_capacity(MEMORY_PROOF_SIZE);
            proof.push(self.merkleize_subtree(parent)?);
            return Ok(proof);
        }

        if depth as usize > MEMORY_PROOF_SIZE - 1 {
            anyhow::bail!("Traversed too deep")
        }

        let mut local = parent << 1;
        let mut sibling = local | 1;
        if address & (1 << (63 - depth)) != 0 {
            (local, sibling) = (sibling, local);
        }

        let mut proof = self.traverse_branch(local, address, depth + 1)?;
        let sibling_node = self.merkleize_subtree(sibling)?;
        proof.push(sibling_node);

        Ok(proof)
    }

    /// Set a 32 bit value in the [Memory] at a given address.
    /// This will invalidate the page at the given address, or allocate a new page if it does not
    /// exist.
    ///
    /// ### Takes
    /// - `address`: The address to set the value at.
    /// - `value`: The 32 bit value to set.
    ///
    /// ### Returns
    /// - A [Result] indicating if the operation was successful.
    #[inline(always)]
    pub fn set_memory_word(&mut self, address: Address, value: Word) -> Result<()> {
        // Address must be aligned to 4 bytes
        if address & 0x3 != 0 {
            anyhow::bail!("Unaligned memory access: {:x}", address);
        }

        let page_index = address >> page::PAGE_ADDRESS_SIZE as u64;
        let page_address = address as usize & page::PAGE_ADDRESS_MASK;

        // Attempt to look up the page.
        // - If it does exist, invalidate it before changing it.
        // - If it does not exist, allocate it.
        let page = self
            .page_lookup(page_index)
            .map(|page| {
                // If the page exists, invalidate it - the value will change.
                self.invalidate(address)?;
                Ok::<_, anyhow::Error>(page)
            })
            .unwrap_or_else(|| {
                let page = self.alloc_page(page_index)?;
                let _ = page.borrow_mut().invalidate(page_address as Address);
                Ok(page)
            })?;

        // Copy the 32 bit value into the page
        page.borrow_mut().data[page_address..page_address + 4]
            .copy_from_slice(&value.to_be_bytes());

        Ok(())
    }

    /// Retrieve a 32 bit value from the [Memory] at a given address.
    ///
    /// ### Takes
    /// - `address`: The [Address] to retrieve the value from.
    ///
    /// ### Returns
    /// - The 32 bit value at the given address.
    #[inline(always)]
    pub fn get_memory_word(&mut self, address: Address) -> Result<Word> {
        // Address must be aligned to 4 bytes
        if address & 0x3 != 0 {
            anyhow::bail!("Unaligned memory access: {:x}", address);
        }

        match self.page_lookup(address as u64 >> page::PAGE_ADDRESS_SIZE as u64) {
            Some(page) => {
                let page_address = address as usize & page::PAGE_ADDRESS_MASK;
                Ok(Word::from_be_bytes(
                    page.borrow().data[page_address..page_address + 4].try_into()?,
                ))
            }
            None => Ok(0),
        }
    }

    /// Set a 64 bit value in the [Memory] at a given address.
    /// This will invalidate the page at the given address, or allocate a new page if it does not
    /// exist.
    ///
    /// ### Takes
    /// - `address`: The address to set the value at.
    /// - `value`: The 64 bit value to set.
    ///
    /// ### Returns
    /// - A [Result] indicating if the operation was successful.
    #[inline(always)]
    pub fn set_memory_doubleword(&mut self, address: Address, value: DoubleWord) -> Result<()> {
        // Address must be aligned to 8 bytes or 4 bytes
        if (address & 0x7 != 0) && (address & 0x3 != 0) {
            anyhow::bail!("Unaligned memory access: {:x}", address);
        }

        let page_index = address >> page::PAGE_ADDRESS_SIZE as u64;
        let page_address = address as usize & page::PAGE_ADDRESS_MASK;

        // Attempt to look up the page.
        // - If it does exist, invalidate it before changing it.
        // - If it does not exist, allocate it.
        let page = self
            .page_lookup(page_index)
            .map(|page| {
                // If the page exists, invalidate it - the value will change.
                self.invalidate(address)?;
                Ok::<_, anyhow::Error>(page)
            })
            .unwrap_or_else(|| {
                let page = self.alloc_page(page_index)?;
                let _ = page.borrow_mut().invalidate(page_address as Address);
                Ok(page)
            })?;

        // Copy the 64 bit value into the page
        page.borrow_mut().data[page_address..page_address + 8]
            .copy_from_slice(&value.to_be_bytes());

        Ok(())
    }

    /// Retrieve a 64 bit value from the [Memory] at a given address.
    ///
    /// ### Takes
    /// - `address`: The [Address] to retrieve the value from.
    ///
    /// ### Returns
    /// - The 64 bit value at the given address.
    #[inline(always)]
    pub fn get_memory_doubleword(&mut self, address: Address) -> Result<DoubleWord> {
        // Address must be aligned to 8 bytes or 4 bytes
        if (address & 0x7 != 0) && (address & 0x3 != 0) {
            anyhow::bail!("Unaligned memory access: {:x}", address);
        }

        match self.page_lookup(address >> page::PAGE_ADDRESS_SIZE as u64) {
            Some(page) => {
                let page_address = address as usize & page::PAGE_ADDRESS_MASK;
                Ok(DoubleWord::from_be_bytes(
                    page.borrow().data[page_address..page_address + 8].try_into()?,
                ))
            }
            None => Ok(0),
        }
    }

    /// Allocate a new page in the [Memory] at a given page index.
    ///
    /// ### Takes
    /// - `page_index`: The page index to allocate the page at.
    ///
    /// ### Returns
    /// - A reference to the allocated [CachedPage].
    pub fn alloc_page(&mut self, page_index: u64) -> Result<SharedCachedPage> {
        let page = SharedCachedPage::default();
        self.pages.insert(page_index, page.clone());

        let mut key = (1 << page::PAGE_KEY_SIZE) | page_index;
        while key > 0 {
            self.nodes.insert(key, None);
            key >>= 1;
        }
        Ok(page)
    }

    /// Set a range of memory in the [Memory] at a given address.
    ///
    /// ### Takes
    /// - `address`: The address to set the memory at.
    /// - `data`: The data to set.
    ///
    /// ### Returns
    /// - A [Result] indicating if the operation was successful.
    pub fn set_memory_range<T: Read>(&mut self, address: Address, data: T) -> Result<()> {
        let mut address = address;
        let mut data = data;
        loop {
            let page_index = address >> page::PAGE_ADDRESS_SIZE as u64;
            let page_address = address as usize & page::PAGE_ADDRESS_MASK;

            let page = self
                .page_lookup(page_index)
                .map(Ok)
                .unwrap_or_else(|| self.alloc_page(page_index))?;
            page.borrow_mut().invalidate_full();

            match data.read(&mut page.borrow_mut().data[page_address..]) {
                Ok(n) => {
                    if n == 0 {
                        return Ok(());
                    }
                    address += n as Address;
                }
                Err(e) => return Err(e.into()),
            };
        }
    }

    /// Returns a human-readable string describing the size of the [Memory].
    ///
    /// ### Returns
    /// - A human-readable string describing the size of the [Memory] in B, KiB, MiB, GiB, TiB, PiB,
    ///   or EiB.
    pub fn usage(&self) -> String {
        let total = (self.pages.len() * page::PAGE_SIZE) as u64;
        const UNIT: u64 = 1024;
        if total < UNIT {
            return format!("{} B", total);
        }
        let mut div = UNIT;
        let mut exp = 0;
        let mut n = total / UNIT;
        while n >= UNIT {
            div *= UNIT;
            exp += 1;
            n /= UNIT;
        }
        format!("{:.1} {}iB", (total as f64) / (div as f64), ['K', 'M', 'G', 'T', 'P', 'E'][exp])
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct PageEntry {
    index: u64,
    #[serde(with = "crate::utils::ser::page_hex")]
    data: Page,
}

impl Default for PageEntry {
    fn default() -> Self {
        Self { index: Default::default(), data: [0u8; page::PAGE_SIZE] }
    }
}

impl Serialize for Memory {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut page_entries: Vec<PageEntry> = self
            .pages
            .iter()
            .map(|(&k, p)| PageEntry { index: k, data: p.borrow().data })
            .collect();

        page_entries.sort_by(|a, b| a.index.cmp(&b.index));
        page_entries.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Memory {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let page_entries: Vec<PageEntry> = Vec::deserialize(deserializer)?;

        let mut memory = Memory::default();

        for (i, p) in page_entries.iter().enumerate() {
            if memory.pages.contains_key(&p.index) {
                return Err(serde::de::Error::custom(format!(
                    "cannot load duplicate page, entry {}, page index {}",
                    i, p.index
                )));
            }
            let page = memory.alloc_page(p.index).map_err(|_| {
                serde::de::Error::custom("Failed to allocate page in deserialization")
            })?;
            let mut page = page.borrow_mut();
            page.data = p.data;
            page.invalidate_full();
        }

        Ok(memory)
    }
}

pub struct MemoryReader<'a> {
    memory: &'a mut Memory,
    address: Address,
    count: u64,
}

impl<'a> MemoryReader<'a> {
    pub fn new(memory: &'a mut Memory, address: Address, count: u64) -> Self {
        Self { memory, address, count }
    }
}

impl<'a> Read for MemoryReader<'a> {
    fn read(&mut self, mut buf: &mut [u8]) -> Result<usize, std::io::Error> {
        if self.count == 0 {
            return Ok(0);
        }

        let end_address = self.address + self.count as Address;

        let page_index = self.address as u64 >> page::PAGE_ADDRESS_SIZE as u64;
        let start = self.address as usize & page::PAGE_ADDRESS_MASK;
        let mut end = page::PAGE_SIZE;

        if page_index == (end_address as u64 >> page::PAGE_ADDRESS_SIZE as u64) {
            end = end_address as usize & page::PAGE_ADDRESS_MASK;
        }
        let n = end - start;
        match self.memory.page_lookup(page_index) {
            Some(page) => {
                std::io::copy(&mut page.borrow().data[start..end].as_ref(), &mut buf)?;
            }
            None => {
                std::io::copy(&mut vec![0; n].as_slice(), &mut buf)?;
            }
        };
        self.address += n as Address;
        self.count -= n as u64;
        Ok(n)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod merkle_proof {
        use super::*;

        #[test]
        fn small_tree() {
            let mut memory = Memory::default();
            memory.set_memory_word(0x10000, 0xaabbccdd).unwrap();
            let proof = memory.merkle_proof(0x10000).unwrap();
            assert_eq!([0xaa, 0xbb, 0xcc, 0xdd], proof[..4]);
            (0..MEMORY_PROOF_SIZE - 1).for_each(|i| {
                let start = 32 + i * 32;
                assert_eq!(page::ZERO_HASHES[i], proof[start..start + 32]);
            });
        }

        #[test]
        fn larger_tree() {
            let mut memory = Memory::default();
            memory.set_memory_word(0x10000, 0xaabbccdd).unwrap();
            memory.set_memory_word(0x80004, 42).unwrap();
            memory.set_memory_word(0x13370000, 123).unwrap();
            let root = memory.merkle_root().unwrap();
            let proof = memory.merkle_proof(0x80004).unwrap();
            assert_eq!([0x00, 0x00, 0x00, 0x2a], proof[4..8]);
            let mut node = proof[..32].try_into().unwrap();
            let mut path = 0x80004 >> 5;
            (32..proof.len()).step_by(32).for_each(|i| {
                let sib: B256 = proof[i..i + 32].try_into().unwrap();
                if path & 1 != 0 {
                    node = keccak_concat_hashes(sib, node);
                } else {
                    node = keccak_concat_hashes(node, sib);
                }
                path >>= 1;
            });
            assert_eq!(root, node, "proof must verify");
        }
    }

    mod merkle_root {
        use super::*;

        #[test]
        fn empty() {
            let mut memory = Memory::default();
            let root = memory.merkle_root().unwrap();
            assert_eq!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                root,
                "Fully zeroed memory should have expected zero hash"
            );
        }

        #[test]
        fn empty_page() {
            let mut memory = Memory::default();
            memory.set_memory_word(0xF000, 0).unwrap();
            let root = memory.merkle_root().unwrap();
            assert_eq!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                root,
                "Fully zeroed memory should have expected zero hash"
            );
        }

        #[test]
        fn single_page() {
            let mut memory = Memory::default();
            memory.set_memory_word(0xF000, 1).unwrap();
            let root = memory.merkle_root().unwrap();
            assert_ne!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                root,
                "Non-zero memory should not have expected zero hash"
            );
        }

        #[test]
        fn repeat_zero() {
            let mut memory = Memory::default();
            memory.set_memory_word(0xF000, 0).unwrap();
            memory.set_memory_word(0xF004, 0).unwrap();
            let root = memory.merkle_root().unwrap();
            assert_eq!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                root,
                "Still should have expected zero hash"
            );
        }

        #[test]
        fn random_few_pages() {
            let mut memory = Memory::default();
            memory.set_memory_word(page::PAGE_SIZE as Address * 3, 1).unwrap();
            memory.set_memory_word(page::PAGE_SIZE as Address * 5, 42).unwrap();
            memory.set_memory_word(page::PAGE_SIZE as Address * 6, 123).unwrap();
            let p3 = memory.merkleize_subtree((1 << page::PAGE_KEY_SIZE) | 3).unwrap();
            let p5 = memory.merkleize_subtree((1 << page::PAGE_KEY_SIZE) | 5).unwrap();
            let p6 = memory.merkleize_subtree((1 << page::PAGE_KEY_SIZE) | 6).unwrap();
            let z = page::ZERO_HASHES[page::PAGE_ADDRESS_SIZE - 5];
            let r1 = keccak_concat_hashes(
                keccak_concat_hashes(
                    keccak_concat_hashes(z, z).into(),
                    keccak_concat_hashes(z, p3).into(),
                )
                .into(),
                keccak_concat_hashes(
                    keccak_concat_hashes(z, p5).into(),
                    keccak_concat_hashes(p6, z).into(),
                )
                .into(),
            );
            let r2 = memory.merkleize_subtree(1 << (page::PAGE_KEY_SIZE - 3)).unwrap();
            assert_eq!(r1, r2, "Expecting manual page combination to match subtree merkle func");
        }

        #[test]
        fn invalidate_page() {
            let mut memory = Memory::default();
            memory.set_memory_word(0xF000, 0).unwrap();
            assert_eq!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                memory.merkle_root().unwrap(),
                "Zero at first"
            );
            memory.set_memory_word(0xF004, 1).unwrap();
            assert_ne!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                memory.merkle_root().unwrap(),
                "Non-zero"
            );
            memory.set_memory_word(0xF004, 0).unwrap();
            assert_eq!(
                page::ZERO_HASHES[MEMORY_PROOF_SIZE - 1],
                memory.merkle_root().unwrap(),
                "Zero again"
            );
        }
    }

    mod read_write {
        use super::*;
        use crate::memory::MemoryReader;
        use rand::RngCore;
        use std::io::Read;

        #[test]
        fn large_random() {
            let mut memory = Memory::default();
            let mut data = [0u8; 20_000];
            rand::thread_rng().fill_bytes(&mut data[..]);
            memory.set_memory_range(0, &data[..]).expect("Should not error");
            for i in [0, 4, 1000, 20_000 - 4] {
                let value = memory.get_memory_word(i).expect("Should not error");
                let expected =
                    Word::from_be_bytes(data[i as usize..i as usize + 4].try_into().unwrap());
                assert_eq!(expected, value, "read at {}", i);
            }
        }

        #[test]
        fn repeat_range() {
            let mut memory = Memory::default();
            let data = b"under the big bright yellow sun".repeat(40);
            memory.set_memory_range(0x1337, &data[..]).expect("Should not error");

            let mut reader = MemoryReader::new(&mut memory, 0x1337 - 10, data.len() as u64 + 20);
            let mut buf = Vec::with_capacity(1260);
            reader.read_to_end(&mut buf).unwrap();

            assert_eq!([0u8; 10], buf[..10], "empty start");
            assert_eq!(data[..], buf[10..buf.len() - 10], "result");
            assert_eq!([0u8; 10], buf[buf.len() - 10..], "empty end");
        }

        #[test]
        fn read_write() {
            let mut memory = Memory::default();
            memory.set_memory_word(12, 0xaabbccdd).unwrap();
            assert_eq!(0xaabbccdd, memory.get_memory_word(12).unwrap());
            memory.set_memory_word(12, 0xaabbc1dd).unwrap();
            assert_eq!(0xaabbc1dd, memory.get_memory_word(12).unwrap());
        }

        #[test]
        fn unaligned_read() {
            let mut memory = Memory::default();
            memory.set_memory_word(12, 0xaabbccdd).unwrap();
            memory.set_memory_word(16, 0x11223344).unwrap();
            assert!(memory.get_memory_word(13).is_err());
            assert!(memory.get_memory_word(14).is_err());
            assert!(memory.get_memory_word(15).is_err());
            assert_eq!(0x11223344, memory.get_memory_word(16).unwrap());
            assert_eq!(0, memory.get_memory_word(20).unwrap());
            assert_eq!(0xaabbccdd, memory.get_memory_word(12).unwrap());
        }

        #[test]
        fn unaligned_write() {
            let mut memory = Memory::default();
            memory.set_memory_word(12, 0xaabbccdd).unwrap();
            assert!(memory.set_memory_word(13, 0x11223344).is_err());
            assert!(memory.set_memory_word(14, 0x11223344).is_err());
            assert!(memory.set_memory_word(15, 0x11223344).is_err());
            assert_eq!(0xaabbccdd, memory.get_memory_word(12).unwrap());
        }
    }

    mod serialize {
        use super::*;
        use crate::types::{Gindex, SharedCachedPage};
        use proptest::{
            prelude::{any, Arbitrary},
            proptest,
            strategy::{BoxedStrategy, Just, Strategy},
        };
        use rustc_hash::FxHashMap;

        impl Arbitrary for Memory {
            type Parameters = ();
            type Strategy = BoxedStrategy<Self>;

            fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
                let dummy_page = SharedCachedPage::default();

                (
                    // Generating random values for nodes
                    proptest::collection::hash_map(
                        any::<Gindex>(),
                        proptest::option::of(any::<[u8; 32]>()),
                        0..10,
                    ),
                    // Generating random values for pages
                    proptest::collection::hash_map(any::<u64>(), Just(dummy_page.clone()), 0..10),
                    // Generating random values for last_page
                    (any::<u64>(), Just(Some(dummy_page.clone()))),
                    (any::<u64>(), Just(Some(dummy_page.clone()))),
                )
                    .prop_map(|(nodes, pages, lp_a, lp_b)| Memory {
                        nodes: nodes
                            .into_iter()
                            .map(|(a, b)| (a, b.map(|x| x.try_into().unwrap())))
                            .collect::<FxHashMap<_, _>>(),
                        pages: pages.into_iter().collect::<FxHashMap<_, _>>(),
                        last_page: [lp_a, lp_b],
                    })
                    .boxed()
            }
        }

        proptest! {
            #[test]
            fn test_serialize_roundtrip(mut memory: Memory) {
                let merkle_root_pre = memory.merkle_root().unwrap();
                let serialized_str = serde_json::to_string(&memory).unwrap();
                let mut deserialized_mem: Memory = serde_json::from_str(&serialized_str).unwrap();
                let merkle_root_post = deserialized_mem.merkle_root().unwrap();
                assert_eq!(merkle_root_pre, merkle_root_post);
                for (i, page) in memory.pages.iter() {
                    let deserialized_page = deserialized_mem.pages.get(i).unwrap();
                    assert_eq!(page.borrow().data, deserialized_page.borrow().data);
                }
            }
        }
    }
}
