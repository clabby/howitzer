//! Radix trie based memory implementation.

use super::{
    page::{Page, PageIndex, EMPTY_PAGE},
    trie::TrieNode,
    Address,
};
use crate::{
    memory::page::{PAGE_ADDRESS_MASK, PAGE_ADDRESS_SIZE, PAGE_SIZE},
    mips::mips_isa::{DoubleWord, Word},
};
use alloy_primitives::{Bytes, B256};
use alloy_rlp::{Decodable, Encodable};
use anyhow::{anyhow, ensure, Result};
use nybbles::Nibbles;
use serde::{Deserialize, Serialize};
use std::io::Read;

/// [TrieMemory] is a hexary radix trie based memory implementation.
#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct TrieMemory {
    /// The page trie
    page_trie: TrieNode<Page>,
}

impl TrieMemory {
    /// Returns the number of pages within the [TrieMemory].
    pub fn page_count(&self) -> usize {
        self.page_trie.leaf_count()
    }

    /// Seal the open branches in the memory trie and flush intermediate node preimages to the
    /// cache.
    ///
    /// ## Returns
    /// - `Ok(merkle_root)` if the memory trie was successfully merkleized.
    /// - `Err(_)` if the memory trie could not be merkleized.
    pub fn merkleize(&mut self) -> B256 {
        self.page_trie.root()
    }

    /// Generate a merkle trie proof for the [TrieNode] at a given [Address].
    ///
    /// ## Takes
    /// - `address`: The address to generate the merkle proof for.
    ///
    /// ## Returns
    /// - A list of merkle proof nodes for the [Page] containing the [Address].
    pub fn merkle_proof(&mut self, address: Address) -> Result<Vec<Bytes>> {
        let page_index = address >> PAGE_ADDRESS_SIZE;
        self.page_trie.proof(&Nibbles::unpack(page_index.to_be_bytes()))
    }

    /// Allocate a new page in thte [TrieMemory] at a given [PageIndex].
    ///
    /// ## Takes
    /// - `page_index`: The index of the page to allocate.
    ///
    /// ## Returns
    /// - `Ok(())` if the page was successfully allocated.
    /// - `Err(_)` if the page could not be allocated.
    pub fn alloc_page(&mut self, page_index: PageIndex) -> Result<&mut Page> {
        let page_index_nibbles = Nibbles::unpack(page_index.to_be_bytes());
        self.page_trie.insert(&page_index_nibbles, EMPTY_PAGE)?;

        self.page_trie
            .open(&page_index_nibbles, true)
            .transpose()
            .ok_or_else(|| anyhow!("Failed to allocate page at index: {}", page_index))?
    }

    /// Looks up a page in the [TrieMemory] by its index. This function will consult the cache
    /// before checking the underlying trie.
    ///
    /// ## Takes
    /// - `page_index`: The index of the page to lookup.
    ///
    /// ## Returns
    /// - `Ok(Some(page))` if the page was found.
    /// - `Ok(None)` if the page was not found.
    /// - `Err(_)` if an error occurred during the lookup.
    pub fn page_lookup(&mut self, page_index: PageIndex, invalidate: bool) -> Option<&mut Page> {
        // TODO(clabby): LRU cache page lookups

        // Fetch the page from the trie.
        let page_index_nibbles = Nibbles::unpack(page_index.to_be_bytes());
        self.page_trie.open(&page_index_nibbles, invalidate).ok().flatten()

        // TODO(clabby): LRU cache page eviction
    }

    /// Get a 32-bit [Word] from memory at a given 4-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to read the word from.
    ///
    /// ## Returns
    /// - `Ok(word)` if the read was successful.
    /// - `Err(_)` if the read failed.
    pub fn get_word(&mut self, address: Address) -> Result<Word> {
        // Check that the address is 4-byte aligned.
        ensure!(address & 0x03 == 0, "Address is not 4-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Attempt to lookup the page in memory.
        match self.page_lookup(page_index, false) {
            Some(page) => {
                let mut word_bytes = [0u8; 4];
                word_bytes.copy_from_slice(&page[page_address..page_address + 4]);
                Ok(Word::from_be_bytes(word_bytes))
            }
            None => Ok(0),
        }
    }

    /// Set a 32-bit [Word] in memory at a given 4-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to write the word to.
    /// - `value`: The value to write to the address.
    ///
    /// ## Returns
    /// - `Ok(())` if the write was successful.
    /// - `Err(_)` if the write failed.
    pub fn set_word(&mut self, address: Address, value: Word) -> Result<()> {
        // Check that the address is 4-byte aligned.
        ensure!(address & 0x03 == 0, "Address is not 4-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Attempt to lookup the page in memory.
        let page = if let Some(page) = self.page_lookup(page_index, true) {
            page
        } else {
            self.alloc_page(page_index)?
        };

        page[page_address..page_address + 4].copy_from_slice(&value.to_be_bytes());

        Ok(())
    }

    /// Get a 64-bit [DoubleWord] from memory at a given 8-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to read the word from.
    ///
    /// ## Returns
    /// - `Ok(word)` if the read was successful.
    /// - `Err(_)` if the read failed.
    pub fn get_doubleword(&mut self, address: Address) -> Result<DoubleWord> {
        // Check that the address is 8-byte aligned.
        ensure!(address & 0x07 == 0, "Address is not 8-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Create a temporary buffer to store the doubleword.
        let mut doubleword = [0u8; 8];

        // Attempt to fetch the doubleword from a single page.
        if let Some(page) = self.page_lookup(page_index, false) {
            doubleword.copy_from_slice(&page[page_address..page_address + 8]);
        }

        Ok(DoubleWord::from_be_bytes(doubleword))
    }

    /// Set a 64-bit [DoubleWord] in memory at a given 8-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to read the word from.
    /// - `value`: The value to write to the address.
    ///
    /// ## Returns
    /// - `Ok(())` if the write was successful.
    /// - `Err(_)` if the write failed.
    pub fn set_doubleword(&mut self, address: Address, value: DoubleWord) -> Result<()> {
        // Check that the address is 8-byte aligned.
        ensure!(address & 0x07 == 0, "Address is not 8-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Store a buffer of the doubleword to write to memory.
        let value = value.to_be_bytes();

        // Attempt to fetch the doubleword from a single page.
        let page = if let Some(page) = self.page_lookup(page_index, true) {
            page
        } else {
            self.alloc_page(page_index)?
        };

        // Write the doubleword to the page.
        page[page_address..page_address + 8].copy_from_slice(value.as_ref());

        Ok(())
    }

    /// Set a range of memory at a given [Address].
    ///
    /// ## Takes
    /// - `address`: The address to set the memory at.
    /// - `data`: The data to set.
    ///
    /// ## Returns
    /// - `Ok(())` if the memory was successfully set.
    /// - `Err(_)` if the memory could not be set.
    pub fn set_memory_range<T: Read>(&mut self, address: Address, data: T) -> Result<()> {
        let mut address = address;
        let mut data = data;
        loop {
            let page_index = address >> PAGE_ADDRESS_SIZE as u64;
            let page_address = address as usize & PAGE_ADDRESS_MASK;

            let page = if let Some(page) = self.page_lookup(page_index, true) {
                page
            } else {
                self.alloc_page(page_index)?
            };

            match data.read(&mut page[page_address..]) {
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
    /// ## Returns
    /// - A human-readable string describing the size of the [Memory] in B, KiB, MiB, GiB, TiB, PiB,
    ///   or EiB.
    pub fn usage(&self) -> String {
        let total = (self.page_count() * PAGE_SIZE) as u64;
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

impl Serialize for TrieMemory {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut rlp_buf = Vec::with_capacity(self.page_trie.length());
        self.page_trie.encode(&mut rlp_buf);

        rlp_buf.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for TrieMemory {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let serialized = Vec::<u8>::deserialize(deserializer)?;
        let page_trie = TrieNode::<Page>::decode(&mut serialized.as_ref())
            .map_err(|e| serde::de::Error::custom(format!("Failed to decode trie node: {}", e)))?;

        Ok(TrieMemory { page_trie })
    }
}

/// A reader for the [TrieMemory] structure.
///
/// Enables unaligned verbatim reads from the [TrieMemory]'s pages. If the pages for the address
/// space requested are not present, the reader will return zeroed out data for that region, rather
/// than fail.
pub struct MemoryReader<'a> {
    memory: &'a mut TrieMemory,
    address: Address,
    count: u64,
}

impl<'a> MemoryReader<'a> {
    pub fn new(memory: &'a mut TrieMemory, address: Address, count: u64) -> Self {
        Self { memory, address, count }
    }
}

impl<'a> Read for MemoryReader<'a> {
    fn read(&mut self, mut buf: &mut [u8]) -> Result<usize, std::io::Error> {
        if self.count == 0 {
            return Ok(0);
        }

        let end_address = self.address + self.count as Address;

        let page_index = self.address >> PAGE_ADDRESS_SIZE as u64;
        let start = self.address as usize & PAGE_ADDRESS_MASK;
        let mut end = PAGE_SIZE;

        if page_index == (end_address >> PAGE_ADDRESS_SIZE as u64) {
            end = end_address as usize & PAGE_ADDRESS_MASK;
        }
        let n = end - start;
        match self.memory.page_lookup(page_index, false) {
            Some(page) => {
                std::io::copy(&mut page[start..end].as_ref(), &mut buf)?;
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
    use super::TrieMemory;
    use crate::{
        memory::{trie_memory::PAGE_SIZE, Address},
        mips::mips_isa::{DoubleWord, Word},
    };
    use alloy_trie::EMPTY_ROOT_HASH;
    use std::io::Cursor;

    #[test]
    fn test_empty_merkle() {
        let mut trie_mem = TrieMemory::default();
        let root = trie_mem.merkleize();
        assert_eq!(root, EMPTY_ROOT_HASH);
    }

    #[test]
    fn test_get_after_merkleize() {
        let mut trie_mem = TrieMemory::default();

        let cursor = Cursor::new(vec![0xFF; PAGE_SIZE]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        let _ = trie_mem.merkleize();

        // Ensure that the data within the memory trie may be revealed once again.
        let word = trie_mem.get_word(0).unwrap();
        assert_eq!(word, 0xFF_FF_FF_FF);
    }

    #[test]
    fn test_proof_generation() {
        let mut trie_mem = TrieMemory::default();

        let cursor = Cursor::new(vec![0xFF; PAGE_SIZE * 2]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        let proof = trie_mem.merkle_proof(0xFF).unwrap();

        dbg!(&proof);
        proof.iter().for_each(|node| {
            dbg!(node.len());
        });

        trie_mem.merkleize();

        // Ensure data may still be retrieved from the page where the proof points to.
        assert_eq!(trie_mem.get_word(0).unwrap(), 0xFF_FF_FF_FF);
    }

    #[test]
    fn test_alloc_page() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;

        assert_eq!(trie_mem.page_count(), 0);

        trie_mem.alloc_page(mock_address).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert!(trie_mem.page_lookup(mock_address, false).is_some());
    }

    #[test]
    fn test_alloc_multipage() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;

        assert_eq!(trie_mem.page_count(), 0);

        trie_mem.alloc_page(mock_address).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert!(trie_mem.page_lookup(mock_address, false).is_some());

        trie_mem.alloc_page(mock_address - PAGE_SIZE as u64).unwrap();
        assert_eq!(trie_mem.page_count(), 2);
        assert!(trie_mem.page_lookup(mock_address, false).is_some());
    }

    #[test]
    fn test_get_word_unaligned() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFD as Address;
        assert!(trie_mem.get_word(mock_address).is_err());
    }

    #[test]
    fn test_set_word_unaligned() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFD as Address;
        assert!(trie_mem.set_word(mock_address, 0xBEEF_BABE).is_err());
    }

    #[test]
    fn test_get_doubleword_unaligned() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;
        assert!(trie_mem.get_doubleword(mock_address).is_err());
    }

    #[test]
    fn test_set_doubleword_unaligned() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;
        assert!(trie_mem.set_doubleword(mock_address, 0xBEEF_BABE).is_err());
    }

    #[test]
    fn test_set_get_word_aligned() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;
        let mock_value = 0xBEEF_BABE as Word;
        let mock_value_b = 0xCAFE_F00D as Word;

        assert_eq!(trie_mem.page_count(), 0);

        trie_mem.set_word(mock_address, mock_value).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert_eq!(trie_mem.get_word(mock_address).unwrap(), mock_value);

        trie_mem.set_word(mock_address - 4, mock_value_b).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert_eq!(trie_mem.get_word(mock_address - 4).unwrap(), mock_value_b);
    }

    #[test]
    fn test_set_get_doubleword_aligned() {
        let mut trie_mem = TrieMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFF8 as Address;
        let mock_value = 0xBEEF_BABE_CAFE_F00D as DoubleWord;
        let mock_value_b = 0xCAFE_F00D_BEEF_BABE as DoubleWord;

        assert_eq!(trie_mem.page_count(), 0);

        trie_mem.set_doubleword(mock_address, mock_value).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert_eq!(trie_mem.get_doubleword(mock_address).unwrap(), mock_value);

        trie_mem.set_doubleword(mock_address - 8, mock_value_b).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert_eq!(trie_mem.get_doubleword(mock_address - 8).unwrap(), mock_value_b);
    }

    #[test]
    fn test_set_memory_range() {
        let mut trie_mem = TrieMemory::default();

        assert_eq!(trie_mem.page_count(), 0);

        let cursor = Cursor::new(vec![0xFF; PAGE_SIZE * 2]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        // A third, empty page is allocated as a result of the `set_memory_range` implementation.
        // The loop will continue after the second page is allocated, allocating a third page before
        // determining that the read is complete.
        assert_eq!(trie_mem.page_count(), 3);

        let left_page = trie_mem.page_lookup(0, false).unwrap();
        assert_eq!(left_page, &[0xFF; PAGE_SIZE]);

        let right_page = trie_mem.page_lookup(1, false).unwrap();
        assert_eq!(right_page, &[0xFF; PAGE_SIZE]);
    }

    #[test]
    fn test_serialize_deserialize_roundtrip() {
        let mut trie_mem = TrieMemory::default();

        let cursor = Cursor::new(vec![0xFF; 2]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        // Perform a roudntrip serialization and deserialization of the trie memory.
        let serialized = serde_json::to_string(&trie_mem).unwrap();
        let mut deserialized: TrieMemory = serde_json::from_str(&serialized).unwrap();

        // Ensure that the deserialized trie memory is equivalent to the original, when merkleized.
        assert_eq!(trie_mem, deserialized);

        // Ensure that data may still be retrieved from the deserialized trie memory.
        let word = deserialized.get_word(0).unwrap();
        assert_eq!(word, 0xFF_FF_00_00);

        // Ensure that the deserialized trie memory still has the 1 page.
        assert_eq!(deserialized.page_count(), 1);
    }
}
