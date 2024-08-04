//! Contains the [Memory] for the Howitzer emulator.

use super::{
    page::{Page, PageIndex, EMPTY_PAGE},
    Address, Memory,
};
use alloy_primitives::B256;
use anyhow::{anyhow, Result};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

/// Binary tree memory implementation for the MIPS emulator.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct TreeMemory {
    pages: FxHashMap<PageIndex, Page>,
}

impl Memory for TreeMemory {
    type Proof = B256;

    fn page_count(&self) -> usize {
        self.pages.len()
    }

    fn merkleize(&mut self) -> Result<B256> {
        unimplemented!()
    }

    fn proof(&mut self, _: Address) -> Result<Self::Proof> {
        unimplemented!()
    }

    fn alloc_page(&mut self, page_index: PageIndex) -> Result<&mut Page> {
        self.pages.insert(page_index, EMPTY_PAGE);
        self.pages.get_mut(&page_index).ok_or_else(|| anyhow!("Failed to allocate page"))
    }

    fn page_lookup(&mut self, page_index: PageIndex, _: bool) -> Option<&mut Page> {
        self.pages.get_mut(&page_index)
    }
}

#[derive(Serialize, Deserialize)]
struct PageEntry {
    index: PageIndex,
    #[serde(with = "crate::utils::ser::page_hex")]
    page: Page,
}

impl Serialize for TreeMemory {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut page_entries: Vec<PageEntry> =
            self.pages.iter().map(|(&k, p)| PageEntry { index: k, page: *p }).collect();

        page_entries.sort_by(|a, b| a.index.cmp(&b.index));
        page_entries.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for TreeMemory {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let page_entries: Vec<PageEntry> = Vec::deserialize(deserializer)?;

        let mut memory = TreeMemory::default();

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
            *page = p.page;
        }

        Ok(memory)
    }
}

#[cfg(test)]
mod test {
    use super::TreeMemory;
    use crate::{
        memory::{page::PAGE_SIZE, Address, Memory},
        mips::isa::{DoubleWord, Word},
    };
    use alloy_trie::EMPTY_ROOT_HASH;
    use std::io::Cursor;

    #[test]
    fn test_empty_merkle() {
        let mut trie_mem = TreeMemory::default();
        let root = trie_mem.merkleize().unwrap();
        assert_eq!(root, EMPTY_ROOT_HASH);
    }

    #[test]
    fn test_get_after_merkleize() {
        let mut trie_mem = TreeMemory::default();

        let cursor = Cursor::new(vec![0xFF; PAGE_SIZE]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        let _ = trie_mem.merkleize();

        // Ensure that the data within the memory trie may be revealed once again.
        let word = trie_mem.get_word(0).unwrap();
        assert_eq!(word, 0xFF_FF_FF_FF);
    }

    #[test]
    fn test_proof_generation() {
        let mut trie_mem = TreeMemory::default();

        let cursor = Cursor::new(vec![0xFF; PAGE_SIZE * 2]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        trie_mem.proof(0xFF).unwrap();
        trie_mem.merkleize().unwrap();

        // Ensure data may still be retrieved from the page where the proof points to.
        assert_eq!(trie_mem.get_word(0).unwrap(), 0xFF_FF_FF_FF);
    }

    #[test]
    fn test_alloc_page() {
        let mut trie_mem = TreeMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;

        assert_eq!(trie_mem.page_count(), 0);

        trie_mem.alloc_page(mock_address).unwrap();
        assert_eq!(trie_mem.page_count(), 1);
        assert!(trie_mem.page_lookup(mock_address, false).is_some());
    }

    #[test]
    fn test_alloc_multipage() {
        let mut trie_mem = TreeMemory::default();
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
        let mut trie_mem = TreeMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFD as Address;
        assert!(trie_mem.get_word(mock_address).is_err());
    }

    #[test]
    fn test_set_word_unaligned() {
        let mut trie_mem = TreeMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFD as Address;
        assert!(trie_mem.set_word(mock_address, 0xBEEF_BABE).is_err());
    }

    #[test]
    fn test_get_doubleword_unaligned() {
        let mut trie_mem = TreeMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;
        assert!(trie_mem.get_doubleword(mock_address).is_err());
    }

    #[test]
    fn test_set_doubleword_unaligned() {
        let mut trie_mem = TreeMemory::default();
        let mock_address = 0xFFFF_FFFF_FFFF_FFFC as Address;
        assert!(trie_mem.set_doubleword(mock_address, 0xBEEF_BABE).is_err());
    }

    #[test]
    fn test_set_get_word_aligned() {
        let mut trie_mem = TreeMemory::default();
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
        let mut trie_mem = TreeMemory::default();
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
        let mut trie_mem = TreeMemory::default();

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
        let mut trie_mem = TreeMemory::default();

        let cursor = Cursor::new(vec![0xFF; 2]);
        trie_mem.set_memory_range(0, cursor).unwrap();

        // Perform a roudntrip serialization and deserialization of the trie memory.
        let serialized = serde_json::to_string(&trie_mem).unwrap();
        let mut deserialized: TreeMemory = serde_json::from_str(&serialized).unwrap();

        // Ensure that the deserialized trie memory is equivalent to the original, when merkleized.
        assert_eq!(trie_mem, deserialized);

        // Ensure that data may still be retrieved from the deserialized trie memory.
        let word = deserialized.get_word(0).unwrap();
        assert_eq!(word, 0xFF_FF_00_00);

        // Ensure that the deserialized trie memory still has the 1 page.
        assert_eq!(deserialized.page_count(), 1);
    }
}
