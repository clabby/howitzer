//! Radix trie based memory implementation.

use super::{
    page::{Page, PageIndex, EMPTY_PAGE},
    trie::TrieNode,
    Address, Memory,
};
use crate::memory::page::PAGE_ADDRESS_SIZE;
use alloy_primitives::{Bytes, B256};
use alloy_rlp::{Decodable, Encodable};
use anyhow::Result;
use nybbles::Nibbles;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

/// [TrieMemory] is a hexary radix trie based memory implementation.
#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct TrieMemory {
    /// The page trie
    page_trie: TrieNode<Page>,
    /// The active page cache
    page_cache: FxHashMap<PageIndex, Page>,
}

impl Memory for TrieMemory {
    type Proof = Vec<Bytes>;

    fn page_count(&self) -> usize {
        self.page_cache.len()
    }

    fn merkleize(&mut self) -> Result<B256> {
        // Flush all pages in the cache to the trie before generating the proof.
        self.flush_page_cache()?;

        // Compute and return the root hash of the page trie.
        Ok(self.page_trie.root())
    }

    fn proof(&mut self, address: Address) -> Result<Self::Proof> {
        // Flush all pages in the cache to the trie before generating the proof.
        self.flush_page_cache()?;

        let page_index = address >> PAGE_ADDRESS_SIZE;
        self.page_trie.proof(&Nibbles::unpack(page_index.to_be_bytes()))
    }

    fn alloc_page(&mut self, page_index: PageIndex) -> Result<&mut Page> {
        Ok(self.page_cache.entry(page_index).or_insert(EMPTY_PAGE))
    }

    fn page_lookup(&mut self, page_index: PageIndex, invalidate: bool) -> Option<&mut Page> {
        // Consult the cache before fetching from the trie.
        if self.page_cache.get_mut(&page_index).is_some() {
            return self.page_cache.get_mut(&page_index);
        }

        // Fetch the page from the trie.
        let page_index_nibbles = Nibbles::unpack(page_index.to_be_bytes());
        let page = self.page_trie.open(&page_index_nibbles, invalidate).ok().flatten()?;

        // Insert the page into the cache.
        Some(self.page_cache.entry(page_index).or_insert(*page))
    }
}

impl TrieMemory {
    /// Flush the active page cache to the [TrieMemory].
    pub fn flush_page_cache(&mut self) -> Result<()> {
        for (page_index, page) in self.page_cache.iter() {
            let page_index_nibbles = Nibbles::unpack(page_index.to_be_bytes());
            self.page_trie.insert(&page_index_nibbles, *page)?;
        }
        Ok(())
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

        Ok(TrieMemory { page_trie, ..Default::default() })
    }
}

#[cfg(test)]
mod test {
    use super::TrieMemory;
    use crate::{
        memory::{page::PAGE_SIZE, Address, Memory},
        mips::isa::{DoubleWord, Word},
    };
    use alloy_trie::EMPTY_ROOT_HASH;
    use std::io::Cursor;

    #[test]
    fn test_empty_merkle() {
        let mut trie_mem = TrieMemory::default();
        let root = trie_mem.merkleize().unwrap();
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

        trie_mem.proof(0xFF).unwrap();
        trie_mem.merkleize().unwrap();

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
        trie_mem.flush_page_cache().unwrap();

        // Perform a roudntrip serialization and deserialization of the trie memory.
        let serialized = serde_json::to_string(&trie_mem).unwrap();
        let mut deserialized: TrieMemory = serde_json::from_str(&serialized).unwrap();

        // Ensure that the deserialized trie memory is equivalent to the original, when merkleized.
        assert_eq!(trie_mem.page_trie, deserialized.page_trie);

        // Ensure that data may still be retrieved from the deserialized trie memory.
        let word = deserialized.get_word(0).unwrap();
        assert_eq!(word, 0xFF_FF_00_00);

        // Ensure that the deserialized trie memory still has the 1 page.
        assert_eq!(deserialized.page_count(), 1);
    }
}
