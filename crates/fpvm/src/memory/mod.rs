//! Contains the memory implementation for the Howitzer FPVM.

/// An [Address] is a 64 bit address in the MIPS emulator's memory.
pub type Address = u64;

pub mod page;
pub mod trie;

mod trie_memory;
pub use trie_memory::{MemoryReader, TrieMemory};
