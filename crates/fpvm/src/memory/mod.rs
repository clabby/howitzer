//! Contains the memory implementation for the Howitzer FPVM.

/// An [Address] is a 64 bit address in the MIPS emulator's memory.
pub type Address = u64;

mod mem_trait;
pub use mem_trait::Memory;

mod reader;
pub use reader::MemoryReader;

pub mod page;

mod trie_memory;
pub use trie_memory::TrieMemory;

pub(crate) mod trie;
