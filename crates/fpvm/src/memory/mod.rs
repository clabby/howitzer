//! Contains the memory implementation for the Howitzer FPVM.

use crate::mips::mips_isa::DoubleWord;

// TODO: Remove, dead
pub const MEMORY_PROOF_SIZE: usize = (DoubleWord::BITS - 4) as usize;

/// An [Address] is a 64 bit address in the MIPS emulator's memory.
pub type Address = u64;

pub(crate) mod trie;

pub(crate) mod page;

mod trie_memory;
pub use trie_memory::{MemoryReader, TrieMemory};
