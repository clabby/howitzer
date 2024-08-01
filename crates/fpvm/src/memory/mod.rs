//! Contains the memory implementation for the Howitzer FPVM.

use crate::mips::mips_isa::DoubleWord;

pub const MEMORY_PROOF_SIZE: usize = (DoubleWord::BITS - 4) as usize;

/// A [Gindex] is a generalized index, defined as $2^{\text{depth}} + \text{index}$.
pub type Gindex = u64;

/// An [Address] is a 64 bit address in the MIPS emulator's memory.
pub type Address = u64;

pub(crate) mod trie;

pub(crate) mod page;

mod trie_memory;
pub use trie_memory::{TrieMemory, MemoryReader};
