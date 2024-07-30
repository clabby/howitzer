//! Contains the memory implementation for the Howitzer FPVM.

pub const MEMORY_CELL_SIZE: usize = 64;
pub const MEMORY_PROOF_SIZE: usize = MEMORY_CELL_SIZE - 4;

pub(crate) mod page;
pub use page::CachedPage;

mod map_memory;
pub use map_memory::{Memory, MemoryReader};
