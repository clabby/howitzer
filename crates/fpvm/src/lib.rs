#![doc = include_str!("../README.md")]

mod mips;
pub use mips::InstrumentedState;

mod memory;
pub use memory::{CachedPage, Memory, MemoryReader};

pub mod utils;

pub mod types;

#[cfg(any(feature = "test-utils", test))]
pub mod test_utils;

#[cfg(feature = "mipsevm")]
pub mod evm;
