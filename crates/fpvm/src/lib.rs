#![doc = include_str!("../README.md")]

mod mips;
pub use mips::InstrumentedState;

pub mod memory;

pub mod utils;

pub mod state;

#[cfg(feature = "mipsevm")]
pub mod evm;

#[cfg(any(feature = "test-utils", test))]
pub mod test_utils;
