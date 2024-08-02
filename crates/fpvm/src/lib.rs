#![doc = include_str!("../README.md")]
#![warn(missing_debug_implementations, missing_docs, unreachable_pub, rustdoc::all)]
#![deny(unused_must_use, rust_2018_idioms)]
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]

pub mod memory;
pub mod mips;
pub mod state;
pub mod utils;

#[cfg(feature = "mipsevm")]
pub mod evm;

#[cfg(any(feature = "test-utils", test))]
pub mod test_utils;
