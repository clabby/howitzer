//! This module contains all of the type aliases and enums used within this crate.

use crate::CachedPage;
use std::{cell::RefCell, rc::Rc};

mod state;
pub use state::State;

mod witness;
pub use witness::{state_hash, StepWitness, STATE_WITNESS_SIZE};

/// A [Page] is a portion of memory of size `PAGE_SIZE`.
pub type Page = [u8; crate::memory::page::PAGE_SIZE];

/// A [CachedPage] with shared ownership.
pub type SharedCachedPage = Rc<RefCell<CachedPage>>;

/// A [StateWitness] is an encoded commitment to the current [crate::State] of the MIPS emulator.
pub type StateWitness = [u8; STATE_WITNESS_SIZE];

/// A single word within the MIPS64 architecture is 32 bits wide.
pub type Word = u32;

/// A double word within the MIPS64 architecture is 64 bits wide.
pub type DoubleWord = u64;

/// A [Gindex] is a generalized index, defined as $2^{\text{depth}} + \text{index}$.
pub type Gindex = u64;

/// An [Address] is a 64 bit address in the MIPS emulator's memory.
pub type Address = u64;

/// The [VMStatus] is an indicator within the [StateWitness] hash that indicates
/// the current status of the MIPS emulator.
#[repr(u8)]
pub enum VMStatus {
    Valid = 0,
    Invalid = 1,
    Panic = 2,
    Unfinished = 3,
}

/// Identifiers for special file descriptors used by the MIPS emulator.
#[repr(u8)]
pub enum Fd {
    StdIn = 0,
    Stdout = 1,
    StdErr = 2,
    HintRead = 3,
    HintWrite = 4,
    PreimageRead = 5,
    PreimageWrite = 6,
}

impl TryFrom<u8> for Fd {
    type Error = anyhow::Error;

    fn try_from(n: u8) -> Result<Self, Self::Error> {
        match n {
            0 => Ok(Fd::StdIn),
            1 => Ok(Fd::Stdout),
            2 => Ok(Fd::StdErr),
            3 => Ok(Fd::HintRead),
            4 => Ok(Fd::HintWrite),
            5 => Ok(Fd::PreimageRead),
            6 => Ok(Fd::PreimageWrite),
            _ => anyhow::bail!("Failed to convert {} to Fd", n),
        }
    }
}
