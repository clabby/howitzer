//! This module contains all of the type aliases and enums used within this crate.

mod vm_state;
pub use vm_state::{state_hash, State, StateWitness, VMStatus, STATE_WITNESS_SIZE};

mod step_witness;
pub use step_witness::StepWitness;
