//! This module contains the data structure for the state of the MIPS emulator.

use crate::{memory::Memory, mips::isa::DoubleWord};
use alloy_primitives::{keccak256, B256};
use anyhow::Result;
use serde::{Deserialize, Serialize};

/// The size of an encoded [StateWitness] in bytes.
pub const STATE_WITNESS_SIZE: usize = 378;

/// A [StateWitness] is an encoded commitment to the current [State] of the MIPS emulator.
pub type StateWitness = [u8; STATE_WITNESS_SIZE];

/// The [State] struct contains the internal model of the MIPS emulator state.
///
/// The [State] by itself does not contain functionality for performing instruction steps
/// or executing the MIPS emulator. For this, use the [HowitzerVM] struct.
///
/// [HowitzerVM]: crate::mips::HowitzerVM
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct State<M: Memory> {
    /// The memory of the emulated MIPS thread context.
    pub memory: M,
    /// The preimage key for the given state.
    pub preimage_key: B256,
    /// The preimage offset.
    pub preimage_offset: u64,
    /// The current program counter. (Special purpose register $pc)
    pub pc: u64,
    /// The next program counter.
    pub next_pc: u64,
    /// The lo special-purpose register
    pub lo: u64,
    /// The hi special-purpose register
    pub hi: u64,
    /// The heap pointer
    pub heap: u64,
    /// The exit code of the MIPS emulator.
    pub exit_code: u8,
    /// The exited status of the MIPS emulator.
    pub exited: bool,
    /// The current step of the MIPS emulator.
    pub step: u64,
    /// The MIPS emulator's registers.
    pub registers: [DoubleWord; 32],
    /// The last hint sent to the host.
    #[serde(with = "crate::utils::ser::vec_u8_hex")]
    pub last_hint: Vec<u8>,
}

impl<M: Memory> State<M> {
    /// Encode the current [State] into a [StateWitness].
    ///
    /// ### Returns
    /// - A [Result] containing the encoded [StateWitness] or an error if the encoding failed.
    pub fn encode_witness(&mut self) -> Result<StateWitness> {
        let mut witness: StateWitness = [0u8; STATE_WITNESS_SIZE];
        witness[..32].copy_from_slice(self.memory.merkleize()?.as_ref());
        witness[32..64].copy_from_slice(self.preimage_key.as_ref());
        witness[64..72].copy_from_slice(&self.preimage_offset.to_be_bytes());
        witness[72..80].copy_from_slice(&self.pc.to_be_bytes());
        witness[80..88].copy_from_slice(&self.next_pc.to_be_bytes());
        witness[88..96].copy_from_slice(&self.lo.to_be_bytes());
        witness[96..104].copy_from_slice(&self.hi.to_be_bytes());
        witness[104..112].copy_from_slice(&self.heap.to_be_bytes());
        witness[112] = self.exit_code;
        witness[113] = self.exited as u8;
        witness[114..122].copy_from_slice(&self.step.to_be_bytes());
        for (i, r) in self.registers.iter().enumerate() {
            let offset = 122 + i * 8;
            witness[offset..offset + 8].copy_from_slice(&r.to_be_bytes());
        }
        Ok(witness)
    }
}

/// The [VMStatus] is an indicator within the [StateWitness] hash that indicates
/// the current status of the MIPS emulator.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
pub enum VMStatus {
    /// The VM exited successfully, and the computation was valid.
    Valid = 0,
    /// The VM exited successfully, and the computation was invalid.
    Invalid = 1,
    /// The program panicked.
    Panic = 2,
    /// The program is still running.
    Unfinished = 3,
}

/// Compute the hash of the [StateWitness]
pub fn state_hash(witness: StateWitness) -> [u8; 32] {
    let mut hash = keccak256(witness);
    let offset = 32 * 2 + 8 * 6;
    let exit_code = witness[offset];
    let exited = witness[offset + 1] == 1;
    hash[0] = vm_status(exited, exit_code) as u8;
    *hash
}

/// Return the [VMStatus] given `exited` and `exit_code` statuses.
fn vm_status(exited: bool, exit_code: u8) -> VMStatus {
    if !exited {
        return VMStatus::Unfinished;
    }

    match exit_code {
        0 => VMStatus::Valid,
        1 => VMStatus::Invalid,
        _ => VMStatus::Panic,
    }
}

#[cfg(test)]
mod test {
    use crate::{
        memory::{Memory, TrieMemory},
        state::{state_hash, vm_state::vm_status, State, STATE_WITNESS_SIZE},
    };
    use alloy_primitives::keccak256;

    #[test]
    fn test_state_hash() {
        let cases = [
            (false, 0),
            (false, 1),
            (false, 2),
            (false, 3),
            (true, 0),
            (true, 1),
            (true, 2),
            (true, 3),
        ];

        for (exited, exit_code) in cases.into_iter() {
            let memory = TrieMemory::default();
            let mut state = State { exited, exit_code, memory, ..Default::default() };

            let actual_witness = state.encode_witness().unwrap();
            let actual_state_hash = state_hash(actual_witness);
            assert_eq!(actual_witness.len(), STATE_WITNESS_SIZE);

            let mut expected_witness = [0u8; STATE_WITNESS_SIZE];
            let mem_root = state.memory.merkleize().unwrap();
            expected_witness[..32].copy_from_slice(mem_root.as_slice());
            expected_witness[32 * 2 + 8 * 6] = exit_code;
            expected_witness[32 * 2 + 8 * 6 + 1] = exited as u8;

            assert_eq!(actual_witness, expected_witness, "Incorrect witness");

            let mut expected_state_hash = keccak256(expected_witness);
            expected_state_hash[0] = vm_status(exited, exit_code) as u8;
            assert_eq!(actual_state_hash, expected_state_hash, "Incorrect state hash");
        }
    }
}
