//! This module contains the data structure for the state of the MIPS emulator.

use crate::{
    types::{StateWitness, VMStatus, STATE_WITNESS_SIZE},
    Memory,
};
use anyhow::Result;
use serde::{Deserialize, Serialize};

/// The [State] struct contains the internal model of the MIPS emulator state.
///
/// The [State] by itself does not contain functionality for performing instruction steps
/// or executing the MIPS emulator. For this, use the [crate::InstrumentedState] struct.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct State {
    /// The [Memory] of the emulated MIPS thread context.
    pub memory: Memory,
    /// The preimage key for the given state.
    #[serde(with = "crate::utils::ser::fixed_32_hex")]
    pub preimage_key: [u8; 32],
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
    pub registers: [u64; 32],
    /// The last hint sent to the host.
    #[serde(with = "crate::utils::ser::vec_u8_hex")]
    pub last_hint: Vec<u8>,
}

impl State {
    /// Encode the current [State] into a [StateWitness].
    ///
    /// ### Returns
    /// - A [Result] containing the encoded [StateWitness] or an error if the encoding failed.
    pub fn encode_witness(&mut self) -> Result<StateWitness> {
        let mut witness: StateWitness = [0u8; STATE_WITNESS_SIZE];
        witness[..32].copy_from_slice(self.memory.merkle_root()?.as_slice());
        witness[32..64].copy_from_slice(self.preimage_key.as_slice());
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

    /// Return the [VMStatus] given `exited` and `exit_code` statuses.
    pub fn vm_status(exited: bool, exit_code: u8) -> VMStatus {
        if !exited {
            return VMStatus::Unfinished;
        }

        match exit_code {
            0 => VMStatus::Valid,
            1 => VMStatus::Invalid,
            _ => VMStatus::Panic,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        types::{state_hash, State, STATE_WITNESS_SIZE},
        utils::keccak256,
    };

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
            let mut state = State { exited, exit_code, ..Default::default() };

            let actual_witness = state.encode_witness().unwrap();
            let actual_state_hash = state_hash(actual_witness);
            assert_eq!(actual_witness.len(), STATE_WITNESS_SIZE);

            let mut expected_witness = [0u8; STATE_WITNESS_SIZE];
            let mem_root = state.memory.merkle_root().unwrap();
            expected_witness[..32].copy_from_slice(mem_root.as_slice());
            expected_witness[32 * 2 + 8 * 6] = exit_code;
            expected_witness[32 * 2 + 8 * 6 + 1] = exited as u8;

            assert_eq!(actual_witness, expected_witness, "Incorrect witness");

            let mut expected_state_hash = keccak256(expected_witness);
            expected_state_hash[0] = State::vm_status(exited, exit_code) as u8;
            assert_eq!(actual_state_hash, expected_state_hash, "Incorrect state hash");
        }
    }
}
