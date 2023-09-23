//! This module contains the various witness types.

use crate::{State, StateWitness, StateWitnessHasher};
use alloy_primitives::{keccak256, Bytes, B256, U256};
use alloy_sol_types::{sol, SolCall};
use preimage_oracle::KeyType;

/// The size of an encoded [StateWitness] in bytes.
pub(crate) const STATE_WITNESS_SIZE: usize = 226;

impl StateWitnessHasher for StateWitness {
    fn state_hash(&self) -> B256 {
        let mut hash = keccak256(self);
        let offset = 32 * 2 + 4 * 6;
        let exit_code = self[offset];
        let exited = self[offset + 1] == 1;
        hash[0] = State::vm_status(exited, exit_code) as u8;
        hash
    }
}

/// A [StepWitness] is produced after each instruction step of the MIPS emulator. It contains
/// the encoded [StateWitness], the proof of memory access, and the preimage key, value, and
/// offset.
pub struct StepWitness {
    /// The encoded state witness
    pub state: StateWitness,
    /// The proof of memory access
    pub mem_proof: Vec<u8>,
    /// The preimage key
    pub preimage_key: B256,
    /// The preimage value
    pub preimage_value: Vec<u8>,
    /// The preimage offset
    pub preimage_offset: u32,
}

impl Default for StepWitness {
    fn default() -> Self {
        Self {
            state: [0u8; crate::witness::STATE_WITNESS_SIZE],
            mem_proof: Default::default(),
            preimage_key: Default::default(),
            preimage_value: Default::default(),
            preimage_offset: Default::default(),
        }
    }
}

sol! {
    // `PreimageOracle` loadLocalData function.
    function loadLocalData(uint256,bytes32,uint256,uint256) external returns (bytes32);

    // `PreimageOracle` loadKeccak256PreimagePart function.
    function loadKeccak256PreimagePart(uint256,bytes) external;

    // `MIPS` step function.
    function step(bytes,bytes) external returns (bytes32);
}

impl StepWitness {
    /// Returns `true` if the step witness has a preimage.
    pub fn has_preimage(&self) -> bool {
        self.preimage_key != B256::ZERO
    }

    /// ABI encodes the input to the preimage oracle, if the [StepWitness] has a preimage request.
    ///
    /// ### Returns
    /// - `Some(input)` if the [StepWitness] has a preimage request.
    /// - `None` if the [StepWitness] does not have a preimage request.
    pub fn encode_preimage_oracle_input(&self) -> Option<Bytes> {
        if self.preimage_key == B256::ZERO {
            crate::error!(target: "mipsevm::step_witness", "Cannot encode preimage oracle input without preimage key");
            return None;
        }

        match KeyType::from(self.preimage_key[0]) {
            KeyType::_Illegal => {
                crate::error!(target: "mipsevm::step_witness", "Illegal key type");
                None
            }
            KeyType::Local => {
                if self.preimage_value.len() > 32 + 8 {
                    crate::error!(target: "mipsevm::step_witness", "Local preimage value exceeds maximum size of 32 bytes with key 0x{:x}", self.preimage_key);
                    return None;
                }

                let preimage_part = &self.preimage_value[8..];
                let mut tmp = [0u8; 32];
                tmp[0..preimage_part.len()].copy_from_slice(preimage_part);

                let call = loadLocalDataCall {
                    _0: self.preimage_key.into(),
                    _1: tmp,
                    _2: U256::from(self.preimage_value.len() - 8),
                    _3: U256::from(self.preimage_offset),
                };

                Some(call.encode().into())
            }
            KeyType::GlobalKeccak => {
                let call = loadKeccak256PreimagePartCall {
                    _0: U256::from(self.preimage_offset),
                    _1: self.preimage_value[8..].into(),
                };

                Some(call.encode().into())
            }
        }
    }

    /// ABI encodes the input to the MIPS step function.
    ///
    /// ### Returns
    /// - The ABI encoded input to the MIPS step function.
    pub fn encode_step_input(&self) -> Bytes {
        let call = stepCall {
            _0: self.state.to_vec(),
            _1: self.mem_proof.clone(),
        };

        call.encode().into()
    }
}
