//! This module contains the various witness types.

use crate::{
    types::{State, StateWitness},
    utils::keccak256,
};
use alloy_primitives::{Bytes, B256, U256};
use alloy_sol_types::{sol, SolCall};
use kona_preimage::PreimageKeyType;

/// The size of an encoded [StateWitness] in bytes.
pub const STATE_WITNESS_SIZE: usize = 226;

/// Compute the hash of the [StateWitness]
pub fn state_hash(witness: StateWitness) -> [u8; 32] {
    let mut hash = keccak256(witness);
    let offset = 32 * 2 + 4 * 6;
    let exit_code = witness[offset];
    let exited = witness[offset + 1] == 1;
    hash[0] = State::vm_status(exited, exit_code) as u8;
    *hash
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
    pub preimage_key: Option<[u8; 32]>,
    /// The preimage value
    pub preimage_value: Option<Vec<u8>>,
    /// The preimage offset
    pub preimage_offset: Option<u32>,
}

impl Default for StepWitness {
    fn default() -> Self {
        Self {
            state: [0u8; STATE_WITNESS_SIZE],
            mem_proof: Vec::with_capacity(28 * 32 * 2),
            preimage_key: Default::default(),
            preimage_value: Default::default(),
            preimage_offset: Default::default(),
        }
    }
}

sol! {
    /// `PreimageOracle` loadLocalData function.
    function loadLocalData(uint256,bytes32,bytes32,uint256,uint256) external returns (bytes32);

    /// `PreimageOracle` loadKeccak256PreimagePart function.
    function loadKeccak256PreimagePart(uint256,bytes) external;

    /// `MIPS` step function.
    function step(bytes,bytes,bytes32) external returns (bytes32);
}

impl StepWitness {
    /// Returns `true` if the step witness has a preimage.
    pub fn has_preimage(&self) -> bool {
        self.preimage_key.is_some()
    }

    /// ABI encodes the input to the preimage oracle, if the [StepWitness] has a preimage request.
    ///
    /// ### Returns
    /// - `Some(input)` if the [StepWitness] has a preimage request.
    /// - `None` if the [StepWitness] does not have a preimage request.
    pub fn encode_preimage_oracle_input(&self) -> Option<Bytes> {
        let preimage_key = self.preimage_key?;

        match PreimageKeyType::try_from(preimage_key[0]).ok()? {
            PreimageKeyType::Local => {
                let preimage_value = &self.preimage_value.clone()?;

                if preimage_value.len() > 32 + 8 {
                    tracing::error!(
                        target: "fpvm::step_witness",
                        "Local preimage value exceeds maximum size of 32 bytes with key 0x{:x}", B256::from(self.preimage_key?)
                    );
                    return None;
                }

                let preimage_part = &preimage_value[8..];
                let mut tmp = [0u8; 32];
                tmp[0..preimage_part.len()].copy_from_slice(preimage_part);

                let call = loadLocalDataCall {
                    _0: B256::from(preimage_key).into(),
                    _1: B256::ZERO, // constant local context
                    _2: B256::from(tmp),
                    _3: U256::from(preimage_value.len() - 8),
                    _4: U256::from(self.preimage_offset?),
                };

                Some(call.abi_encode().into())
            }
            PreimageKeyType::Keccak256 => {
                let call = loadKeccak256PreimagePartCall {
                    _0: U256::from(self.preimage_offset?),
                    _1: self.preimage_value.clone()?[8..].to_vec().into(),
                };

                Some(call.abi_encode().into())
            }
            _ => todo!(),
        }
    }

    /// ABI encodes the input to the MIPS step function.
    ///
    /// ### Returns
    /// - The ABI encoded input to the MIPS step function.
    pub fn encode_step_input(&self) -> Bytes {
        let call = stepCall {
            _0: self.state.to_vec().into(),
            _1: self.mem_proof.to_vec().into(),
            _2: B256::ZERO, // constant local context
        };

        call.abi_encode().into()
    }
}
