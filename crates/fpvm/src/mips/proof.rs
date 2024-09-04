//! Contains the [ProofMeta] struct as well as some helper functions for the [HowitzerVM].

use super::{isa::DoubleWord, HowitzerVM};
use crate::memory::{Address, Memory};
use anyhow::{ensure, Result};
use kona_preimage::{HintRouter, PreimageFetcher};

/// Metadata for the proof generation processes during VM execution.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct ProofMeta<M>
where
    M: Memory,
{
    /// Whether or not the memory proof generation is enabled.
    pub mem_proof_enabled: bool,
    /// The last address that was accessed in memory.
    pub last_mem_access: Option<Address>,
    /// The memory proof, if it is enabled.
    pub mem_proof: Option<M::Proof>,

    /// Cached pre-image data, including 8 byte length prefix    
    pub last_preimage: Vec<u8>,
    /// Key for the above preimage         
    pub last_preimage_key: [u8; 32],
    /// The offset we last read from, or max u64 if nothing is read at
    /// the current step.
    pub last_preimage_offset: Option<DoubleWord>,
}

impl<M, P> HowitzerVM<M, P>
where
    M: Memory,
    P: HintRouter + PreimageFetcher,
{
    /// Track an access to [Memory] at the given [Address].
    ///
    /// ### Takes
    /// - `address`: The address in [Memory] being accessed.
    ///
    /// ### Returns
    /// - A [Result] indicating if the operation was successful.
    #[inline(always)]
    pub(crate) fn track_mem_access(&mut self, address: Address) -> Result<()> {
        if self.proof_meta.mem_proof_enabled && self.proof_meta.last_mem_access != Some(address) {
            ensure!(
                self.proof_meta.last_mem_access.is_none(),
                "Unexpected last memory access with existing access buffered."
            );
            self.proof_meta.last_mem_access = Some(address);
            self.proof_meta.mem_proof = Some(self.state.memory.proof(address)?);
        }
        Ok(())
    }
}
