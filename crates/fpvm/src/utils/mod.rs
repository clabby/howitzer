//! This module contains utility and helper functions for this crate.

use alloy_primitives::B256;

pub mod patch;
pub mod ser;

/// Concatenate two fixed sized arrays together into a new array with minimal reallocation.
#[inline(always)]
pub(crate) fn concat_fixed<T>(a: [T; 32], b: [T; 32]) -> [T; 64]
where
    T: Copy + Default,
{
    let mut concatenated: [T; 64] = [T::default(); 64];
    let (left, right) = concatenated.split_at_mut(32);
    left.copy_from_slice(&a);
    right.copy_from_slice(&b);
    concatenated
}

/// Hash the concatenation of two 32 byte digests.
#[inline(always)]
pub(crate) fn keccak_concat_hashes(a: [u8; 32], b: [u8; 32]) -> B256 {
    #[cfg(feature = "simd-keccak")]
    {
        let mut out = B256::ZERO;
        keccak256_aarch64_simd::simd_keccak256_64b_single(&concat_fixed(a, b), out.as_mut());
        out
    }

    #[cfg(not(feature = "simd-keccak"))]
    keccak256(concat_fixed(a, b).as_slice())
}

#[inline(always)]
pub(crate) fn keccak256<T: AsRef<[u8]>>(input: T) -> B256 {
    let mut out = B256::ZERO;
    xkcp_rs::keccak256(input.as_ref(), out.as_mut());
    out
}
