//! This module contains utility and helper functions for this crate.

use alloy_primitives::{B256, B512};

pub mod meta;
pub mod patch;
pub mod ser;

/// Concatenate two fixed sized arrays together into a new array with minimal reallocation.
#[inline(always)]
pub(crate) fn concat_fixed(a: B256, b: B256) -> B512 {
    let mut concatenated = B512::ZERO;
    let (left, right) = concatenated.split_at_mut(32);
    left.copy_from_slice(a.as_ref());
    right.copy_from_slice(b.as_ref());
    concatenated
}

/// Hash the concatenation of two 32 byte digests.
#[inline(always)]
pub(crate) fn keccak_concat_hashes(a: B256, b: B256) -> B256 {
    #[cfg(feature = "simd-keccak")]
    {
        let mut out = B256::ZERO;
        keccak256_aarch64_simd::simd_keccak256_64b_single(
            concat_fixed(a, b).as_slice(),
            out.as_mut(),
        );
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

/// Perform a sign extension of a value embedded in the lower bits of `data` up to
/// the `index`th bit.
///
/// ### Takes
/// - `data`: The data to sign extend.
/// - `index`: The index of the bit to sign extend to.
///
/// ### Returns
/// - The sign extended value.
#[inline(always)]
pub(crate) fn sign_extend(data: u64, index: u64) -> u64 {
    let is_signed = (data >> (index - 1)) != 0;
    let signed = ((1 << (64 - index)) - 1) << index;
    let mask = (1 << index) - 1;
    if is_signed {
        (data & mask) | signed
    } else {
        data & mask
    }
}
