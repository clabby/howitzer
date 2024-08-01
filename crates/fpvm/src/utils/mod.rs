//! This module contains utility and helper functions for this crate.

pub mod meta;
pub mod patch;
pub mod ser;

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
