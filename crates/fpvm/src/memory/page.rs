//! This module contains the [Page] type as well as associated page parameterization constants.

pub(crate) const PAGE_ADDRESS_SIZE: usize = 12;
pub(crate) const PAGE_SIZE: usize = 1 << PAGE_ADDRESS_SIZE;
pub(crate) const PAGE_ADDRESS_MASK: usize = PAGE_SIZE - 1;
// pub(crate) const MAX_PAGE_COUNT: usize = 1 << PAGE_KEY_SIZE;
// pub(crate) const PAGE_SIZE_WORDS: usize = PAGE_SIZE >> 5;
// pub(crate) const PAGE_KEY_SIZE: usize = 64 - PAGE_ADDRESS_SIZE;
// pub(crate) const PAGE_KEY_MASK: usize = MAX_PAGE_COUNT - 1;

/// An empty page of memory, zeroed out.
pub(crate) const EMPTY_PAGE: Page = [0u8; PAGE_SIZE];

/// An index of a [Page] within a [TrieMemory] structure.
pub(crate) type PageIndex = u64;

/// A page of memory, representing [PAGE_SIZE] bytes of data.
pub(crate) type Page = [u8; PAGE_SIZE];
