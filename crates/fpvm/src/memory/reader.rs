//! Contains the [MemoryReader] structure.

use super::{
    page::{PAGE_ADDRESS_MASK, PAGE_ADDRESS_SIZE, PAGE_SIZE},
    Address, Memory,
};
use std::io::Read;

/// A reader for a generic [Memory] structure.
///
/// Enables unaligned verbatim reads from the [Memory]'s pages. If the pages for the address
/// space requested are not present, the reader will return zeroed out data for that region, rather
/// than fail.
#[derive(Debug)]
pub struct MemoryReader<'a, M: Memory> {
    memory: &'a mut M,
    address: Address,
    count: u64,
}

impl<'a, M> MemoryReader<'a, M>
where
    M: Memory,
{
    /// Create a new [MemoryReader] for the given [Memory] structure that can read
    /// `count` bytes starting from `address`.
    pub fn new(memory: &'a mut M, address: Address, count: u64) -> Self {
        Self { memory, address, count }
    }
}

impl<'a, M> Read for MemoryReader<'a, M>
where
    M: Memory,
{
    fn read(&mut self, mut buf: &mut [u8]) -> Result<usize, std::io::Error> {
        if self.count == 0 {
            return Ok(0);
        }

        let end_address = self.address + self.count as Address;

        let page_index = self.address >> PAGE_ADDRESS_SIZE as u64;
        let start = self.address as usize & PAGE_ADDRESS_MASK;
        let mut end = PAGE_SIZE;

        if page_index == (end_address >> PAGE_ADDRESS_SIZE as u64) {
            end = end_address as usize & PAGE_ADDRESS_MASK;
        }
        let n = end - start;
        match self.memory.page_lookup(page_index, false) {
            Some(page) => {
                std::io::copy(&mut page[start..end].as_ref(), &mut buf)?;
            }
            None => {
                std::io::copy(&mut vec![0; n].as_slice(), &mut buf)?;
            }
        };
        self.address += n as Address;
        self.count -= n as u64;
        Ok(n)
    }
}
