//! Contains the [Memory] trait for the Howitzer FPVM.

use super::{
    page::{Page, PageIndex},
    Address,
};
use crate::{
    memory::page::{PAGE_ADDRESS_MASK, PAGE_ADDRESS_SIZE, PAGE_SIZE},
    mips::isa::{DoubleWord, Word},
};
use alloy_primitives::B256;
use anyhow::{ensure, Result};
use std::{fmt::Debug, io::Read};

/// The [Memory] trait defines the interface for the MIPS emulator's memory.
pub trait Memory: Default + Debug {
    /// The proof type for [Page]s in the [Memory].
    type Proof: Default + Debug;

    /// Returns the number of pages allocated within the [Memory].
    fn page_count(&self) -> usize;

    /// Seal the open branches in the memory and compute the merkle root.
    ///
    /// ## Returns
    /// - `Ok(merkle_root)` if the memory was successfully merkleized.
    /// - `Err(_)` if the memory could not be merkleized.
    fn merkleize(&mut self) -> Result<B256>;

    /// Generate a proof for the [Page] containing the [Address].
    ///
    /// ## Takes
    /// - `address`: The address to generate the merkle proof for.
    ///
    /// ## Returns
    /// - A proof for the [Page] containing the [Address].
    fn proof(&mut self, address: Address) -> Result<Self::Proof>;

    /// Allocate a new page within the [Memory].
    ///
    /// ## Takes
    /// - `page_index`: The index of the page to allocate.
    ///
    /// ## Returns
    /// - `Ok(())` if the page was successfully allocated.
    /// - `Err(_)` if the page could not be allocated.
    fn alloc_page(&mut self, page_index: PageIndex) -> Result<&mut Page>;

    /// Looks up a page in the [Memory] by its index.
    ///
    /// ## Takes
    /// - `page_index`: The index of the page to lookup.
    /// - `invalidate`: Whether to invalidate the page cache after looking it up.
    ///
    /// ## Returns
    /// - `Ok(Some(page))` if the page was found.
    /// - `Ok(None)` if the page was not found.
    /// - `Err(_)` if an error occurred during the lookup.
    fn page_lookup(&mut self, page_index: PageIndex, invalidate: bool) -> Option<&mut Page>;

    /// Get a 32-bit [Word] from memory at a given 4-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to read the word from.
    ///
    /// ## Returns
    /// - `Ok(word)` if the read was successful.
    /// - `Err(_)` if the read failed.
    fn get_word(&mut self, address: Address) -> Result<Word> {
        // Check that the address is 4-byte aligned.
        ensure!(address & 0x03 == 0, "Address is not 4-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Attempt to lookup the page in memory.
        match self.page_lookup(page_index, false) {
            Some(page) => {
                let mut word_bytes = [0u8; 4];
                word_bytes.copy_from_slice(&page[page_address..page_address + 4]);
                Ok(Word::from_be_bytes(word_bytes))
            }
            None => Ok(0),
        }
    }

    /// Set a 32-bit [Word] in memory at a given 4-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to write the word to.
    /// - `value`: The value to write to the address.
    ///
    /// ## Returns
    /// - `Ok(())` if the write was successful.
    /// - `Err(_)` if the write failed.
    fn set_word(&mut self, address: Address, value: Word) -> Result<()> {
        // Check that the address is 4-byte aligned.
        ensure!(address & 0x03 == 0, "Address is not 4-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Attempt to lookup the page in memory.
        let page = if let Some(page) = self.page_lookup(page_index, true) {
            page
        } else {
            self.alloc_page(page_index)?
        };

        page[page_address..page_address + 4].copy_from_slice(&value.to_be_bytes());

        Ok(())
    }

    /// Get a 64-bit [DoubleWord] from memory at a given 8-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to read the word from.
    ///
    /// ## Returns
    /// - `Ok(word)` if the read was successful.
    /// - `Err(_)` if the read failed.
    fn get_doubleword(&mut self, address: Address) -> Result<DoubleWord> {
        // Check that the address is 8-byte aligned.
        ensure!(address & 0x07 == 0, "Address is not 8-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Create a temporary buffer to store the doubleword.
        let mut doubleword = [0u8; 8];

        // Attempt to fetch the doubleword from a single page.
        if let Some(page) = self.page_lookup(page_index, false) {
            doubleword.copy_from_slice(&page[page_address..page_address + 8]);
        }

        Ok(DoubleWord::from_be_bytes(doubleword))
    }

    /// Set a 64-bit [DoubleWord] in memory at a given 8-byte aligned address.
    ///
    /// ## Takes
    /// - `address`: The address to read the word from.
    /// - `value`: The value to write to the address.
    ///
    /// ## Returns
    /// - `Ok(())` if the write was successful.
    /// - `Err(_)` if the write failed.
    fn set_doubleword(&mut self, address: Address, value: DoubleWord) -> Result<()> {
        // Check that the address is 8-byte aligned.
        ensure!(address & 0x07 == 0, "Address is not 8-byte aligned");

        // Compute the page index and the memory address within it.
        let page_index = address >> PAGE_ADDRESS_SIZE;
        let page_address = address as usize & PAGE_ADDRESS_MASK;

        // Store a buffer of the doubleword to write to memory.
        let value = value.to_be_bytes();

        // Attempt to fetch the doubleword from a single page.
        let page = if let Some(page) = self.page_lookup(page_index, true) {
            page
        } else {
            self.alloc_page(page_index)?
        };

        // Write the doubleword to the page.
        page[page_address..page_address + 8].copy_from_slice(value.as_ref());

        Ok(())
    }

    /// Set a range of memory at a given [Address].
    ///
    /// ## Takes
    /// - `address`: The address to set the memory at.
    /// - `data`: The data to set.
    ///
    /// ## Returns
    /// - `Ok(())` if the memory was successfully set.
    /// - `Err(_)` if the memory could not be set.
    fn set_memory_range<T: Read>(&mut self, address: Address, data: T) -> Result<()> {
        let mut address = address;
        let mut data = data;
        loop {
            let page_index = address >> PAGE_ADDRESS_SIZE as u64;
            let page_address = address as usize & PAGE_ADDRESS_MASK;

            let page = if let Some(page) = self.page_lookup(page_index, true) {
                page
            } else {
                self.alloc_page(page_index)?
            };

            match data.read(&mut page[page_address..]) {
                Ok(n) => {
                    if n == 0 {
                        return Ok(());
                    }
                    address += n as Address;
                }
                Err(e) => return Err(e.into()),
            };
        }
    }

    /// Returns a human-readable string describing the size of the [Memory].
    ///
    /// ## Returns
    /// - A human-readable string describing the size of the [Memory] in B, KiB, MiB, GiB, TiB, PiB,
    ///   or EiB.
    fn usage(&self) -> String {
        let total = (self.page_count() * PAGE_SIZE) as u64;
        const UNIT: u64 = 1024;
        if total < UNIT {
            return format!("{} B", total);
        }
        let mut div = UNIT;
        let mut exp = 0;
        let mut n = total / UNIT;
        while n >= UNIT {
            div *= UNIT;
            exp += 1;
            n /= UNIT;
        }
        format!("{:.1} {}iB", (total as f64) / (div as f64), ['K', 'M', 'G', 'T', 'P', 'E'][exp])
    }
}
