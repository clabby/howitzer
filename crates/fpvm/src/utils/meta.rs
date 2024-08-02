//! Contains a utility for parsing ELF metadata.

use crate::memory::Address;
use anyhow::{anyhow, Result};
use elf::{endian::AnyEndian, ElfBytes};
use serde::{Deserialize, Serialize};

/// A symbol within an ELF binary.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Symbol {
    /// The name of the symbol.
    pub name: String,
    /// The start address of the symbol.
    pub start: u64,
    /// The size of the symbol.
    pub size: u64,
}

/// The [Meta] struct contains metadata about the symbols in an ELF binary.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Meta {
    /// The symbols in the binary.
    pub symbols: Vec<Symbol>,
}

impl Meta {
    /// Create [Meta] from an elf file.
    ///
    /// ## Takes
    /// - `elf`: The ELF file to parse.
    ///
    /// ## Returns
    /// - `Ok(Meta)` if the parsing was successful.
    /// - `Err(_)` if the parsing failed.
    pub fn from_elf(elf: ElfBytes<'_, AnyEndian>) -> Result<Self> {
        let (parsing_table, string_table) =
            elf.symbol_table()?.ok_or_else(|| anyhow!("No segments found"))?;

        let mut symbols = parsing_table
            .iter()
            .map(|symbol| {
                let symbol_idx = symbol.st_name;
                let name = string_table.get(symbol_idx as usize)?;

                Ok::<_, anyhow::Error>(Symbol {
                    name: name.to_string(),
                    start: symbol.st_value,
                    size: symbol.st_size,
                })
            })
            .collect::<Result<Vec<_>>>()?;

        // Sort by address
        symbols.sort_by_key(|symbol| symbol.start);

        Ok(Self { symbols })
    }

    /// Lookup the symbol at a given address.
    ///
    /// ## Takes
    /// - `address`: The address to lookup.
    ///
    /// ## Returns
    /// - The name of the symbol at the address.
    pub fn lookup(&self, address: Address) -> String {
        if self.symbols.is_empty() {
            return "unknown".to_string();
        }

        let i = self.symbols.iter().position(|symbol| symbol.start > address).unwrap_or(0);

        if i == 0 {
            return "!start".to_string();
        }

        let out = &self.symbols[i - 1];
        if out.start + out.size < address {
            return "!gap".to_string();
        }

        out.name.clone()
    }
}
