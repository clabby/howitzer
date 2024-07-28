use anyhow::{anyhow, Result};
use elf::{endian::AnyEndian, ElfBytes};
use serde::{Deserialize, Serialize};

use crate::types::Address;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Symbol {
    /// The name of the symbol.
    pub name: String,
    /// The start address of the symbol.
    pub start: u64,
    /// The size of the symbol.
    pub size: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Meta {
    /// The symbols in the binary.
    pub symbols: Vec<Symbol>,
}

impl Meta {
    /// Create [Meta] from an elf file
    pub fn from_elf(elf: ElfBytes<AnyEndian>) -> Result<Self> {
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

    /// Lookup a symbol name by address
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
