//! This module contains utilities for loading ELF files into [State] objects.

use crate::{
    memory::{page, Address, Memory},
    state::State,
};
use anyhow::Result;
use elf::{abi::PT_LOAD, endian::AnyEndian, ElfBytes};
use std::io::{self, Cursor, Read};

/// Symbols that indicate there is a patch to be made on an ELF file that was compiled from Go.
pub(crate) const GO_SYMBOLS: [&str; 14] = [
    "runtime.gcenable",
    "runtime.init.5",            // patch out: init() { go forcegchelper() }
    "runtime.main.func1",        // patch out: main.func() { newm(sysmon, ....) }
    "runtime.deductSweepCredit", // uses floating point nums and interacts with gc we disabled
    "runtime.(*gcControllerState).commit",
    "github.com/prometheus/client_golang/prometheus.init",
    "github.com/prometheus/client_golang/prometheus.init.0",
    "github.com/prometheus/procfs.init",
    "github.com/prometheus/common/model.init",
    "github.com/prometheus/client_model/go.init",
    "github.com/prometheus/client_model/go.init.0",
    "github.com/prometheus/client_model/go.init.1",
    "flag.init", // skip flag pkg init, we need to debug arg-processing more to see why this fails
    "runtime.check", /* We need to patch this out, we don't pass float64nan because we don't support
                  * floats */
];

/// Load a raw ELF file into a [State] object.
///
/// ### Takes
/// - `raw`: The raw contents of the ELF file to load.
///
/// ### Returns
/// - `Ok(state)` if the ELF file was loaded successfully
/// - `Err(_)` if the ELF file could not be loaded
pub fn load_elf<M: Memory>(raw: &[u8]) -> Result<State<M>> {
    let elf = ElfBytes::<AnyEndian>::minimal_parse(raw)?;

    let mut state: State<M> = State {
        pc: elf.ehdr.e_entry,
        next_pc: elf.ehdr.e_entry + 4,
        heap: 0x10_00_00_00_00_00_00_00u64,
        ..Default::default()
    };

    let headers = elf.segments().ok_or(anyhow::anyhow!("Failed to load section headers"))?;

    for (i, header) in headers.iter().enumerate() {
        if header.p_type == 0x70000003 {
            continue;
        }

        let section_data = &elf.segment_data(&header)?[..header.p_filesz as usize];
        let mut reader: Box<dyn Read> = Box::new(section_data);

        if header.p_filesz != header.p_memsz {
            if header.p_type == PT_LOAD {
                if header.p_filesz < header.p_memsz {
                    reader = Box::new(MultiReader(
                        reader,
                        Cursor::new(vec![0; (header.p_memsz - header.p_filesz) as usize]),
                    ));
                } else {
                    anyhow::bail!(
                        "Invalid PT_LOAD program segment {}, file size ({}) > mem size ({})",
                        i,
                        header.p_filesz,
                        header.p_memsz
                    );
                }
            } else {
                anyhow::bail!(
                    "Program segment {} has different file size ({}) than mem size ({}): filling for non PT_LOAD segments is not supported",
                    i,
                    header.p_filesz,
                    header.p_memsz
                );
            }
        }

        if header.p_vaddr + header.p_memsz >= 1 << 47 {
            anyhow::bail!(
                "Program segment {} out of 64-bit mem range: {} - {} (size: {})",
                i,
                header.p_vaddr,
                header.p_vaddr + header.p_memsz,
                header.p_memsz
            );
        }

        state.memory.set_memory_range(header.p_vaddr, reader)?;
    }

    Ok(state)
}

/// Patch a Go ELF file to work with mipsevm.
///
/// ### Takes
/// - `elf`: The ELF file to patch
/// - `state`: The state to patch the ELF file into
///
/// ### Returns
/// - `Ok(())` if the patch was successful
/// - `Err(_)` if the patch failed
pub fn patch_go<M: Memory>(raw: &[u8], state: &mut State<M>) -> Result<()> {
    let elf = ElfBytes::<AnyEndian>::minimal_parse(raw)?;
    let (parsing_table, string_table) =
        elf.symbol_table()?.ok_or(anyhow::anyhow!("Failed to load ELF symbol table"))?;

    for symbol in parsing_table {
        let symbol_idx = symbol.st_name;
        let name = string_table.get(symbol_idx as usize)?;

        if GO_SYMBOLS.contains(&name) {
            // MIPS32 patch: ret (pseudo instruction)
            // 03e00008 = jr $ra = ret (pseudo instruction)
            // 00000000 = nop (executes with delay-slot, but does nothing)
            state.memory.set_memory_range(
                symbol.st_value,
                [0x03, 0xe0, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00].as_slice(),
            )?;
        } else if name == "runtime.MemProfileRate" {
            // disable mem profiling, to avoid a lot of unnecessary floating point ops
            state.memory.set_doubleword(symbol.st_value, 0)?;
        }
    }

    Ok(())
}

/// Patches the stack to be in a valid state for the Go MIPS runtime.
///
/// ### Takes
/// - `state`: The state to patch the stack for
///
/// ### Returns
/// - `Ok(())` if the patch was successful
/// - `Err(_)` if the patch failed
pub fn patch_stack<M: Memory>(state: &mut State<M>) -> Result<()> {
    // Setup stack pointer
    let ptr = 0x7F_FF_FF_FF_D0_00_u64;

    // Allocate 1 page for the initial stack data, and 16KB = 4 pages for the stack to grow.
    state.memory.set_memory_range(
        ptr - 8 * page::PAGE_SIZE as u64,
        [0u8; page::PAGE_SIZE * 5].as_slice(),
    )?;
    state.registers[29] = ptr;

    #[inline(always)]
    fn store_mem<M: Memory>(st: &mut State<M>, address: Address, value: u64) -> Result<()> {
        st.memory.set_doubleword(address, value)
    }

    store_mem(state, ptr + 8, 0x42)?; // argc = 0 (argument count)
    store_mem(state, ptr + 8 * 2, 0x35)?; // argv[n] = 0 (terminating argv)
    store_mem(state, ptr + 8 * 3, 0)?; // envp[term] = 0 (no env vars)
    store_mem(state, ptr + 8 * 4, 6)?; // auxv[0] = _AT_PAGESZ = 6 (key)
    store_mem(state, ptr + 8 * 5, 4096)?; // auxv[1] = page size of 4 KiB (value) - (== minPhysPageSize)
    store_mem(state, ptr + 8 * 6, 25)?; // auxv[2] = AT_RANDOM
    store_mem(state, ptr + 8 * 7, ptr + 8 * 9)?; // auxv[3] = address of 16 bytes
    store_mem(state, ptr + 8 * 8, 0)?; // auxv[term] = 0
    store_mem(state, ptr + 8 * 9, 0x6f727020646e6172)?; // randomness 8/16
    store_mem(state, ptr + 8 * 10, 0x6164626d616c6f74)?; // randomness 8/16

    Ok(())
}

/// A multi reader is a reader that reads from the first reader until it returns 0, then reads from
/// the second reader.
#[derive(Debug)]
pub struct MultiReader<R1: Read, R2: Read>(R1, R2);

impl<R1: Read, R2: Read> Read for MultiReader<R1, R2> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let read_first = self.0.read(buf)?;
        if read_first == 0 {
            return self.1.read(buf);
        }
        Ok(read_first)
    }
}
