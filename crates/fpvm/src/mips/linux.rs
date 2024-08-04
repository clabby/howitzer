//! Linux-specific MIPS64 constructs for Howitzer.
//!
//! This module contains the MIPS64-specific [Syscall] definitions and [Syscall] handling logic for
//! the MIPS emulator.

use super::{
    def_enum,
    isa::{DoubleWord, Word},
};
use crate::{
    memory::{page, Address, Memory, MemoryReader},
    mips::InstrumentedState,
};
use anyhow::Result;
use kona_preimage::{HintRouter, PreimageFetcher};
use std::io::{self, BufReader, Read, Write};

/// [MIPS Syscall Definitions](https://www.cs.cmu.edu/afs/club/usr/jhutz/project/Linux/src/include/asm-mips/errno.h)
const MIPS_EBADF: u64 = 0x9;

/// [MIPS Syscall Definitions](https://www.cs.cmu.edu/afs/club/usr/jhutz/project/Linux/src/include/asm-mips/errno.h)
const MIPS_EINVAL: u64 = 0x16;

def_enum!(Fd {
    StdIn = 0,
    Stdout = 1,
    StdErr = 2,
    HintRead = 3,
    HintWrite = 4,
    PreimageRead = 5,
    PreimageWrite = 6,
});

def_enum!(Syscall {
    Mmap = 5009,
    Brk = 5012,
    Clone = 5055,
    ExitGroup = 5205,
    Read = 5000,
    Write = 5001,
    Fcntl = 5070,
});

impl<M, O, E, P> InstrumentedState<M, O, E, P>
where
    M: Memory,
    O: Write,
    E: Write,
    P: HintRouter + PreimageFetcher,
{
    /// Handles a [Syscall] dispatch within the MIPS kernel.
    ///
    /// ### Returns
    /// - `Ok(())` - The syscall was successfully handled.
    /// - `Err(_)` - An error occurred while handling the syscall.
    #[inline(always)]
    pub(crate) async fn handle_syscall(&mut self) -> Result<()> {
        let mut v0 = 0;
        let mut v1 = 0;

        let (a0, a1, mut a2) =
            (self.state.registers[4], self.state.registers[5], self.state.registers[6]);

        if let Ok(syscall) = Syscall::try_from(self.state.registers[2] as Word) {
            match syscall {
                Syscall::Mmap => {
                    let mut sz = a1;

                    // Adjust the size to align with the page size if the size
                    // cannot fit within the page address mask.
                    let masked_size = sz & page::PAGE_ADDRESS_MASK as u64;
                    if masked_size != 0 {
                        sz += page::PAGE_SIZE as u64 - masked_size;
                    }

                    if a0 == 0 {
                        v0 = self.state.heap;
                        self.state.heap += sz;
                    } else {
                        v0 = a0;
                    }
                }
                Syscall::Brk => {
                    // TODO(clabby): Prob wrong for 64-bit?
                    v0 = 0x40000000;
                }
                Syscall::Clone => {
                    // Clone is not supported, set the virtual register to 1.
                    v0 = 1;
                }
                Syscall::ExitGroup => {
                    self.state.exited = true;
                    self.state.exit_code = a0 as u8;
                    return Ok(());
                }
                Syscall::Read => match Fd::try_from(a0 as u32) {
                    Ok(Fd::StdIn) => {
                        // Nothing to do; Leave v0 and v1 zero, read nothing, and give no error.
                    }
                    Ok(Fd::PreimageRead) => {
                        let effective_address = (a1 & 0xFFFFFFFFFFFFFFF8) as Address;

                        self.track_mem_access(effective_address)?;
                        let memory = self.state.memory.get_doubleword(effective_address)?;

                        let (data, mut data_len) = self
                            .read_preimage(self.state.preimage_key, self.state.preimage_offset)
                            .await?;

                        let alignment = (a1 & 0x7) as usize;
                        let space = 8 - alignment;
                        if space < data_len {
                            data_len = space;
                        }
                        if (a2 as usize) < data_len {
                            data_len = a2 as usize;
                        }

                        let mut out_mem = memory.to_be_bytes();
                        out_mem[alignment..alignment + data_len].copy_from_slice(&data[..data_len]);
                        self.state
                            .memory
                            .set_doubleword(effective_address, u64::from_be_bytes(out_mem))?;
                        self.state.preimage_offset += data_len as u64;
                        v0 = data_len as DoubleWord;
                    }
                    Ok(Fd::HintRead) => {
                        // Don't actually read anything into memory, just say we read it. The
                        // result is ignored anyways.
                        v0 = a2;
                    }
                    _ => {
                        v0 = DoubleWord::MAX;
                        v1 = MIPS_EBADF;
                    }
                },
                Syscall::Write => match Fd::try_from(a0 as u32) {
                    Ok(fd @ (Fd::Stdout | Fd::StdErr)) => {
                        let mut reader =
                            MemoryReader::new(&mut self.state.memory, a1 as Address, a2);
                        let writer: &mut dyn Write = if matches!(fd, Fd::Stdout) {
                            &mut self.std_out
                        } else {
                            &mut self.std_err
                        };
                        io::copy(&mut reader, writer)?;
                        v0 = a2;
                    }
                    Ok(Fd::HintWrite) => {
                        let mut reader =
                            MemoryReader::new(&mut self.state.memory, a1 as Address, a2);
                        let mut hint_data = Vec::with_capacity(a2 as usize);
                        reader.read_to_end(&mut hint_data)?;
                        self.state.last_hint.extend(hint_data);

                        // Continue processing while there is enough data to check if there are any
                        // hints.
                        while self.state.last_hint.len() >= 4 {
                            let hint_len =
                                u32::from_be_bytes(self.state.last_hint[..4].try_into()?);
                            if hint_len >= self.state.last_hint.len() as u32 - 4 {
                                let hint = &self.state.last_hint[4..4 + hint_len as usize];

                                // TODO(clabby): Ordering could be an issue here.
                                self.preimage_oracle
                                    .route_hint(
                                        String::from_utf8(hint.to_vec())
                                            .map_err(|e| anyhow::anyhow!(e))?,
                                    )
                                    .await?;
                                self.state.last_hint =
                                    self.state.last_hint[4 + hint_len as usize..].into();
                            } else {
                                break;
                            }
                        }
                        v0 = a2;
                    }
                    Ok(Fd::PreimageWrite) => {
                        let effective_address = a1 & 0xFFFFFFFFFFFFFFF8;
                        self.track_mem_access(effective_address as Address)?;

                        let memory =
                            self.state.memory.get_doubleword(effective_address as Address)?;
                        let mut key = self.state.preimage_key;
                        let alignment = a1 & 0x7;
                        let space = 8 - alignment;

                        if space < a2 {
                            a2 = space;
                        }

                        let key_copy = key;
                        io::copy(&mut key_copy[a2 as usize..].as_ref(), &mut key.as_mut_slice())?;

                        let _ = memory.to_be_bytes()[alignment as usize..]
                            .as_ref()
                            .read(&mut key.as_mut_slice()[32 - a2 as usize..])?;

                        self.state.preimage_key = key;
                        self.state.preimage_offset = 0;
                        v0 = a2;
                    }
                    _ => {
                        v0 = DoubleWord::MAX;
                        v1 = MIPS_EBADF;
                    }
                },
                Syscall::Fcntl => {
                    if a1 == 3 {
                        match Fd::try_from(a0 as u32) {
                            Ok(Fd::StdIn | Fd::PreimageRead | Fd::HintRead) => {
                                v0 = 0; // O_RDONLY
                            }
                            Ok(Fd::Stdout | Fd::StdErr | Fd::PreimageWrite | Fd::HintWrite) => {
                                v0 = 1; // O_WRONLY
                            }
                            _ => {
                                v0 = DoubleWord::MAX;
                                v1 = MIPS_EBADF;
                            }
                        }
                    } else {
                        // The command is not recognized by this kernel.
                        v0 = DoubleWord::MAX;
                        v1 = MIPS_EINVAL;
                    }
                }
            }
        }

        self.state.registers[2] = v0;
        self.state.registers[7] = v1;

        self.state.pc = self.state.next_pc;
        self.state.next_pc += 4;

        Ok(())
    }

    /// Read the preimage for the given key and offset from the preimage server.
    ///
    /// ### Takes
    /// - `key`: The key of the preimage (the preimage's [alloy_primitives::keccak256] digest).
    /// - `offset`: The offset of the preimage to fetch.
    ///
    /// ### Returns
    /// - `Ok((data, data_len))`: The preimage data and length.
    /// - `Err(_)`: An error occurred while fetching the preimage.
    #[inline(always)]
    pub(crate) async fn read_preimage(
        &mut self,
        key: [u8; 32],
        offset: u64,
    ) -> Result<([u8; 32], usize)> {
        if key != self.last_preimage_key {
            let data = self.preimage_oracle.get_preimage(key.try_into()?).await?;
            self.last_preimage_key = key;

            // Add the length prefix to the preimage
            // Resizes the `last_preimage` vec in-place to reduce reallocations.
            self.last_preimage.resize(8 + data.len(), 0);
            self.last_preimage[0..8].copy_from_slice(&data.len().to_be_bytes());
            self.last_preimage[8..].copy_from_slice(&data);
        }

        self.last_preimage_offset = Some(offset);

        let mut data = [0u8; 32];
        let data_len =
            BufReader::new(&self.last_preimage[offset as usize..]).read(data.as_mut_slice())?;
        Ok((data, data_len))
    }
}
