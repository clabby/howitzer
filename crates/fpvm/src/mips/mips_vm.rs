//! This module contains the MIPS VM implementation for the [InstrumentedState].

use super::mips_instruction::{IType, JType, Opcode, RType, Special2Function, SpecialFunction};
use crate::{
    memory::{page, MemoryReader},
    types::{Address, DoubleWord, Fd, Syscall},
    utils::sign_extend,
    InstrumentedState,
};
use anyhow::Result;
use kona_preimage::{HintRouter, PreimageFetcher};
use std::io::{self, BufReader, Read, Write};

pub(crate) const MIPS_EBADF: u64 = 0x9;
pub(crate) const MIPS_EINVAL: u64 = 0x16;

impl<O, E, P> InstrumentedState<O, E, P>
where
    O: Write,
    E: Write,
    P: HintRouter + PreimageFetcher,
{
    /// Performs a single step of the MIPS thread context emulation.
    ///
    /// ### Returns
    /// - A [Result] indicating if the step was successful.
    #[inline]
    pub(crate) async fn inner_step(&mut self) -> Result<()> {
        // Return early if the program is already exited; There is no more work to do.
        if self.state.exited {
            return Ok(());
        }

        // Increment the instruction counter.
        self.state.step += 1;

        // Fetch the instruction from memory and extract the opcode from the high-order 6 bits.
        let instruction = self.state.memory.get_memory_word(self.state.pc as Address)?;
        let opcode = Opcode::try_from(instruction >> 26)?;

        // Handle J-type - J/JAL
        if matches!(opcode, Opcode::J | Opcode::JAL) {
            // J has no link register, only JAL.
            let link_reg = if matches!(opcode, Opcode::JAL) { 31 } else { 0 };
            let j_type = JType::decode(instruction)?;

            // Take the top 4 bits of the next PC (its 256MB region), and concatenate with the
            // 26-bit `instr_index` within the instruction, left shifted 2 bits.
            // target format (bits): `next_pc[0..36] | instr_index | 00`
            let target =
                self.state.next_pc & 0xFF_FF_FF_FF_F0_00_00_00 | ((j_type.address as u64) << 2);
            return self.handle_jump(link_reg, target);
        }

        // Handle branch instructions
        if matches!(
            opcode,
            Opcode::BEQ | Opcode::BNE | Opcode::BLEZ | Opcode::BGTZ | Opcode::REGIMM
        ) {
            let i_type = IType::decode(instruction)?;
            return self.handle_branch(opcode, i_type);
        }

        // Handle SPECIAL and SPECIAL2 R-Type instructions
        if matches!(opcode, Opcode::SPECIAL | Opcode::SPECIAL2) {
            let r_type = RType::decode(instruction)?;
            match self.execute_special(opcode, r_type).await? {
                Some(val) => return self.handle_rd(r_type.rd as usize, val, true),
                None => return Ok(()),
            }
        }

        // Handle ALU immediate instructions
        if matches!(
            opcode,
            Opcode::ADDI
                | Opcode::ADDIU
                | Opcode::SLTI
                | Opcode::SLTIU
                | Opcode::ANDI
                | Opcode::ORI
                | Opcode::XORI
                | Opcode::DADDI
                | Opcode::DADDIU
        ) {
            let i_type = IType::decode(instruction)?;

            // Zero extend for ANDI, ORI, XORI. Otherwise, sign extend.
            let rt_val = if matches!(opcode, Opcode::ANDI | Opcode::ORI | Opcode::XORI) {
                i_type.imm as DoubleWord
            } else {
                sign_extend(i_type.imm as DoubleWord, 16)
            };
            let rs_val = self.state.registers[i_type.rs as usize];

            let val = self.execute_immediate_alu(opcode, rs_val, rt_val)?;
            return self.handle_rd(i_type.rt as usize, val, true);
        }

        // Handle remaining I-type instructions
        let i_type = IType::decode(instruction)?;
        let (rd_reg_index, store_address, val) = self.execute_i_type(opcode, i_type)?;

        if let Some(address) = store_address {
            self.track_mem_access(address)?;
            self.state.memory.set_memory_doubleword(address, val)?;
        }

        return self.handle_rd(rd_reg_index, val, true);
    }

    /// Executes a [Opcode::SPECIAL] or [Opcode::SPECIAL2] instruction.
    ///
    /// ### Takes
    /// - `opcode`: The opcode of the special instruction.
    /// - `instruction`: The [RType] instruction being executed.
    ///
    /// ### Returns
    /// - A [Result] indicating if the special dispatch was successful.
    pub(crate) async fn execute_special(
        &mut self,
        opcode: Opcode,
        instruction: RType,
    ) -> Result<Option<DoubleWord>> {
        let rs_val = self.state.registers[instruction.rs as usize];
        let rt_val = self.state.registers[instruction.rt as usize];
        let res = match opcode {
            Opcode::SPECIAL => {
                let funct = SpecialFunction::try_from(instruction.funct)?;

                match funct {
                    // MIPS32
                    SpecialFunction::SLL => {
                        Some(sign_extend((rt_val & 0xFFFFFFFF) << instruction.shamt, 32))
                    }
                    SpecialFunction::SRL => {
                        Some(sign_extend((rt_val & 0xFFFFFFFF) >> instruction.shamt, 32))
                    }
                    SpecialFunction::SRA => Some(sign_extend(
                        (rt_val & 0xFFFFFFFF) >> instruction.shamt,
                        32 - instruction.shamt as u64,
                    )),
                    SpecialFunction::SLLV => Some(sign_extend((rt_val & 0xFFFFFFFF) << rs_val, 32)),
                    SpecialFunction::SRLV => Some(sign_extend((rt_val & 0xFFFFFFFF) >> rs_val, 32)),
                    SpecialFunction::SRAV => {
                        Some(sign_extend((rt_val & 0xFFFFFFFF) >> rs_val, 32 - rs_val as u64))
                    }
                    SpecialFunction::JR | SpecialFunction::JALR => {
                        let link_reg = if matches!(funct, SpecialFunction::JALR) {
                            instruction.rd as usize
                        } else {
                            0
                        };
                        self.handle_jump(link_reg, rs_val)?;
                        None
                    }
                    SpecialFunction::MOVZ => {
                        self.handle_rd(instruction.rd as usize, rs_val, rt_val == 0)?;
                        None
                    }
                    SpecialFunction::MOVN => {
                        self.handle_rd(instruction.rd as usize, rs_val, rt_val != 0)?;
                        None
                    }
                    SpecialFunction::SYSCALL => {
                        self.handle_syscall().await?;
                        None
                    }
                    SpecialFunction::SYNC => {
                        // no-op
                        Some(rs_val)
                    }
                    SpecialFunction::MFHI
                    | SpecialFunction::MTHI
                    | SpecialFunction::MFLO
                    | SpecialFunction::MTLO
                    | SpecialFunction::MULT
                    | SpecialFunction::MULTU
                    | SpecialFunction::DIV
                    | SpecialFunction::DIVU => {
                        self.handle_hi_lo(funct, rs_val, rt_val, instruction.rd as usize)?;
                        None
                    }
                    SpecialFunction::ADD => {
                        Some(self.execute_immediate_alu(Opcode::ADDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::ADDU => {
                        Some(self.execute_immediate_alu(Opcode::ADDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::SUB => Some(sign_extend(rs_val - rt_val, 32)),
                    SpecialFunction::SUBU => Some(sign_extend(rs_val - rt_val, 32)),
                    SpecialFunction::AND => {
                        Some(self.execute_immediate_alu(Opcode::ANDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::OR => {
                        Some(self.execute_immediate_alu(Opcode::ORI, rs_val, rt_val)?)
                    }
                    SpecialFunction::XOR => {
                        Some(self.execute_immediate_alu(Opcode::XORI, rs_val, rt_val)?)
                    }
                    SpecialFunction::NOR => Some(!(rs_val | rt_val)),
                    SpecialFunction::SLTI => {
                        Some(((rs_val as i32) < (rt_val as i32)) as DoubleWord)
                    }
                    SpecialFunction::SLTIU => {
                        Some(((rs_val as u32) < (rt_val as u32)) as DoubleWord)
                    }
                    SpecialFunction::TEQ => {
                        if (rs_val as u32) == (rt_val as u32) {
                            anyhow::bail!("TEQ: rs [{rs_val}] == rt [{rt_val}]");
                        }
                        Some(rs_val)
                    }

                    // MIPS64
                    SpecialFunction::DSLLV => Some(rt_val << rs_val),
                    SpecialFunction::DSRLV => Some(rt_val >> rs_val),
                    SpecialFunction::DMULTU | SpecialFunction::DDIVU => {
                        println!("rs: {:05b} | rd {} | shamt: {}", instruction.rs, instruction.rt, instruction.shamt);
                        self.handle_hi_lo(funct, rs_val, rt_val, instruction.rd as usize)?;
                        None
                    }
                    SpecialFunction::DADD => {
                        Some(self.execute_immediate_alu(Opcode::DADDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::DADDU => {
                        Some(self.execute_immediate_alu(Opcode::DADDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::DSUB => Some(rs_val.wrapping_sub(rt_val)),
                    SpecialFunction::DSUBU => Some(rs_val.wrapping_sub(rt_val)),
                    SpecialFunction::DSRL => Some(rt_val >> instruction.shamt),
                    SpecialFunction::DSRA => Some(((rt_val as i64) >> instruction.shamt) as u64),
                    SpecialFunction::DSLL => Some(rt_val << instruction.shamt),
                    SpecialFunction::DSLL32 => Some(rt_val << (instruction.shamt + 32)),
                    SpecialFunction::DSRL32 => Some(rt_val >> (instruction.shamt + 32)),
                    SpecialFunction::DSRA32 => Some(((rt_val as i64) >> (instruction.shamt + 32)) as u64),
                }
            }
            Opcode::SPECIAL2 => {
                let funct = Special2Function::try_from(instruction.funct)?;
                match funct {
                    Special2Function::MUL => {
                        Some(sign_extend(((rs_val as i32) * (rt_val as i32)) as u64, 32))
                    }
                    Special2Function::CLO | Special2Function::CLZ => {
                        let mut rs = rs_val;
                        if matches!(funct, Special2Function::CLO) {
                            rs = !rs;
                        }
                        let mut i = 0u64;

                        while rs & 0x80000000 != 0 {
                            rs <<= 1;
                            i += 1;
                        }
                        Some(i)
                    }
                }
            }
            _ => anyhow::bail!("Passed non-special opcode to execute_special: {opcode:?}"),
        };

        Ok(res)
    }

    /// Executes an immediate ALU operation within the MIPS thread context emulation.
    ///
    /// ### Takes
    /// - `opcode`: The opcode of the immediate ALU instruction.
    /// - `rs_val`: The value of the source register.
    /// - `rt_val`: The value of the target register.
    ///
    /// ### Returns
    /// - `Ok(n)` - The result of the immediate ALU operation.
    /// - `Err(_)`: An error occurred while executing the immediate ALU operation.
    pub(crate) fn execute_immediate_alu(
        &mut self,
        opcode: Opcode,
        rs_val: DoubleWord,
        rt_val: DoubleWord,
    ) -> Result<DoubleWord> {
        match opcode {
            // MIPS32
            Opcode::ADDI | Opcode::ADDIU => Ok(sign_extend(rs_val + rt_val, 32)),
            Opcode::SLTI => Ok(((rs_val as i32) < (rt_val as i32)) as u64),
            Opcode::SLTIU => Ok(((rs_val as u32) < (rt_val as u32)) as u64),
            Opcode::ANDI => Ok(rs_val & rt_val),
            Opcode::ORI => Ok(rs_val | rt_val),
            Opcode::XORI => Ok(rs_val ^ rt_val),
            // MIPS64
            Opcode::DADDI | Opcode::DADDIU => Ok(rs_val + rt_val),
            _ => anyhow::bail!(
                "Passed non-immediate ALU instruction to execute_immediate_alu {:?}",
                opcode
            ),
        }
    }

    /// Handles the execution of a MIPS instruction in the MIPS thread context emulation.
    ///
    /// ### Takes
    /// - `instruction`: The instruction to execute.
    /// - `rs`: The register index of the source register.
    /// - `rt`: The register index of the target register.
    /// - `mem`: The memory that the instruction is operating on.
    ///
    /// ### Returns
    /// - `Ok(n)` - The result of the instruction execution.
    /// - `Err(_)`: An error occurred while executing the instruction.
    #[inline(always)]
    pub(crate) fn execute_i_type(
        &mut self,
        opcode: Opcode,
        instruction: IType,
    ) -> Result<(usize, Option<Address>, DoubleWord)> {
        let rs_val =
            self.state.registers[instruction.rs as usize] + sign_extend(instruction.imm as u64, 16);
        let rt_val = self.state.registers[instruction.rt as usize];

        let address = rs_val & 0xFFFFFFFFFFFFFFF8;
        self.track_mem_access(address as Address)?;
        let mem = self.state.memory.get_memory_doubleword(address as Address)?;

        match opcode {
            // MIPS32
            Opcode::LUI => Ok((
                instruction.rt as usize,
                None,
                sign_extend((instruction.imm as DoubleWord) << 16, 32),
            )),
            Opcode::LB => Ok((
                instruction.rt as usize,
                None,
                sign_extend((mem >> (56 - ((rs_val & 0x7) << 3))) & 0xFF, 8),
            )),
            Opcode::LH => Ok((
                instruction.rt as usize,
                None,
                sign_extend((mem >> (48 - ((rs_val & 0x6) << 3))) & 0xFFFF, 16),
            )),
            Opcode::LWL => {
                let sl = (rs_val & 0x3) << 3;
                let val = ((mem >> (32 - ((rs_val & 0x4) << 3))) << sl) & 0xFFFFFFFF;
                let mask = (0xFFFFFFFFu32 << sl) as DoubleWord;
                Ok((instruction.rt as usize, None, sign_extend((rt_val & !mask) | val, 32)))
            }
            Opcode::LW | Opcode::LL => Ok((
                instruction.rt as usize,
                None,
                sign_extend((mem >> (32 - ((rs_val & 0x4) << 3))) & 0xFFFFFFFF, 32),
            )),
            Opcode::LBU => {
                Ok((instruction.rt as usize, None, (mem >> (56 - ((rs_val & 0x7) << 3))) & 0xFF))
            }
            Opcode::LHU => {
                Ok((instruction.rt as usize, None, (mem >> (48 - ((rs_val & 0x6) << 3))) & 0xFFFF))
            }
            Opcode::LWR => {
                let sr = 24 - ((rs_val & 0x3) << 3);
                let val = ((mem >> (32 - ((rs_val & 0x4) << 3))) >> sr) & 0xFFFFFFFF;
                let mask = (0xFFFFFFFFu32 >> sr) as DoubleWord;
                Ok((instruction.rt as usize, None, sign_extend((rt_val & !mask) | val, 32)))
            }
            Opcode::SB => {
                let sl = 56 - ((rs_val & 0x7) << 3);
                let val = (rt_val & 0xFF) << sl;
                let mask = DoubleWord::MAX ^ (0xFF << sl);
                Ok((0, Some(address), (mem & mask) | val))
            }
            Opcode::SH => {
                let sl = 48 - ((rs_val & 0x6) << 3);
                let val = (rt_val & 0xFFFF) << sl;
                let mask = DoubleWord::MAX ^ (0xFFFF << sl);
                Ok((0, Some(address), (mem & mask) | val))
            }
            Opcode::SWL => {
                let sr = (rs_val & 0x3) << 3;
                let val = ((rt_val & 0xFFFFFFFF) >> sr) << (32 - ((rs_val & 0x4) << 3));
                let mask = ((0xFFFFFFFFu32 >> sr) as u64) << (32 - ((rs_val & 0x4) << 3));
                Ok((0, Some(address), (mem & !mask) | val))
            }
            Opcode::SW | Opcode::SC => {
                let sl = 32 - ((rs_val & 0x4) << 3);
                let val = (rt_val & 0xFFFFFFFF) << sl;
                let mask = 0xFFFFFFFFFFFFFFFF ^ (0xFFFFFFFF << sl);

                if matches!(opcode, Opcode::SC) && instruction.rt != 0 {
                    self.state.registers[instruction.rt as usize] = 1;
                }

                Ok((0, Some(address), (mem & mask) | val))
            }
            Opcode::SWR => {
                let sl = 24 - ((rs_val & 0x3) << 3);
                let val = ((rt_val & 0xFFFFFFFF) << sl) << (32 - ((rs_val & 0x4) << 3));
                let mask = ((0xFFFFFFFFu32 << sl) as u64) << (32 - ((rs_val & 0x4) << 3));
                Ok((0, Some(address), (mem & !mask) | val))
            }
            // MIPS64
            Opcode::LWU => Ok((
                instruction.rt as usize,
                None,
                (mem >> (32 - ((rs_val & 0x4) << 3))) & 0xFFFFFFFF,
            )),
            Opcode::LD => Ok((instruction.rt as usize, None, mem)),
            Opcode::SD => {
                Ok((0, Some(address), rt_val))
            }
            _ => anyhow::bail!("Invalid opcode {:?}", opcode),
        }
    }

    /// Handles a syscall within the MIPS thread context emulation.
    ///
    /// ### Returns
    /// - A [Result] indicating if the syscall dispatch was successful.
    #[inline]
    pub(crate) async fn handle_syscall(&mut self) -> Result<()> {
        let mut v0 = 0;
        let mut v1 = 0;

        let (a0, a1, mut a2) =
            (self.state.registers[4], self.state.registers[5], self.state.registers[6]);

        if let Ok(syscall) = Syscall::try_from(self.state.registers[2]) {
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
                    v0 = 0x40000000;
                }
                Syscall::Clone => {
                    // Clone is not supported, set the virtual register to 1.
                    v0 = 1;
                }
                Syscall::ExitGroup => {
                    dbg!("Syscall: {syscall}");
                    self.state.exited = true;
                    self.state.exit_code = a0 as u8;
                    return Ok(());
                }
                Syscall::Read => match (a0 as u8).try_into() {
                    Ok(Fd::StdIn) => {
                        // Nothing to do; Leave v0 and v1 zero, read nothing, and give no error.
                    }
                    Ok(Fd::PreimageRead) => {
                        let effective_address = (a1 & 0xFFFFFFFFFFFFFFFC) as Address;

                        self.track_mem_access(effective_address)?;
                        let memory = self.state.memory.get_memory_word(effective_address)?;

                        let (data, mut data_len) = self
                            .read_preimage(self.state.preimage_key, self.state.preimage_offset)
                            .await?;

                        let alignment = (a1 & 0x3) as usize;
                        let space = 4 - alignment;
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
                            .set_memory_word(effective_address, u32::from_be_bytes(out_mem))?;
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
                Syscall::Write => match (a0 as u8).try_into() {
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
                        let effective_address = a1 & 0xFFFFFFFFFFFFFFFC;
                        self.track_mem_access(effective_address as Address)?;

                        let memory =
                            self.state.memory.get_memory_word(effective_address as Address)?;
                        let mut key = self.state.preimage_key;
                        let alignment = a1 & 0x3;
                        let space = 4 - alignment;

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
                        match (a0 as u8).try_into() {
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

    /// Handles a branch within the MIPS thread context emulation.
    ///
    /// ### Takes
    /// - `opcode`: The opcode of the branch instruction.
    /// - `instruction`: The instruction being executed.
    /// - `rt_reg`: The register index of the target register.
    /// - `rs`: The register index of the source register.
    ///
    /// ### Returns
    /// - A [Result] indicating if the branch dispatch was successful.
    #[inline]
    pub(crate) fn handle_branch(&mut self, opcode: Opcode, instruction: IType) -> Result<()> {
        if self.state.next_pc != self.state.pc + 4 {
            anyhow::bail!("Unexpected branch in delay slot at {:x}", self.state.pc,);
        }

        let rs = self.state.registers[instruction.rs as usize];

        let should_branch = match opcode {
            Opcode::BEQ | Opcode::BNE => {
                let rt = self.state.registers[instruction.rt as usize];
                (rs == rt && matches!(opcode, Opcode::BEQ))
                    || (rs != rt && matches!(opcode, Opcode::BNE))
            }
            // blez
            Opcode::BLEZ => (rs as i32) <= 0,
            // bgtz
            Opcode::BGTZ => (rs as i32) > 0,
            Opcode::REGIMM => {
                // regimm
                if instruction.rt == 0 {
                    // bltz
                    (rs as i32) < 0
                } else if instruction.rt == 1 {
                    // bgez
                    (rs as i32) >= 0
                } else {
                    false
                }
            }
            _ => false,
        };

        let prev_pc = self.state.pc;
        self.state.pc = self.state.next_pc;

        if should_branch {
            self.state.next_pc =
                prev_pc + 4 + (sign_extend((instruction.imm << 2) as DoubleWord, 16));
        } else {
            // Branch not taken; proceed as normal.
            self.state.next_pc += 4;
        }

        Ok(())
    }

    /// Handles a hi/lo instruction within the MIPS thread context emulation.
    ///
    /// ### Takes
    /// - `fun`: The function code of the instruction.
    /// - `rs`: The register index of the source register.
    /// - `rt`: The register index of the target register.
    /// - `store_reg`: The register index of the register to store the result in.
    ///
    /// ### Returns
    /// - A [Result] indicating if the branch dispatch was successful.
    #[inline]
    pub(crate) fn handle_hi_lo(
        &mut self,
        fun: SpecialFunction,
        rs: DoubleWord,
        rt: DoubleWord,
        store_reg: usize,
    ) -> Result<()> {
        let val = match fun {
            // MIPS32
            SpecialFunction::MFHI => {
                // mfhi
                self.state.hi
            }
            SpecialFunction::MTHI => {
                // mthi
                self.state.hi = rs;
                0
            }
            SpecialFunction::MFLO => {
                // mflo
                self.state.lo
            }
            SpecialFunction::MTLO => {
                // mtlo
                self.state.lo = rs;
                0
            }
            SpecialFunction::MULT => {
                // mult
                let acc = ((rs as i32) as i64) as u64 * ((rt as i32) as i64) as u64;
                self.state.hi = sign_extend(acc >> 32, 32);
                self.state.lo = sign_extend((acc as u32) as u64, 32);
                0
            }
            SpecialFunction::MULTU => {
                // multu
                let acc = (rs as u32) as u64 * (rt as u32) as u64;
                self.state.hi = sign_extend(acc >> 32, 32);
                self.state.lo = sign_extend((acc as u32) as u64, 32);
                0
            }
            SpecialFunction::DIV => {
                // div
                self.state.hi = sign_extend((rs as i32 % rt as i32) as u64, 32);
                self.state.lo = sign_extend((rs as i32 / rt as i32) as u64, 32);
                0
            }
            SpecialFunction::DIVU => {
                // divu
                self.state.hi = sign_extend((rs as u32 % rt as u32) as u64, 32);
                self.state.lo = sign_extend((rs as u32 / rt as u32) as u64, 32);
                0
            }
            // MIPS64
            SpecialFunction::DMULTU => {
                // dmultu
                let acc = (rs as u128).wrapping_mul(rt as u128); // Perform 64-bit unsigned multiplication

                self.state.hi = (acc >> 64) as u64; // Upper 64 bits
                self.state.lo = acc as u64; // Lower 64 bits
                0
            }
            SpecialFunction::DDIVU => {
                // ddivu
                self.state.hi = rs % rt;
                self.state.lo = rs / rt;
                0
            }
            _ => 0,
        };

        if store_reg != 0 {
            self.state.registers[store_reg] = val;
        }

        self.state.pc = self.state.next_pc;
        self.state.next_pc += 4;

        Ok(())
    }

    /// Handles a jump within the MIPS thread context emulation.
    ///
    /// ### Takes
    /// - `link_reg`: The register index of the link register.
    /// - `dest`: The destination address of the jump.
    ///
    /// ### Returns
    /// - A [Result] indicating if the branch dispatch was successful.
    #[inline]
    pub(crate) fn handle_jump(&mut self, link_reg: usize, dest: Address) -> Result<()> {
        if self.state.next_pc != self.state.pc + 4 {
            anyhow::bail!("Unexpected jump in delay slot at {:x}", self.state.pc);
        }

        let prev_pc = self.state.pc;
        self.state.pc = self.state.next_pc;
        self.state.next_pc = dest;
        if link_reg != 0 {
            self.state.registers[link_reg as usize] = prev_pc + 8;
        }
        Ok(())
    }

    /// Handles a register destination instruction within the MIPS thread context emulation.
    ///
    /// ### Takes
    /// - `store_reg`: The register index of the register to store the result in.
    /// - `val`: The value to store in the register.
    /// - `conditional`: Whether or not the register should be updated.
    ///
    /// ### Returns
    /// - A [Result] indicating if the branch dispatch was successful.
    #[inline]
    pub(crate) fn handle_rd(
        &mut self,
        store_reg: usize,
        val: DoubleWord,
        conditional: bool,
    ) -> Result<()> {
        if store_reg >= 32 {
            anyhow::bail!("Invalid register index {}", store_reg);
        }

        if store_reg != 0 && conditional {
            self.state.registers[store_reg as usize] = val;
        }

        self.state.pc = self.state.next_pc;
        self.state.next_pc += 4;
        Ok(())
    }

    /// Read the preimage for the given key and offset from the [PreimageOracle] server.
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

        self.last_preimage_offset = offset;

        let mut data = [0u8; 32];
        let data_len =
            BufReader::new(&self.last_preimage[offset as usize..]).read(data.as_mut_slice())?;
        Ok((data, data_len))
    }

    /// Track an access to [crate::Memory] at the given [Address].
    ///
    /// ### Takes
    /// - `effective_address`: The address in [crate::Memory] being accessed.
    ///
    /// ### Returns
    /// - A [Result] indicating if the operation was successful.
    #[inline(always)]
    pub(crate) fn track_mem_access(&mut self, effective_address: Address) -> Result<()> {
        if self.mem_proof_enabled && self.last_mem_access != effective_address {
            if self.last_mem_access != Address::MAX {
                anyhow::bail!("Unexpected diffrent memory access at {:x}, already have access at {:x} buffered", effective_address, self.last_mem_access);
            }

            self.last_mem_access = effective_address;
            self.mem_proof = self.state.memory.merkle_proof(effective_address)?;
        }
        Ok(())
    }
}
