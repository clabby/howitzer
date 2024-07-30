//! This module contains the MIPS VM implementation for the [InstrumentedState].

use super::mips_isa::{
    IType, JType, Opcode, RType, RegImmFunction, Special2Function, SpecialFunction,
};
use crate::{
    types::{Address, DoubleWord, Word},
    utils::sign_extend,
    InstrumentedState,
};
use anyhow::Result;
use kona_preimage::{HintRouter, PreimageFetcher};
use std::io::{BufReader, Read, Write};

const DOUBLEWORD_MASK: DoubleWord = DoubleWord::MAX;
const WORD_MASK: DoubleWord = Word::MAX as DoubleWord;

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

        // println!(
        //     "Step: {}, Opcode: {:?} | Instruction: {:04x}",
        //     self.state.step, opcode, instruction
        // );

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

        // Handle branch I-type instructions
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
            Opcode::ADDI |
                Opcode::ADDIU |
                Opcode::SLTI |
                Opcode::SLTIU |
                Opcode::ANDI |
                Opcode::ORI |
                Opcode::XORI |
                Opcode::DADDI |
                Opcode::DADDIU
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

        self.handle_rd(rd_reg_index, val, true)
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
                    SpecialFunction::SLLV => {
                        Some(sign_extend((rt_val & 0xFFFFFFFF) << (rs_val & 0x1F), 32))
                    }
                    SpecialFunction::SRLV => {
                        Some(sign_extend((rt_val & 0xFFFFFFFF) >> (rs_val & 0x1F), 32))
                    }
                    SpecialFunction::SRAV => Some(sign_extend(
                        ((rt_val & 0xFFFFFFFF) as i32 >> (rs_val & 0x1F)) as u64,
                        32 - rs_val,
                    )),
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
                    SpecialFunction::MFHI |
                    SpecialFunction::MTHI |
                    SpecialFunction::MFLO |
                    SpecialFunction::MTLO |
                    SpecialFunction::MULT |
                    SpecialFunction::MULTU |
                    SpecialFunction::DIV |
                    SpecialFunction::DIVU => {
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
                    SpecialFunction::SLT => Some(((rs_val as i64) < (rt_val as i64)) as DoubleWord),
                    SpecialFunction::SLTU => Some((rs_val < rt_val) as DoubleWord),

                    // MIPS64
                    SpecialFunction::DSLLV => Some(rt_val << (rs_val & 0x3F)),
                    SpecialFunction::DSRLV => Some(rt_val >> (rs_val & 0x3F)),
                    SpecialFunction::DSRAV => Some(((rt_val as i64) >> (rs_val & 0x3F)) as u64),
                    SpecialFunction::DMULTU | SpecialFunction::DDIVU | SpecialFunction::DDIV => {
                        self.handle_hi_lo(funct, rs_val, rt_val, instruction.rd as usize)?;
                        None
                    }
                    SpecialFunction::DADD => {
                        // TODO: Trap on overflow
                        Some(self.execute_immediate_alu(Opcode::DADDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::DADDU => {
                        Some(self.execute_immediate_alu(Opcode::DADDI, rs_val, rt_val)?)
                    }
                    SpecialFunction::DSUB => {
                        // TODO: Trap on underflow
                        Some(rs_val - rt_val)
                    }
                    SpecialFunction::DSUBU => Some(rs_val - rt_val),
                    SpecialFunction::DSRL => Some(rt_val >> instruction.shamt),
                    SpecialFunction::DSRA => Some(((rt_val as i64) >> instruction.shamt) as u64),
                    SpecialFunction::DSLL => Some(rt_val << instruction.shamt),
                    SpecialFunction::DSLL32 => Some(rt_val << (instruction.shamt + 32)),
                    SpecialFunction::DSRL32 => Some(rt_val >> (instruction.shamt + 32)),
                    SpecialFunction::DSRA32 => {
                        Some(((rt_val as i64) >> (instruction.shamt + 32)) as u64)
                    }
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
    #[inline]
    pub(crate) fn execute_immediate_alu(
        &mut self,
        opcode: Opcode,
        rs_val: DoubleWord,
        rt_val: DoubleWord,
    ) -> Result<DoubleWord> {
        match opcode {
            // MIPS32
            Opcode::ADDI | Opcode::ADDIU => Ok(sign_extend(rs_val + rt_val, 32)),
            Opcode::SLTI => Ok(((rs_val as i64) < (rt_val as i64)) as u64),
            Opcode::SLTIU => Ok((rs_val < rt_val) as u64),
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
    /// - `Ok((rd_idx, Option<store_address>, value))` - The result of the instruction execution.
    /// - `Err(_)`: An error occurred while executing the instruction.
    #[inline]
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
                // Grab the # of bytes to load from the word
                // This is the distance to the nearest aligned offset * 8
                let sl = (rs_val & 0x3) << 3;
                // Pull the bytes into the upper part of the word
                let val = mem << sl;
                // Create a mask for the untouched part of the dest register
                let mask = WORD_MASK >> (32 - sl);
                // Merge the values
                let merged = (val | (rt_val & mask)) & WORD_MASK;
                Ok((instruction.rt as usize, None, sign_extend(merged, 32)))
            }
            Opcode::LW | Opcode::LL => Ok((
                instruction.rt as usize,
                None,
                sign_extend((mem >> (32 - ((rs_val & 0x4) << 3))) & WORD_MASK, 32),
            )),
            Opcode::LBU => {
                Ok((instruction.rt as usize, None, (mem >> (56 - ((rs_val & 0x7) << 3))) & 0xFF))
            }
            Opcode::LHU => {
                Ok((instruction.rt as usize, None, (mem >> (48 - ((rs_val & 0x6) << 3))) & 0xFFFF))
            }
            Opcode::LWR => {
                // Grab the # of bytes to load from the word
                // This is the distance to the nearest aligned offset * 8
                let sr = 24 - ((rs_val & 0x3) << 3);
                // Pull the bytes into the lower part of the word
                let val = mem >> sr;
                // Create a mask for the untouched part of the dest register
                let mask = WORD_MASK << (32 - sr);
                // Merge the values
                let merged = (val | (rt_val & mask)) & WORD_MASK;
                Ok((instruction.rt as usize, None, sign_extend(merged, 32)))
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
                let val = ((rt_val & WORD_MASK) >> sr) << (32 - ((rs_val & 0x4) << 3));
                let mask = (WORD_MASK >> sr) << (32 - ((rs_val & 0x4) << 3));
                Ok((0, Some(address), (mem & !mask) | val))
            }
            Opcode::SW | Opcode::SC => {
                let sl = 32 - ((rs_val & 0x4) << 3);
                let val = (rt_val & WORD_MASK) << sl;
                let mask = DOUBLEWORD_MASK ^ (WORD_MASK << sl);

                if matches!(opcode, Opcode::SC) && instruction.rt != 0 {
                    self.state.registers[instruction.rt as usize] = 1;
                }

                Ok((0, Some(address), (mem & mask) | val))
            }
            Opcode::SWR => {
                let sl = 24 - ((rs_val & 0x3) << 3);
                let val = ((rt_val & WORD_MASK) << sl) << (32 - ((rs_val & 0x4) << 3));
                let mask = (((WORD_MASK as u32) << sl) as u64) << (32 - ((rs_val & 0x4) << 3));
                Ok((0, Some(address), (mem & !mask) | val))
            }
            // MIPS64
            Opcode::SDL => {
                let val = rt_val >> ((rs_val & 0x7) << 3);
                let mask = u64::MAX >> ((rs_val & 0x7) << 3);
                Ok((0, Some(address), (mem & !mask) | val))
            }
            Opcode::SDR => {
                let val = rt_val << (56 - ((rs_val & 0x7) << 3));
                let mask = u64::MAX << (56 - ((rs_val & 0x7) << 3));
                Ok((0, Some(address), (mem & !mask) | val))
            }
            Opcode::LWU => Ok((
                instruction.rt as usize,
                None,
                (mem >> (32 - ((rs_val & 0x4) << 3))) & WORD_MASK,
            )),
            Opcode::LD | Opcode::LLD => Ok((instruction.rt as usize, None, mem)),
            Opcode::SD | Opcode::SCD => {
                let shift_left = (rs_val & 0x7) << 3;
                let val = rt_val << shift_left;
                let mask = u64::MAX << shift_left;

                if matches!(opcode, Opcode::SCD) && instruction.rt != 0 {
                    self.state.registers[instruction.rt as usize] = 1;
                }

                Ok((0, Some(address), (mem & !mask) | val))
            }
            _ => anyhow::bail!("Invalid opcode {:?}", opcode),
        }
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
                (rs == rt && matches!(opcode, Opcode::BEQ)) ||
                    (rs != rt && matches!(opcode, Opcode::BNE))
            }
            // blez
            Opcode::BLEZ => (rs as i64) <= 0,
            // bgtz
            Opcode::BGTZ => (rs as i64) > 0,
            Opcode::REGIMM => match RegImmFunction::try_from(instruction.rt)? {
                RegImmFunction::BLTZ => (rs as i64) < 0,
                RegImmFunction::BGEZ => (rs as i64) >= 0,
                RegImmFunction::BGEZAL => {
                    // Always set the link register to pc + 8
                    self.state.registers[31] = self.state.pc + 8;

                    (rs as i64) >= 0
                }
            },
            _ => false,
        };

        let prev_pc = self.state.pc;
        self.state.pc = self.state.next_pc;

        if should_branch {
            self.state.next_pc =
                prev_pc + 4 + (sign_extend(instruction.imm as DoubleWord, 16) << 2);
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
                anyhow::ensure!(rt > 0, "TRAP: Division by zero");

                self.state.hi = sign_extend(((rs as i32) % (rt as i32)) as u64, 32);
                self.state.lo = sign_extend(((rs as i32) / (rt as i32)) as u64, 32);
                0
            }
            SpecialFunction::DIVU => {
                anyhow::ensure!(rt > 0, "TRAP: Division by zero");

                self.state.hi = ((rs as u32) % (rt as u32)) as u64;
                self.state.lo = ((rs as u32) / (rt as u32)) as u64;
                0
            }
            // MIPS64
            SpecialFunction::DMULTU => {
                // dmultu
                let acc = (rs as u128) * (rt as u128);

                self.state.hi = (acc >> 64) as u64;
                self.state.lo = acc as u64;
                0
            }
            SpecialFunction::DDIV => {
                anyhow::ensure!(rt > 0, "TRAP: Division by zero");

                self.state.hi = ((rs as i64) % (rt as i64)) as u64;
                self.state.lo = ((rs as i64) / (rt as i64)) as u64;
                0
            }
            SpecialFunction::DDIVU => {
                anyhow::ensure!(rt > 0, "TRAP: Division by zero");

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
            self.state.registers[link_reg] = prev_pc + 8;
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
            self.state.registers[store_reg] = val;
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
    #[inline]
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
    #[inline]
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
