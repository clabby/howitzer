//! Contains the supported MIPS instructions.

use crate::types::Word;
use anyhow::Result;

/// MIPS64 opcodes supported by the emulator.
#[derive(Debug, Clone, Copy)]
#[repr(u32)]
pub enum Opcode {
    // MIPS32
    SPECIAL = 0x00,
    REGIMM = 0x01,
    J = 0x02,
    JAL = 0x03,
    BEQ = 0x04,
    BNE = 0x05,
    BLEZ = 0x06,
    BGTZ = 0x07,
    ADDI = 0x08,
    ADDIU = 0x09,
    SLTI = 0x0A,
    SLTIU = 0x0B,
    ANDI = 0x0C,
    ORI = 0x0D,
    XORI = 0x0E,
    LUI = 0x0F,
    BEQL = 0x14,
    SPECIAL2 = 0x1C,
    LB = 0x20,
    LH = 0x21,
    LWL = 0x22,
    LW = 0x23,
    LBU = 0x24,
    LHU = 0x25,
    LWR = 0x26,
    SB = 0x28,
    SH = 0x29,
    SWL = 0x2A,
    SW = 0x2B,
    SWR = 0x2E,
    LL = 0x30,
    SC = 0x38,

    // MIPS64
    DADDI = 0x18,
    DADDIU = 0x19,
    LWU = 0x27,
    LLD = 0x34,
    LD = 0x37,
    SCD = 0x3C,
    SD = 0x3F,
}

impl TryFrom<u32> for Opcode {
    type Error = anyhow::Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            // MIPS32
            0x00 => Ok(Opcode::SPECIAL),
            0x01 => Ok(Opcode::REGIMM),
            0x02 => Ok(Opcode::J),
            0x03 => Ok(Opcode::JAL),
            0x04 => Ok(Opcode::BEQ),
            0x05 => Ok(Opcode::BNE),
            0x06 => Ok(Opcode::BLEZ),
            0x07 => Ok(Opcode::BGTZ),
            0x08 => Ok(Opcode::ADDI),
            0x09 => Ok(Opcode::ADDIU),
            0x0A => Ok(Opcode::SLTI),
            0x0B => Ok(Opcode::SLTIU),
            0x0C => Ok(Opcode::ANDI),
            0x0D => Ok(Opcode::ORI),
            0x0E => Ok(Opcode::XORI),
            0x0F => Ok(Opcode::LUI),
            0x14 => Ok(Opcode::BEQL),
            0x1C => Ok(Opcode::SPECIAL2),
            0x20 => Ok(Opcode::LB),
            0x21 => Ok(Opcode::LH),
            0x22 => Ok(Opcode::LWL),
            0x23 => Ok(Opcode::LW),
            0x24 => Ok(Opcode::LBU),
            0x25 => Ok(Opcode::LHU),
            0x26 => Ok(Opcode::LWR),
            0x28 => Ok(Opcode::SB),
            0x29 => Ok(Opcode::SH),
            0x2A => Ok(Opcode::SWL),
            0x2B => Ok(Opcode::SW),
            0x2E => Ok(Opcode::SWR),
            0x30 => Ok(Opcode::LL),
            0x38 => Ok(Opcode::SC),

            // MIPS64
            0x18 => Ok(Opcode::DADDI),
            0x19 => Ok(Opcode::DADDIU),
            0x27 => Ok(Opcode::LWU),
            0x34 => Ok(Opcode::LLD),
            0x37 => Ok(Opcode::LD),
            0x3C => Ok(Opcode::SCD),
            0x3F => Ok(Opcode::SD),
            _ => anyhow::bail!("Invalid opcode: {:02x}", value),
        }
    }
}

/// Supported functions for the [Opcode::SPECIAL] opcode.
#[derive(Debug, Clone, Copy)]
#[repr(u32)]
pub enum SpecialFunction {
    // MIPS32
    SLL = 0x00,
    SRL = 0x02,
    SRA = 0x03,
    SLLV = 0x04,
    SRLV = 0x06,
    SRAV = 0x07,
    JR = 0x08,
    JALR = 0x09,
    MOVZ = 0x0A,
    MOVN = 0x0B,
    SYSCALL = 0x0C,
    SYNC = 0x0F,
    MFHI = 0x10,
    MTHI = 0x11,
    MFLO = 0x12,
    MTLO = 0x13,
    MULT = 0x18,
    MULTU = 0x19,
    DIV = 0x1A,
    DIVU = 0x1B,
    ADD = 0x20,
    ADDU = 0x21,
    SUB = 0x22,
    SUBU = 0x23,
    AND = 0x24,
    OR = 0x25,
    XOR = 0x26,
    NOR = 0x27,
    SLTI = 0x2A,
    SLTIU = 0x2B,

    // MIPS64
    DSLLV = 0x14,
    DSRLV = 0x16,
    DMULTU = 0x1D,
    DDIVU = 0x1F,
    DADD = 0x2C,
    DADDU = 0x2D,
    DSUB = 0x2E,
    DSUBU = 0x2F,
    DSLL = 0x38,
    DSRL = 0x3A,
    DSRA = 0x3B,
    DSLL32 = 0x3C,
    DSRL32 = 0x3E,
    DSRA32 = 0x3F,
}

impl TryFrom<u32> for SpecialFunction {
    type Error = anyhow::Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            // MIPS32
            0x00 => Ok(SpecialFunction::SLL),
            0x02 => Ok(SpecialFunction::SRL),
            0x03 => Ok(SpecialFunction::SRA),
            0x04 => Ok(SpecialFunction::SLLV),
            0x06 => Ok(SpecialFunction::SRLV),
            0x07 => Ok(SpecialFunction::SRAV),
            0x08 => Ok(SpecialFunction::JR),
            0x09 => Ok(SpecialFunction::JALR),
            0x0A => Ok(SpecialFunction::MOVZ),
            0x0B => Ok(SpecialFunction::MOVN),
            0x0C => Ok(SpecialFunction::SYSCALL),
            0x0F => Ok(SpecialFunction::SYNC),
            0x10 => Ok(SpecialFunction::MFHI),
            0x11 => Ok(SpecialFunction::MTHI),
            0x12 => Ok(SpecialFunction::MFLO),
            0x13 => Ok(SpecialFunction::MTLO),
            0x18 => Ok(SpecialFunction::MULT),
            0x19 => Ok(SpecialFunction::MULTU),
            0x1A => Ok(SpecialFunction::DIV),
            0x1B => Ok(SpecialFunction::DIVU),
            0x20 => Ok(SpecialFunction::ADD),
            0x21 => Ok(SpecialFunction::ADDU),
            0x22 => Ok(SpecialFunction::SUB),
            0x23 => Ok(SpecialFunction::SUBU),
            0x24 => Ok(SpecialFunction::AND),
            0x25 => Ok(SpecialFunction::OR),
            0x26 => Ok(SpecialFunction::XOR),
            0x27 => Ok(SpecialFunction::NOR),
            0x2A => Ok(SpecialFunction::SLTI),
            0x2B => Ok(SpecialFunction::SLTIU),

            // MIPS64
            0x14 => Ok(SpecialFunction::DSLLV),
            0x16 => Ok(SpecialFunction::DSRLV),
            0x1D => Ok(SpecialFunction::DMULTU),
            0x1F => Ok(SpecialFunction::DDIVU),
            0x2C => Ok(SpecialFunction::DADD),
            0x2D => Ok(SpecialFunction::DADDU),
            0x2E => Ok(SpecialFunction::DSUB),
            0x2F => Ok(SpecialFunction::DSUBU),
            0x38 => Ok(SpecialFunction::DSLL),
            0x3A => Ok(SpecialFunction::DSRL),
            0x3B => Ok(SpecialFunction::DSRA),
            0x3C => Ok(SpecialFunction::DSLL32),
            0x3E => Ok(SpecialFunction::DSRL32),
            0x3F => Ok(SpecialFunction::DSRA32),
            _ => anyhow::bail!("Invalid special function: {:02x}", value),
        }
    }
}

/// Supported functions for the [Opcode::SPECIAL2] opcode.
#[derive(Debug, Clone, Copy)]
#[repr(u32)]
pub enum Special2Function {
    // MIPS32
    MUL = 0x02,
    CLO = 0x20,
    CLZ = 0x21,
}

impl TryFrom<u32> for Special2Function {
    type Error = anyhow::Error;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            0x02 => Ok(Special2Function::MUL),
            0x20 => Ok(Special2Function::CLO),
            0x21 => Ok(Special2Function::CLZ),
            _ => anyhow::bail!("Invalid special2 function: {:02x}", value),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct JType {
    /// Virtual address
    pub address: u32,
}

impl JType {
    /// Decodes a J-type MIPS64 instruction.
    ///
    /// # Arguments
    /// - `instruction`: The instruction to decode
    ///
    /// # Returns
    /// - `Ok(JType)` if the instruction was successfully decoded
    /// - `Err(_)` if the instruction could not be decoded
    pub fn decode(instruction: Word) -> Result<Self> {
        let address = instruction & 0x03_FF_FF_FF;
        Ok(JType { address })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct RType {
    /// Source register
    pub rs: u32,
    /// Target/source register
    pub rt: u32,
    /// Destination register
    pub rd: u32,
    /// Shift amount
    pub shamt: u32,
    /// Function
    pub funct: u32,
}

impl RType {
    /// Decodes an R-type MIPS64 instruction.
    ///
    /// # Arguments
    /// - `instruction`: The instruction to decode
    ///
    /// # Returns
    /// - `Ok(RType)` if the instruction was successfully decoded
    /// - `Err(_)` if the instruction could not be decoded
    pub fn decode(instruction: Word) -> Result<Self> {
        let rs = (instruction >> 21) & 0x1F;
        let rt = (instruction >> 16) & 0x1F;
        let rd = (instruction >> 11) & 0x1F;
        let shamt = (instruction >> 6) & 0x1F;
        let funct = instruction & 0x3F;
        Ok(RType { rs, rt, rd, shamt, funct })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct IType {
    /// Source register
    pub rs: u32,
    /// Target register
    pub rt: u32,
    /// Immediate value
    pub imm: u16,
}

impl IType {
    /// Decodes an I-type MIPS64 instruction.
    ///
    /// # Arguments
    /// - `instruction`: The instruction to decode
    ///
    /// # Returns
    /// - `Ok(IType)` if the instruction was successfully decoded
    /// - `Err(_)` if the instruction could not be decoded
    pub fn decode(instruction: Word) -> Result<Self> {
        let rs = (instruction >> 21) & 0x1F;
        let rt = (instruction >> 16) & 0x1F;
        let imm = instruction as u16;
        Ok(IType { rs, rt, imm })
    }
}
