//! Supported MIPS32/MIPS64 instructions for the emulator.

use super::def_enum;
use anyhow::Result;

/// A single word within the MIPS64 architecture is 32 bits wide.
pub type Word = u32;

/// A double word within the MIPS64 architecture is 64 bits wide.
pub type DoubleWord = u64;

/// A J-Type instruction in the MIPS64 architecture.
///
/// **Encoding:**
/// | Bit Offset | Description |
/// | ---------- | ----------- |
/// | `[0, 6)`   | Opcode      |
/// | `[6, 32)`  | Target      |
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

/// An R-Type instruction in the MIPS64 architecture.
///
/// **Encoding:**
/// | Bit Offset | Description |
/// | ---------- | ----------- |
/// | `[0, 6)`   | Opcode      |
/// | `[6, 11)`  | rs          |
/// | `[11, 16)` | rt          |
/// | `[16, 21)` | rd          |
/// | `[21, 26)` | shamt       |
/// | `[26, 32)` | function    |
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

/// An I-type instruction in the MIPS64 architecture.
///
/// **Encoding:**
/// | Bit Offset | Description |
/// | ---------- | ----------- |
/// | `[0, 6)`   | Opcode      |
/// | `[6, 11)`  | rs          |
/// | `[11, 16)` | rt          |
/// | `[16, 32)` | Immediate   |
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

def_enum!(Opcode {
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
    LDL = 0x1A,
    LDR = 0x1B,
    SDL = 0x2C,
    SDR = 0x2D,
    LWU = 0x27,
    LLD = 0x34,
    LD = 0x37,
    SCD = 0x3C,
    SD = 0x3F,
});

def_enum!(SpecialFunction {
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
    SLT = 0x2A,
    SLTU = 0x2B,

    // MIPS64
    DSLLV = 0x14,
    DSRLV = 0x16,
    DSRAV = 0x17,
    DDIV = 0x1E,
    DMULT = 0x1C,
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
});

def_enum!(Special2Function {
    // MIPS32
    MUL = 0x02,
    CLO = 0x20,
    CLZ = 0x21,
    // MIPS64
    DCLZ = 0x24
});

def_enum!(RegImmFunction {
    // MIPS32
    BLTZ = 0x00,
    BGEZ = 0x01,
    BGEZAL = 0x11,
});

#[cfg(test)]
mod test {
    use crate::mips::isa::{IType, JType, RType};

    #[test]
    fn decode_j_type() {
        #[allow(clippy::unusual_byte_groupings)]
        let example_j_type = 0b010101_10101010101010101010101010;

        assert_eq!(JType::decode(example_j_type).unwrap().address, 0b10101010101010101010101010);
    }

    #[test]
    fn decode_r_type() {
        #[allow(clippy::unusual_byte_groupings)]
        let example_r_type = 0b000000_00001_00010_00011_00100_000101;

        let r_type = RType::decode(example_r_type).unwrap();
        assert_eq!(r_type.rs, 0b00001);
        assert_eq!(r_type.rt, 0b00010);
        assert_eq!(r_type.rd, 0b00011);
        assert_eq!(r_type.shamt, 0b00100);
        assert_eq!(r_type.funct, 0b000101);
    }

    #[test]
    fn decode_i_type() {
        #[allow(clippy::unusual_byte_groupings)]
        let example_i_type = 0b010111_11111_00001_1111111111111111;

        let i_type = IType::decode(example_i_type).unwrap();
        assert_eq!(i_type.rs, 0b11111);
        assert_eq!(i_type.rt, 0b00001);
        assert_eq!(i_type.imm, 0b1111111111111111);
    }
}
