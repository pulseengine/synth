//! RV32 instruction encoder — translates `RiscVOp` to 32-bit machine words.
//!
//! Reference: RISC-V Unprivileged ISA, version 20191213 (Volume I), § 2.2-2.6.
//! All encodings below are little-endian 32-bit instructions.
//!
//! The encoder is intentionally thin: branches/jumps with labels are NOT
//! resolved here — the ELF builder fills those after layout. This module
//! handles the mechanical bit-packing.

use crate::riscv_op::{Branch, Csr, RiscVOp};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RiscVEncodingError {
    #[error("immediate {value} out of range for {what} (allowed: {min}..={max})")]
    ImmediateOutOfRange {
        value: i64,
        what: &'static str,
        min: i64,
        max: i64,
    },

    #[error("shift amount {0} out of range (must be 0..32)")]
    ShiftAmountOutOfRange(u8),

    #[error("CSR address 0x{0:03X} out of range (must be 12-bit)")]
    CsrOutOfRange(u16),

    #[error("instruction `{0}` requires label resolution and cannot be encoded standalone")]
    UnresolvedLabel(&'static str),
}

pub type EncodingResult = Result<u32, RiscVEncodingError>;

/// RV32IMAC encoder.
///
/// `xlen` selects between RV32 (32) and RV64 (64). Currently only RV32 is
/// fully exercised; RV64-specific instructions (LD, SD, ADDIW, etc.) will be
/// added in a follow-up. Storing it here makes that a localized change.
pub struct RiscVEncoder {
    pub xlen: u8,
}

impl RiscVEncoder {
    pub fn new_rv32() -> Self {
        Self { xlen: 32 }
    }

    pub fn new_rv64() -> Self {
        Self { xlen: 64 }
    }

    /// Encode a single op. Variants requiring label resolution
    /// (`Jal`, `Branch`, `Call`, `Label`) return `UnresolvedLabel` —
    /// the ELF builder calls back through the lower-level helpers
    /// once it knows byte offsets.
    pub fn encode(&self, op: &RiscVOp) -> EncodingResult {
        use RiscVOp::*;
        match op {
            Lui { rd, imm20 } => Ok(encode_u(0b0110111, rd.num(), *imm20)),
            Auipc { rd, imm20 } => Ok(encode_u(0b0010111, rd.num(), *imm20)),

            Addi { rd, rs1, imm } => encode_i_signed(0b0010011, 0b000, rd.num(), rs1.num(), *imm),
            Slti { rd, rs1, imm } => encode_i_signed(0b0010011, 0b010, rd.num(), rs1.num(), *imm),
            Sltiu { rd, rs1, imm } => encode_i_signed(0b0010011, 0b011, rd.num(), rs1.num(), *imm),
            Xori { rd, rs1, imm } => encode_i_signed(0b0010011, 0b100, rd.num(), rs1.num(), *imm),
            Ori { rd, rs1, imm } => encode_i_signed(0b0010011, 0b110, rd.num(), rs1.num(), *imm),
            Andi { rd, rs1, imm } => encode_i_signed(0b0010011, 0b111, rd.num(), rs1.num(), *imm),

            Slli { rd, rs1, shamt } => {
                encode_shift(0b0010011, 0b001, 0b0000000, rd.num(), rs1.num(), *shamt)
            }
            Srli { rd, rs1, shamt } => {
                encode_shift(0b0010011, 0b101, 0b0000000, rd.num(), rs1.num(), *shamt)
            }
            Srai { rd, rs1, shamt } => {
                encode_shift(0b0010011, 0b101, 0b0100000, rd.num(), rs1.num(), *shamt)
            }

            Add { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b000,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Sub { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b000,
                0b0100000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Sll { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b001,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Slt { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b010,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Sltu { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b011,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Xor { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b100,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Srl { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b101,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Sra { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b101,
                0b0100000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Or { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b110,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            And { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b111,
                0b0000000,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),

            // Loads (I-type, opcode 0b0000011)
            Lb { rd, rs1, imm } => encode_i_signed(0b0000011, 0b000, rd.num(), rs1.num(), *imm),
            Lh { rd, rs1, imm } => encode_i_signed(0b0000011, 0b001, rd.num(), rs1.num(), *imm),
            Lw { rd, rs1, imm } => encode_i_signed(0b0000011, 0b010, rd.num(), rs1.num(), *imm),
            Lbu { rd, rs1, imm } => encode_i_signed(0b0000011, 0b100, rd.num(), rs1.num(), *imm),
            Lhu { rd, rs1, imm } => encode_i_signed(0b0000011, 0b101, rd.num(), rs1.num(), *imm),

            // Stores (S-type, opcode 0b0100011)
            Sb { rs1, rs2, imm } => encode_s(0b0100011, 0b000, rs1.num(), rs2.num(), *imm),
            Sh { rs1, rs2, imm } => encode_s(0b0100011, 0b001, rs1.num(), rs2.num(), *imm),
            Sw { rs1, rs2, imm } => encode_s(0b0100011, 0b010, rs1.num(), rs2.num(), *imm),

            // Jumps
            Jalr { rd, rs1, imm } => encode_i_signed(0b1100111, 0b000, rd.num(), rs1.num(), *imm),

            // System ops with fixed funct12 / funct7 encodings
            Ecall => Ok(encode_i_unsigned(0b1110011, 0b000, 0, 0, 0)),
            Ebreak => Ok(encode_i_unsigned(0b1110011, 0b000, 0, 0, 1)),
            Mret => Ok(encode_i_unsigned(0b1110011, 0b000, 0, 0, 0x302)),
            Wfi => Ok(encode_i_unsigned(0b1110011, 0b000, 0, 0, 0x105)),
            Fence => Ok(0x0FF0000F), // fence iorw, iorw

            // CSR ops
            Csrrw { rd, csr, rs1 } => encode_csr(0b001, rd.num(), rs1.num(), *csr),
            Csrrs { rd, csr, rs1 } => encode_csr(0b010, rd.num(), rs1.num(), *csr),
            Csrrc { rd, csr, rs1 } => encode_csr(0b011, rd.num(), rs1.num(), *csr),
            Csrrwi { rd, csr, uimm5 } => encode_csr(0b101, rd.num(), *uimm5, *csr),
            Csrrsi { rd, csr, uimm5 } => encode_csr(0b110, rd.num(), *uimm5, *csr),
            Csrrci { rd, csr, uimm5 } => encode_csr(0b111, rd.num(), *uimm5, *csr),

            // M-extension
            Mul { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b000,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Mulh { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b001,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Mulhsu { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b010,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Mulhu { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b011,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Div { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b100,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Divu { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b101,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Rem { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b110,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),
            Remu { rd, rs1, rs2 } => Ok(encode_r(
                0b0110011,
                0b111,
                0b0000001,
                rd.num(),
                rs1.num(),
                rs2.num(),
            )),

            // Label-relative ops — must be resolved by the ELF builder.
            Jal { .. } => Err(RiscVEncodingError::UnresolvedLabel("jal")),
            Branch { .. } => Err(RiscVEncodingError::UnresolvedLabel("branch")),
            Call { .. } => Err(RiscVEncodingError::UnresolvedLabel("call")),
            Label { .. } => Err(RiscVEncodingError::UnresolvedLabel("label")),
        }
    }

    /// Encode a `jal rd, label` once the byte offset is known.
    /// `rel_offset` is the byte distance from the JAL instruction to the target.
    /// Must be even and in the range [-1 MiB, +1 MiB).
    pub fn encode_jal(&self, rd: u8, rel_offset: i32) -> EncodingResult {
        encode_j(0b1101111, rd, rel_offset)
    }

    /// Encode a `b{cond} rs1, rs2, label` once the byte offset is known.
    /// `rel_offset` is the byte distance from the branch to the target.
    /// Must be even and in the range [-4 KiB, +4 KiB).
    pub fn encode_branch(&self, cond: Branch, rs1: u8, rs2: u8, rel_offset: i32) -> EncodingResult {
        encode_b(0b1100011, cond.funct3() as u32, rs1, rs2, rel_offset)
    }
}

impl Default for RiscVEncoder {
    fn default() -> Self {
        Self::new_rv32()
    }
}

// ────────────────────────────────────────────────────────────────────────
// Bit-packing helpers — one per RV32 instruction format.
// ────────────────────────────────────────────────────────────────────────

#[inline]
fn encode_r(opcode: u32, funct3: u32, funct7: u32, rd: u8, rs1: u8, rs2: u8) -> u32 {
    opcode
        | ((rd as u32 & 0x1F) << 7)
        | (funct3 << 12)
        | ((rs1 as u32 & 0x1F) << 15)
        | ((rs2 as u32 & 0x1F) << 20)
        | (funct7 << 25)
}

#[inline]
fn encode_i_unsigned(opcode: u32, funct3: u32, rd: u8, rs1: u8, imm12: u32) -> u32 {
    opcode
        | ((rd as u32 & 0x1F) << 7)
        | (funct3 << 12)
        | ((rs1 as u32 & 0x1F) << 15)
        | ((imm12 & 0xFFF) << 20)
}

fn encode_i_signed(opcode: u32, funct3: u32, rd: u8, rs1: u8, imm: i32) -> EncodingResult {
    if !(-2048..=2047).contains(&imm) {
        return Err(RiscVEncodingError::ImmediateOutOfRange {
            value: imm as i64,
            what: "I-type imm12",
            min: -2048,
            max: 2047,
        });
    }
    let imm12 = (imm as u32) & 0xFFF;
    Ok(encode_i_unsigned(opcode, funct3, rd, rs1, imm12))
}

fn encode_s(opcode: u32, funct3: u32, rs1: u8, rs2: u8, imm: i32) -> EncodingResult {
    if !(-2048..=2047).contains(&imm) {
        return Err(RiscVEncodingError::ImmediateOutOfRange {
            value: imm as i64,
            what: "S-type imm12",
            min: -2048,
            max: 2047,
        });
    }
    let imm12 = (imm as u32) & 0xFFF;
    let imm_low = imm12 & 0x1F; // imm[4:0]
    let imm_high = (imm12 >> 5) & 0x7F; // imm[11:5]
    Ok(opcode
        | (imm_low << 7)
        | (funct3 << 12)
        | ((rs1 as u32 & 0x1F) << 15)
        | ((rs2 as u32 & 0x1F) << 20)
        | (imm_high << 25))
}

fn encode_b(opcode: u32, funct3: u32, rs1: u8, rs2: u8, imm: i32) -> EncodingResult {
    if !(-4096..=4094).contains(&imm) || (imm & 1) != 0 {
        return Err(RiscVEncodingError::ImmediateOutOfRange {
            value: imm as i64,
            what: "B-type rel offset",
            min: -4096,
            max: 4094,
        });
    }
    let i = imm as u32 & 0x1FFE; // 13-bit signed, low bit always 0
    // Field layout for B-type imm:
    //   inst[31]   = imm[12]
    //   inst[7]    = imm[11]
    //   inst[30:25]= imm[10:5]
    //   inst[11:8] = imm[4:1]
    let bit12 = (i >> 12) & 0x1;
    let bit11 = (i >> 11) & 0x1;
    let bits10_5 = (i >> 5) & 0x3F;
    let bits4_1 = (i >> 1) & 0xF;
    Ok(opcode
        | (bit11 << 7)
        | (bits4_1 << 8)
        | (funct3 << 12)
        | ((rs1 as u32 & 0x1F) << 15)
        | ((rs2 as u32 & 0x1F) << 20)
        | (bits10_5 << 25)
        | (bit12 << 31))
}

#[inline]
fn encode_u(opcode: u32, rd: u8, imm20: u32) -> u32 {
    opcode | ((rd as u32 & 0x1F) << 7) | ((imm20 & 0xFFFFF) << 12)
}

fn encode_j(opcode: u32, rd: u8, imm: i32) -> EncodingResult {
    if !(-(1 << 20)..(1 << 20)).contains(&imm) || (imm & 1) != 0 {
        return Err(RiscVEncodingError::ImmediateOutOfRange {
            value: imm as i64,
            what: "J-type rel offset",
            min: -(1 << 20),
            max: (1 << 20) - 1,
        });
    }
    let i = imm as u32 & 0x1FFFFE; // 21-bit signed, low bit always 0
    // Field layout:
    //   inst[31]    = imm[20]
    //   inst[30:21] = imm[10:1]
    //   inst[20]    = imm[11]
    //   inst[19:12] = imm[19:12]
    let bit20 = (i >> 20) & 0x1;
    let bits10_1 = (i >> 1) & 0x3FF;
    let bit11 = (i >> 11) & 0x1;
    let bits19_12 = (i >> 12) & 0xFF;
    Ok(opcode
        | ((rd as u32 & 0x1F) << 7)
        | (bits19_12 << 12)
        | (bit11 << 20)
        | (bits10_1 << 21)
        | (bit20 << 31))
}

fn encode_shift(
    opcode: u32,
    funct3: u32,
    funct7: u32,
    rd: u8,
    rs1: u8,
    shamt: u8,
) -> EncodingResult {
    // RV32: shamt is 5 bits (0..31).
    if shamt >= 32 {
        return Err(RiscVEncodingError::ShiftAmountOutOfRange(shamt));
    }
    Ok(opcode
        | ((rd as u32 & 0x1F) << 7)
        | (funct3 << 12)
        | ((rs1 as u32 & 0x1F) << 15)
        | ((shamt as u32 & 0x1F) << 20)
        | (funct7 << 25))
}

fn encode_csr(funct3: u32, rd: u8, rs1_or_uimm: u8, csr: Csr) -> EncodingResult {
    if csr.0 >= 0x1000 {
        return Err(RiscVEncodingError::CsrOutOfRange(csr.0));
    }
    Ok(0b1110011
        | ((rd as u32 & 0x1F) << 7)
        | (funct3 << 12)
        | ((rs1_or_uimm as u32 & 0x1F) << 15)
        | ((csr.0 as u32 & 0xFFF) << 20))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::register::Reg;

    fn enc(op: RiscVOp) -> u32 {
        RiscVEncoder::new_rv32().encode(&op).unwrap()
    }

    // Reference encodings cross-checked with the RISC-V official spec
    // and the SiFive `riscv-opcodes` table. These aren't tautologies —
    // they're literal hex values that any toolchain (GAS, LLVM) must produce.

    #[test]
    fn addi_a0_a0_1() {
        // addi a0, a0, 1  →  00150513
        let inst = enc(RiscVOp::Addi {
            rd: Reg::A0,
            rs1: Reg::A0,
            imm: 1,
        });
        assert_eq!(inst, 0x00150513);
    }

    #[test]
    fn addi_zero_zero_neg1() {
        // addi zero, zero, -1  →  fff00013
        let inst = enc(RiscVOp::Addi {
            rd: Reg::ZERO,
            rs1: Reg::ZERO,
            imm: -1,
        });
        assert_eq!(inst, 0xFFF00013);
    }

    #[test]
    fn add_a0_a0_a1() {
        // add a0, a0, a1  →  00b50533
        let inst = enc(RiscVOp::Add {
            rd: Reg::A0,
            rs1: Reg::A0,
            rs2: Reg::A1,
        });
        assert_eq!(inst, 0x00B50533);
    }

    #[test]
    fn sub_a0_a0_a1() {
        // sub a0, a0, a1  →  40b50533
        let inst = enc(RiscVOp::Sub {
            rd: Reg::A0,
            rs1: Reg::A0,
            rs2: Reg::A1,
        });
        assert_eq!(inst, 0x40B50533);
    }

    #[test]
    fn lui_a0_0x12345() {
        // lui a0, 0x12345  →  12345537
        let inst = enc(RiscVOp::Lui {
            rd: Reg::A0,
            imm20: 0x12345,
        });
        assert_eq!(inst, 0x12345537);
    }

    #[test]
    fn auipc_ra_0() {
        // auipc ra, 0  →  00000097
        let inst = enc(RiscVOp::Auipc {
            rd: Reg::RA,
            imm20: 0,
        });
        assert_eq!(inst, 0x00000097);
    }

    #[test]
    fn jalr_ra_0_ra() {
        // jalr ra, 0(ra)  →  000080e7
        let inst = enc(RiscVOp::Jalr {
            rd: Reg::RA,
            rs1: Reg::RA,
            imm: 0,
        });
        assert_eq!(inst, 0x000080E7);
    }

    #[test]
    fn ret_jalr_zero_0_ra() {
        // ret = jalr zero, 0(ra)  →  00008067
        let inst = enc(RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::RA,
            imm: 0,
        });
        assert_eq!(inst, 0x00008067);
    }

    #[test]
    fn lw_a0_4_a0() {
        // lw a0, 4(a0)  →  00452503
        let inst = enc(RiscVOp::Lw {
            rd: Reg::A0,
            rs1: Reg::A0,
            imm: 4,
        });
        assert_eq!(inst, 0x00452503);
    }

    #[test]
    fn sw_a1_4_a0() {
        // sw a1, 4(a0)  →  00b52223
        let inst = enc(RiscVOp::Sw {
            rs1: Reg::A0,
            rs2: Reg::A1,
            imm: 4,
        });
        assert_eq!(inst, 0x00B52223);
    }

    #[test]
    fn slli_a0_a0_3() {
        // slli a0, a0, 3  →  00351513
        let inst = enc(RiscVOp::Slli {
            rd: Reg::A0,
            rs1: Reg::A0,
            shamt: 3,
        });
        assert_eq!(inst, 0x00351513);
    }

    #[test]
    fn srai_a0_a0_31() {
        // srai a0, a0, 31  →  41f55513
        let inst = enc(RiscVOp::Srai {
            rd: Reg::A0,
            rs1: Reg::A0,
            shamt: 31,
        });
        assert_eq!(inst, 0x41F55513);
    }

    #[test]
    fn ecall() {
        assert_eq!(enc(RiscVOp::Ecall), 0x00000073);
    }

    #[test]
    fn ebreak() {
        assert_eq!(enc(RiscVOp::Ebreak), 0x00100073);
    }

    #[test]
    fn mret() {
        assert_eq!(enc(RiscVOp::Mret), 0x30200073);
    }

    #[test]
    fn wfi() {
        assert_eq!(enc(RiscVOp::Wfi), 0x10500073);
    }

    #[test]
    fn fence_iorw() {
        assert_eq!(enc(RiscVOp::Fence), 0x0FF0000F);
    }

    #[test]
    fn csrrw_mtvec() {
        // csrrw zero, mtvec, a0  →  30551073
        let inst = enc(RiscVOp::Csrrw {
            rd: Reg::ZERO,
            csr: Csr::MTVEC,
            rs1: Reg::A0,
        });
        assert_eq!(inst, 0x30551073);
    }

    #[test]
    fn mul_a0_a0_a1() {
        // mul a0, a0, a1  →  02b50533
        let inst = enc(RiscVOp::Mul {
            rd: Reg::A0,
            rs1: Reg::A0,
            rs2: Reg::A1,
        });
        assert_eq!(inst, 0x02B50533);
    }

    #[test]
    fn divu_a0_a0_a1() {
        // divu a0, a0, a1  →  02b55533
        let inst = enc(RiscVOp::Divu {
            rd: Reg::A0,
            rs1: Reg::A0,
            rs2: Reg::A1,
        });
        assert_eq!(inst, 0x02B55533);
    }

    #[test]
    fn imm_out_of_range() {
        // addi a0, a0, 4096  → overflow (max is 2047)
        let result = RiscVEncoder::new_rv32().encode(&RiscVOp::Addi {
            rd: Reg::A0,
            rs1: Reg::A0,
            imm: 4096,
        });
        assert!(matches!(
            result,
            Err(RiscVEncodingError::ImmediateOutOfRange { .. })
        ));
    }

    #[test]
    fn shamt_out_of_range() {
        let result = RiscVEncoder::new_rv32().encode(&RiscVOp::Slli {
            rd: Reg::A0,
            rs1: Reg::A0,
            shamt: 32,
        });
        assert!(matches!(
            result,
            Err(RiscVEncodingError::ShiftAmountOutOfRange(32))
        ));
    }

    #[test]
    fn jal_unresolved() {
        let result = RiscVEncoder::new_rv32().encode(&RiscVOp::Jal {
            rd: Reg::RA,
            label: "foo".into(),
        });
        assert!(matches!(
            result,
            Err(RiscVEncodingError::UnresolvedLabel("jal"))
        ));
    }

    #[test]
    fn jal_resolved_forward_4() {
        // jal ra, +4 (next instruction)  →  004000ef
        let inst = RiscVEncoder::new_rv32()
            .encode_jal(Reg::RA.num(), 4)
            .unwrap();
        assert_eq!(inst, 0x004000EF);
    }

    #[test]
    fn jal_resolved_backward_4() {
        // jal ra, -4 (loop to self at offset -4)  →  ffdff0ef
        let inst = RiscVEncoder::new_rv32()
            .encode_jal(Reg::RA.num(), -4)
            .unwrap();
        assert_eq!(inst, 0xFFDFF0EF);
    }

    #[test]
    fn beq_a0_a1_8() {
        // beq a0, a1, +8  →  00b50463
        let inst = RiscVEncoder::new_rv32()
            .encode_branch(Branch::Eq, Reg::A0.num(), Reg::A1.num(), 8)
            .unwrap();
        assert_eq!(inst, 0x00B50463);
    }

    #[test]
    fn bne_a0_zero_neg4() {
        // bne a0, zero, -4 (busy-wait until zero)  →  fe051ee3
        let inst = RiscVEncoder::new_rv32()
            .encode_branch(Branch::Ne, Reg::A0.num(), Reg::ZERO.num(), -4)
            .unwrap();
        assert_eq!(inst, 0xFE051EE3);
    }

    #[test]
    fn branch_odd_offset_rejected() {
        let r = RiscVEncoder::new_rv32().encode_branch(Branch::Eq, 0, 0, 3);
        assert!(matches!(
            r,
            Err(RiscVEncodingError::ImmediateOutOfRange { .. })
        ));
    }
}
