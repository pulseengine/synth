//! ARM Code Encoder - Converts ARM instructions to binary machine code
//!
//! Generates ARM32/Thumb-2 machine code from ARM instruction structures

use synth_core::Result;
use synth_synthesis::{ArmOp, MemAddr, Operand2, Reg};

/// ARM instruction encoding
pub struct ArmEncoder {
    /// Use Thumb mode (vs ARM mode)
    thumb_mode: bool,
}

impl ArmEncoder {
    /// Create a new ARM encoder in ARM32 mode
    pub fn new_arm32() -> Self {
        Self { thumb_mode: false }
    }

    /// Create a new ARM encoder in Thumb-2 mode
    pub fn new_thumb2() -> Self {
        Self { thumb_mode: true }
    }

    /// Encode a single ARM instruction to bytes
    pub fn encode(&self, op: &ArmOp) -> Result<Vec<u8>> {
        if self.thumb_mode {
            self.encode_thumb(op)
        } else {
            self.encode_arm(op)
        }
    }

    /// Encode an ARM instruction in ARM32 mode (32-bit instructions)
    fn encode_arm(&self, op: &ArmOp) -> Result<Vec<u8>> {
        let instr: u32 = match op {
            // Data processing instructions
            ArmOp::Add { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // ADD encoding: cond(4) | 00 | I(1) | 0100 | S(1) | Rn(4) | Rd(4) | operand2(12)
                0xE0800000 // condition=always(E), opcode=ADD(0100), S=0
                    | (i_flag << 25)
                    | (rn_bits << 16)
                    | (rd_bits << 12)
                    | op2_bits
            }

            ArmOp::Sub { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // SUB encoding: opcode=0010
                0xE0400000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Mul { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // MUL encoding: cond(4) | 000000 | A(1) | S(1) | Rd(4) | Rn(4) | Rs(4) | 1001 | Rm(4)
                0xE0000090 | (rd_bits << 16) | (rn_bits << 8) | rm_bits
            }

            ArmOp::Sdiv { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // SDIV encoding: cond(4) | 01110001 | Rd(4) | 1111 | Rm(4) | 0001 | Rn(4)
                // ARMv7-M and above
                0xE710F010 | (rd_bits << 16) | (rm_bits << 8) | rn_bits
            }

            ArmOp::Udiv { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // UDIV encoding: cond(4) | 01110011 | Rd(4) | 1111 | Rm(4) | 0001 | Rn(4)
                // ARMv7-M and above
                0xE730F010 | (rd_bits << 16) | (rm_bits << 8) | rn_bits
            }

            ArmOp::Mls { rd, rn, rm, ra } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                let ra_bits = reg_to_bits(ra);

                // MLS encoding: cond(4) | 00000110 | Rd(4) | Ra(4) | Rm(4) | 1001 | Rn(4)
                // Rd = Ra - (Rn * Rm)
                0xE0600090 | (rd_bits << 16) | (ra_bits << 12) | (rm_bits << 8) | rn_bits
            }

            ArmOp::And { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // AND encoding: opcode=0000
                0xE0000000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Orr { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // ORR encoding: opcode=1100
                0xE1800000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Eor { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // EOR encoding: opcode=0001
                0xE0200000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            // Shift instructions
            ArmOp::Lsl { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = (*shift as u32) & 0x1F;

                // LSL encoding: MOV with shift
                0xE1A00000 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            ArmOp::Lsr { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = (*shift as u32) & 0x1F;

                // LSR encoding
                0xE1A00020 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            ArmOp::Asr { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = (*shift as u32) & 0x1F;

                // ASR encoding
                0xE1A00040 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            ArmOp::Ror { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = (*shift as u32) & 0x1F;

                // ROR encoding: MOV with ROR shift
                0xE1A00060 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            // Bit manipulation instructions
            ArmOp::Clz { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);

                // CLZ encoding: cond(4) | 00010110 | 1111 | Rd(4) | 1111 | 0001 | Rm(4)
                // ARMv5T and above
                0xE16F0F10 | (rd_bits << 12) | rm_bits
            }

            ArmOp::Rbit { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);

                // RBIT encoding: cond(4) | 01101111 | 1111 | Rd(4) | 1111 | 0011 | Rm(4)
                // ARMv6T2 and above
                0xE6FF0F30 | (rd_bits << 12) | rm_bits
            }

            // Move instructions
            ArmOp::Mov { rd, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // MOV encoding: opcode=1101
                0xE1A00000 | (i_flag << 25) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Mvn { rd, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // MVN encoding: opcode=1111
                0xE1E00000 | (i_flag << 25) | (rd_bits << 12) | op2_bits
            }

            // Compare
            ArmOp::Cmp { rn, op2 } => {
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // CMP encoding: opcode=1010, S=1
                0xE1500000 | (i_flag << 25) | (rn_bits << 16) | op2_bits
            }

            // Load/Store
            ArmOp::Ldr { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);

                // LDR encoding: cond(4) | 01 | I(1) | P(1) | U(1) | B(1) | W(1) | L(1) | Rn(4) | Rd(4) | offset(12)
                // P=1 (pre-indexed), U=1 (add offset), L=1 (load)
                0xE5900000 | (base_bits << 16) | (rd_bits << 12) | offset_bits
            }

            ArmOp::Str { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);

                // STR encoding: L=0 (store)
                0xE5800000 | (base_bits << 16) | (rd_bits << 12) | offset_bits
            }

            // Branch instructions
            ArmOp::B { label: _ } => {
                // B encoding: cond(4) | 1010 | offset(24)
                // Simplified: branch to offset 0
                0xEA000000
            }

            ArmOp::Bl { label: _ } => {
                // BL encoding: cond(4) | 1011 | offset(24)
                0xEB000000
            }

            ArmOp::Bx { rm } => {
                let rm_bits = reg_to_bits(rm);

                // BX encoding: cond(4) | 000100101111111111110001 | Rm(4)
                0xE12FFF10 | rm_bits
            }

            ArmOp::Nop => {
                // NOP encoding: MOV R0, R0
                0xE1A00000
            }

            // Pseudo-instructions for verification - encode as NOP
            // These are used in formal verification but not actual code generation
            ArmOp::Popcnt { .. } => {
                // Population count pseudo-instruction
                // Not a real ARM instruction, would be expanded to actual code
                0xE1A00000 // NOP for now
            }

            ArmOp::SetCond { .. } => {
                // Condition evaluation pseudo-instruction
                // Not a real ARM instruction, would be expanded to actual code
                0xE1A00000 // NOP for now
            }

            ArmOp::Select { .. } => {
                // Select pseudo-instruction
                // Not a real ARM instruction, would be expanded to conditional moves
                0xE1A00000 // NOP for now
            }

            ArmOp::LocalGet { .. } => {
                // Local variable get pseudo-instruction
                // Not a real ARM instruction, would be expanded to memory access
                0xE1A00000 // NOP for now
            }

            ArmOp::LocalSet { .. } => {
                // Local variable set pseudo-instruction
                // Not a real ARM instruction, would be expanded to memory access
                0xE1A00000 // NOP for now
            }

            ArmOp::LocalTee { .. } => {
                // Local variable tee pseudo-instruction
                // Not a real ARM instruction, would be expanded to memory access
                0xE1A00000 // NOP for now
            }

            ArmOp::GlobalGet { .. } => {
                // Global variable get pseudo-instruction
                // Not a real ARM instruction, would be expanded to memory access
                0xE1A00000 // NOP for now
            }

            ArmOp::GlobalSet { .. } => {
                // Global variable set pseudo-instruction
                // Not a real ARM instruction, would be expanded to memory access
                0xE1A00000 // NOP for now
            }

            ArmOp::BrTable { .. } => {
                // Branch table pseudo-instruction
                // Not a real ARM instruction, would be expanded to jump table
                0xE1A00000 // NOP for now
            }

            ArmOp::Call { .. } => {
                // Function call pseudo-instruction
                // Not a real ARM instruction, would be expanded to BL
                0xE1A00000 // NOP for now
            }

            ArmOp::CallIndirect { .. } => {
                // Indirect function call pseudo-instruction
                // Not a real ARM instruction, would be expanded to indirect branch
                0xE1A00000 // NOP for now
            }

            // i64 pseudo-instructions (Phase 2) - encode as NOP for now
            // Real compiler would expand these to multi-instruction sequences
            ArmOp::I64Add { .. } => 0xE1A00000,  // NOP
            ArmOp::I64Sub { .. } => 0xE1A00000,  // NOP
            ArmOp::I64Mul { .. } => 0xE1A00000,  // NOP
            ArmOp::I64And { .. } => 0xE1A00000,  // NOP
            ArmOp::I64Or { .. } => 0xE1A00000,   // NOP
            ArmOp::I64Xor { .. } => 0xE1A00000,  // NOP
            ArmOp::I64Eqz { .. } => 0xE1A00000,  // NOP
            ArmOp::I64Eq { .. } => 0xE1A00000,   // NOP
            ArmOp::I64LtS { .. } => 0xE1A00000,  // NOP
            ArmOp::I64LtU { .. } => 0xE1A00000,  // NOP
            ArmOp::I64Const { .. } => 0xE1A00000,  // NOP
            ArmOp::I64ExtendI32S { .. } => 0xE1A00000,  // NOP
            ArmOp::I64ExtendI32U { .. } => 0xE1A00000,  // NOP
            ArmOp::I32WrapI64 { .. } => 0xE1A00000,  // NOP
        };

        // ARM32 instructions are little-endian
        Ok(instr.to_le_bytes().to_vec())
    }

    /// Encode an ARM instruction in Thumb-2 mode (16-bit or 32-bit instructions)
    fn encode_thumb(&self, op: &ArmOp) -> Result<Vec<u8>> {
        // Simplified Thumb-2 encoding
        // For now, use 16-bit encodings for simple operations
        let instr: u16 = match op {
            ArmOp::Add { rd, rn, op2 } => {
                // Simplified: ADDS Rd, Rn, Rm (16-bit)
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    0x1800 | (rm_bits << 6) | (rn_bits << 3) | rd_bits
                } else {
                    // MOV placeholder
                    0x4600
                }
            }

            ArmOp::Mov { rd, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;

                if let Operand2::Imm(imm) = op2 {
                    let imm_bits = (*imm as u16) & 0xFF;
                    0x2000 | (rd_bits << 8) | imm_bits
                } else {
                    0x4600 | (rd_bits << 3)
                }
            }

            ArmOp::Nop => 0xBF00, // NOP in Thumb-2

            _ => 0xBF00, // NOP placeholder for unsupported ops
        };

        // Thumb instructions are little-endian
        Ok(instr.to_le_bytes().to_vec())
    }

    /// Encode a sequence of ARM instructions
    pub fn encode_sequence(&self, ops: &[ArmOp]) -> Result<Vec<u8>> {
        let mut code = Vec::new();

        for op in ops {
            let encoded = self.encode(op)?;
            code.extend_from_slice(&encoded);
        }

        Ok(code)
    }
}

/// Convert register to bit encoding (0-15)
fn reg_to_bits(reg: &Reg) -> u32 {
    match reg {
        Reg::R0 => 0,
        Reg::R1 => 1,
        Reg::R2 => 2,
        Reg::R3 => 3,
        Reg::R4 => 4,
        Reg::R5 => 5,
        Reg::R6 => 6,
        Reg::R7 => 7,
        Reg::R8 => 8,
        Reg::R9 => 9,
        Reg::R10 => 10,
        Reg::R11 => 11,
        Reg::R12 => 12,
        Reg::SP => 13,
        Reg::LR => 14,
        Reg::PC => 15,
    }
}

/// Encode operand2 field and return (bits, immediate_flag)
fn encode_operand2(op2: &Operand2) -> (u32, u32) {
    match op2 {
        Operand2::Imm(val) => {
            // Simplified: assume value fits in 8-bit immediate
            let imm = (*val as u32) & 0xFF;
            (imm, 1) // I=1 for immediate
        }

        Operand2::Reg(reg) => {
            let reg_bits = reg_to_bits(reg);
            (reg_bits, 0) // I=0 for register
        }

        Operand2::RegShift { rm, shift: _, amount } => {
            // Simplified encoding with shift
            let rm_bits = reg_to_bits(rm);
            let shift_bits = (*amount & 0x1F) << 7;
            (shift_bits | rm_bits, 0)
        }
    }
}

/// Encode memory address to (base_reg, offset)
fn encode_mem_addr(addr: &MemAddr) -> (u32, u32) {
    let base_bits = reg_to_bits(&addr.base);
    let offset_bits = (addr.offset as u32) & 0xFFF; // 12-bit offset
    (base_bits, offset_bits)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encoder_creation() {
        let encoder_arm = ArmEncoder::new_arm32();
        assert!(!encoder_arm.thumb_mode);

        let encoder_thumb = ArmEncoder::new_thumb2();
        assert!(encoder_thumb.thumb_mode);
    }

    #[test]
    fn test_encode_nop_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let code = encoder.encode(&ArmOp::Nop).unwrap();

        assert_eq!(code.len(), 4); // ARM32 instructions are 4 bytes
        assert_eq!(code, vec![0x00, 0x00, 0xA0, 0xE1]); // MOV R0, R0
    }

    #[test]
    fn test_encode_nop_thumb() {
        let encoder = ArmEncoder::new_thumb2();
        let code = encoder.encode(&ArmOp::Nop).unwrap();

        assert_eq!(code.len(), 2); // Thumb instructions are 2 bytes
        assert_eq!(code, vec![0x00, 0xBF]); // NOP
    }

    #[test]
    fn test_encode_mov_immediate_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Mov {
            rd: Reg::R0,
            op2: Operand2::Imm(42),
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);

        // Verify it's a MOV instruction (bits should have immediate flag set)
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(instr & 0x0E000000, 0x02000000); // Check I bit is set
    }

    #[test]
    fn test_encode_add_registers_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);

        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        // Verify it's an ADD instruction with correct opcode
        assert_eq!(instr & 0x0FE00000, 0x00800000);
    }

    #[test]
    fn test_encode_ldr_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Ldr {
            rd: Reg::R0,
            addr: MemAddr {
                base: Reg::R1,
                offset: 4,
            },
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);

        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        // Verify load bit is set
        assert_eq!(instr & 0x00100000, 0x00100000);
    }

    #[test]
    fn test_encode_str_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Str {
            rd: Reg::R0,
            addr: MemAddr {
                base: Reg::SP,
                offset: 0,
            },
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_branch_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Bl {
            label: "main".to_string(),
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);

        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        // Verify BL opcode
        assert_eq!(instr & 0x0F000000, 0x0B000000);
    }

    #[test]
    fn test_encode_sequence() {
        let encoder = ArmEncoder::new_arm32();
        let ops = vec![
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(42),
            },
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Imm(10),
            },
            ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
        ];

        let code = encoder.encode_sequence(&ops).unwrap();
        assert_eq!(code.len(), 12); // 3 instructions * 4 bytes
    }

    #[test]
    fn test_reg_to_bits() {
        assert_eq!(reg_to_bits(&Reg::R0), 0);
        assert_eq!(reg_to_bits(&Reg::R7), 7);
        assert_eq!(reg_to_bits(&Reg::SP), 13);
        assert_eq!(reg_to_bits(&Reg::LR), 14);
        assert_eq!(reg_to_bits(&Reg::PC), 15);
    }

    #[test]
    fn test_encode_bitwise_operations() {
        let encoder = ArmEncoder::new_arm32();

        let and_op = ArmOp::And {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        let and_code = encoder.encode(&and_op).unwrap();
        assert_eq!(and_code.len(), 4);

        let orr_op = ArmOp::Orr {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        let orr_code = encoder.encode(&orr_op).unwrap();
        assert_eq!(orr_code.len(), 4);

        let eor_op = ArmOp::Eor {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        let eor_code = encoder.encode(&eor_op).unwrap();
        assert_eq!(eor_code.len(), 4);
    }
}
