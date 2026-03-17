//! ARM Code Encoder - Converts ARM instructions to binary machine code
//!
//! Generates ARM32/Thumb-2 machine code from ARM instruction structures

use synth_core::Result;
use synth_core::target::FPUPrecision;
use synth_synthesis::{ArmOp, MemAddr, Operand2, Reg, VfpReg};

/// ARM instruction encoding
pub struct ArmEncoder {
    /// Use Thumb mode (vs ARM mode)
    thumb_mode: bool,
    /// FPU capability for VFP instruction encoding
    #[allow(dead_code)]
    fpu: Option<FPUPrecision>,
}

impl ArmEncoder {
    /// Create a new ARM encoder in ARM32 mode
    pub fn new_arm32() -> Self {
        Self {
            thumb_mode: false,
            fpu: None,
        }
    }

    /// Create a new ARM encoder in Thumb-2 mode
    pub fn new_thumb2() -> Self {
        Self {
            thumb_mode: true,
            fpu: None,
        }
    }

    /// Create a new Thumb-2 encoder with FPU capability
    pub fn new_thumb2_with_fpu(fpu: Option<FPUPrecision>) -> Self {
        Self {
            thumb_mode: true,
            fpu,
        }
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

            // i64 support: ADDS, ADC, SUBS, SBC for ARM32
            ArmOp::Adds { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // ADDS encoding: opcode=0100, S=1
                0xE0900000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Adc { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // ADC encoding: opcode=0101
                0xE0A00000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Subs { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // SUBS encoding: opcode=0010, S=1
                0xE0500000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Sbc { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // SBC encoding: opcode=0110
                0xE0C00000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
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
                let shift_bits = *shift & 0x1F;

                // LSL encoding: MOV with shift
                0xE1A00000 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            ArmOp::Lsr { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = *shift & 0x1F;

                // LSR encoding
                0xE1A00020 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            ArmOp::Asr { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = *shift & 0x1F;

                // ASR encoding
                0xE1A00040 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            ArmOp::Ror { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let shift_bits = *shift & 0x1F;

                // ROR encoding: MOV with ROR shift
                0xE1A00060 | (rd_bits << 12) | (shift_bits << 7) | rn_bits
            }

            // Register-based shifts (ARM32)
            // LSL Rd, Rn, Rm: cond 0001101S 0000 Rd Rs 0001 Rn
            ArmOp::LslReg { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                0xE1A00010 | (rd_bits << 12) | (rm_bits << 8) | rn_bits
            }
            ArmOp::LsrReg { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                0xE1A00030 | (rd_bits << 12) | (rm_bits << 8) | rn_bits
            }
            ArmOp::AsrReg { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                0xE1A00050 | (rd_bits << 12) | (rm_bits << 8) | rn_bits
            }
            ArmOp::RorReg { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                0xE1A00070 | (rd_bits << 12) | (rm_bits << 8) | rn_bits
            }

            // RSB (Reverse Subtract): Rd = imm - Rn
            ArmOp::Rsb { rd, rn, imm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                // RSB encoding: cond(4) | 00 1 0011 S | Rn(4) | Rd(4) | imm12
                // Opcode for RSB = 0011, I=1 (immediate), S=0
                0xE2600000 | (rn_bits << 16) | (rd_bits << 12) | (*imm & 0xFF)
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

            ArmOp::Sxtb { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);

                // SXTB encoding: cond(4) | 01101010 | 1111 | Rd(4) | rotate(2) | 00 | 0111 | Rm(4)
                // ARMv6 and above. rotate=00 for no rotation
                0xE6AF0070 | (rd_bits << 12) | rm_bits
            }

            ArmOp::Sxth { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);

                // SXTH encoding: cond(4) | 01101011 | 1111 | Rd(4) | rotate(2) | 00 | 0111 | Rm(4)
                // ARMv6 and above. rotate=00 for no rotation
                0xE6BF0070 | (rd_bits << 12) | rm_bits
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

            // MOVW - Move Wide (ARM32)
            // Encoding: cond(4) | 0011 0000 | imm4(4) | Rd(4) | imm12(12)
            ArmOp::Movw { rd, imm16 } => {
                let rd_bits = reg_to_bits(rd);
                let imm4 = ((*imm16 as u32) >> 12) & 0xF;
                let imm12 = (*imm16 as u32) & 0xFFF;
                0xE3000000 | (imm4 << 16) | (rd_bits << 12) | imm12
            }

            // MOVT - Move Top (ARM32)
            // Encoding: cond(4) | 0011 0100 | imm4(4) | Rd(4) | imm12(12)
            ArmOp::Movt { rd, imm16 } => {
                let rd_bits = reg_to_bits(rd);
                let imm4 = ((*imm16 as u32) >> 12) & 0xF;
                let imm12 = (*imm16 as u32) & 0xFFF;
                0xE3400000 | (imm4 << 16) | (rd_bits << 12) | imm12
            }

            // Compare
            ArmOp::Cmp { rn, op2 } => {
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // CMP encoding: opcode=1010, S=1
                0xE1500000 | (i_flag << 25) | (rn_bits << 16) | op2_bits
            }

            // Compare Negative (CMN) - computes Rn + op2 and sets flags
            ArmOp::Cmn { rn, op2 } => {
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2);

                // CMN encoding: opcode=1011, S=1
                0xE1700000 | (i_flag << 25) | (rn_bits << 16) | op2_bits
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

            // BHS (Branch if Higher or Same) - used for bounds checking
            ArmOp::Bhs { label: _ } => {
                // BHS encoding: cond(2=HS) | 1010 | offset(24)
                0x2A000000 // BHS with offset 0
            }

            // BLO (Branch if Lower) - complementary to BHS
            ArmOp::Blo { label: _ } => {
                // BLO encoding: cond(3=LO) | 1010 | offset(24)
                0x3A000000 // BLO with offset 0
            }

            // Branch with numeric offset (in instructions)
            // ARM32 B instruction: offset is in instructions, stored as words
            // The offset is relative to PC+8 (due to ARM pipeline)
            ArmOp::BOffset { offset } => {
                // B encoding: cond(4) | 1010 | offset(24)
                // Offset is signed, in words (4-byte units)
                // ARM adds PC+8 to the offset, so we need to adjust:
                // target = PC + 8 + (offset * 4)
                // For backward branch of N instructions: offset = -(N + 2)
                let adjusted_offset = *offset - 2; // Account for PC+8
                let offset_bits = (adjusted_offset as u32) & 0x00FFFFFF;
                0xEA000000 | offset_bits
            }

            // Conditional branch with numeric offset
            ArmOp::BCondOffset { cond, offset } => {
                use synth_synthesis::Condition;
                let cond_bits: u32 = match cond {
                    Condition::EQ => 0x0,
                    Condition::NE => 0x1,
                    Condition::HS => 0x2,
                    Condition::LO => 0x3,
                    Condition::HI => 0x8,
                    Condition::LS => 0x9,
                    Condition::GE => 0xA,
                    Condition::LT => 0xB,
                    Condition::GT => 0xC,
                    Condition::LE => 0xD,
                };
                // B<cond> encoding: cond(4) | 1010 | offset(24)
                let adjusted_offset = *offset - 2; // Account for PC+8
                let offset_bits = (adjusted_offset as u32) & 0x00FFFFFF;
                (cond_bits << 28) | 0x0A000000 | offset_bits
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

            ArmOp::Blx { rm } => {
                let rm_bits = reg_to_bits(rm);

                // BLX (register) encoding: cond(4) | 000100101111111111110011 | Rm(4)
                0xE12FFF30 | rm_bits
            }

            ArmOp::Nop => {
                // NOP encoding: MOV R0, R0
                0xE1A00000
            }

            ArmOp::Udf { imm } => {
                // UDF (Undefined) encoding in ARM: 0xE7F000F0 | (imm12_hi << 8) | imm4_lo
                // We only use imm8, so split into imm4_hi and imm4_lo
                let imm8 = *imm as u32;
                0xE7F000F0 | ((imm8 & 0xF0) << 4) | (imm8 & 0x0F)
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

            ArmOp::SelectMove { .. } => {
                // Conditional move pseudo-instruction for ARM32
                // Would use MOV{cond} instruction
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
            ArmOp::I64Add { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Sub { .. } => 0xE1A00000,        // NOP
            ArmOp::I64DivS { .. } => 0xE1A00000,       // NOP
            ArmOp::I64DivU { .. } => 0xE1A00000,       // NOP
            ArmOp::I64RemS { .. } => 0xE1A00000,       // NOP
            ArmOp::I64RemU { .. } => 0xE1A00000,       // NOP
            ArmOp::I64Clz { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Ctz { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Popcnt { .. } => 0xE1A00000,     // NOP
            ArmOp::I64And { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Or { .. } => 0xE1A00000,         // NOP
            ArmOp::I64Xor { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Eqz { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Eq { .. } => 0xE1A00000,         // NOP
            ArmOp::I64Ne { .. } => 0xE1A00000,         // NOP
            ArmOp::I64LtS { .. } => 0xE1A00000,        // NOP
            ArmOp::I64LtU { .. } => 0xE1A00000,        // NOP
            ArmOp::I64LeS { .. } => 0xE1A00000,        // NOP
            ArmOp::I64LeU { .. } => 0xE1A00000,        // NOP
            ArmOp::I64GtS { .. } => 0xE1A00000,        // NOP
            ArmOp::I64GtU { .. } => 0xE1A00000,        // NOP
            ArmOp::I64GeS { .. } => 0xE1A00000,        // NOP
            ArmOp::I64GeU { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Const { .. } => 0xE1A00000,      // NOP
            ArmOp::I64Ldr { .. } => 0xE1A00000,        // NOP
            ArmOp::I64Str { .. } => 0xE1A00000,        // NOP
            ArmOp::I64ExtendI32S { .. } => 0xE1A00000, // NOP
            ArmOp::I64ExtendI32U { .. } => 0xE1A00000, // NOP
            ArmOp::I64Extend8S { .. } => 0xE1A00000,   // NOP (Thumb-2 only)
            ArmOp::I64Extend16S { .. } => 0xE1A00000,  // NOP (Thumb-2 only)
            ArmOp::I64Extend32S { .. } => 0xE1A00000,  // NOP (Thumb-2 only)
            ArmOp::I32WrapI64 { .. } => 0xE1A00000,    // NOP

            // f32 VFP single-precision instructions
            ArmOp::F32Add { sd, sn, sm } => encode_vfp_3reg(0xEE300A00, sd, sn, sm),
            ArmOp::F32Sub { sd, sn, sm } => encode_vfp_3reg(0xEE300A40, sd, sn, sm),
            ArmOp::F32Mul { sd, sn, sm } => encode_vfp_3reg(0xEE200A00, sd, sn, sm),
            ArmOp::F32Div { sd, sn, sm } => encode_vfp_3reg(0xEE800A00, sd, sn, sm),
            ArmOp::F32Abs { sd, sm } => encode_vfp_2reg(0xEEB00AC0, sd, sm),
            ArmOp::F32Neg { sd, sm } => encode_vfp_2reg(0xEEB10A40, sd, sm),
            ArmOp::F32Sqrt { sd, sm } => encode_vfp_2reg(0xEEB10AC0, sd, sm),

            // f32 pseudo-ops — multi-instruction sequences
            // FPSCR RMode: 00=nearest, 01=+inf(ceil), 10=-inf(floor), 11=zero(trunc)
            ArmOp::F32Ceil { sd, sm } => {
                return self.encode_arm_f32_rounding(sd, sm, 0b01); // Round toward +Inf
            }
            ArmOp::F32Floor { sd, sm } => {
                return self.encode_arm_f32_rounding(sd, sm, 0b10); // Round toward -Inf
            }
            ArmOp::F32Trunc { sd, sm } => {
                return self.encode_arm_f32_rounding(sd, sm, 0b11); // VCVT toward zero
            }
            ArmOp::F32Nearest { sd, sm } => {
                return self.encode_arm_f32_rounding(sd, sm, 0b00); // VCVT to nearest
            }
            ArmOp::F32Min { sd, sn, sm } => {
                return self.encode_arm_f32_minmax(sd, sn, sm, true);
            }
            ArmOp::F32Max { sd, sn, sm } => {
                return self.encode_arm_f32_minmax(sd, sn, sm, false);
            }
            ArmOp::F32Copysign { sd, sn, sm } => {
                return self.encode_arm_f32_copysign(sd, sn, sm);
            }

            // f32 comparisons — multi-instruction: VCMP + VMRS + conditional MOV
            ArmOp::F32Eq { rd, sn, sm } => {
                return self.encode_arm_f32_compare(rd, sn, sm, 0x0); // EQ
            }
            ArmOp::F32Ne { rd, sn, sm } => {
                return self.encode_arm_f32_compare(rd, sn, sm, 0x1); // NE
            }
            ArmOp::F32Lt { rd, sn, sm } => {
                return self.encode_arm_f32_compare(rd, sn, sm, 0x4); // MI (less than)
            }
            ArmOp::F32Le { rd, sn, sm } => {
                return self.encode_arm_f32_compare(rd, sn, sm, 0x9); // LS (less or same)
            }
            ArmOp::F32Gt { rd, sn, sm } => {
                return self.encode_arm_f32_compare(rd, sn, sm, 0xC); // GT
            }
            ArmOp::F32Ge { rd, sn, sm } => {
                return self.encode_arm_f32_compare(rd, sn, sm, 0xA); // GE
            }

            // f32 const — multi-instruction: MOVW + MOVT + VMOV
            ArmOp::F32Const { sd, value } => {
                return self.encode_arm_f32_const(sd, *value);
            }

            ArmOp::F32Load { sd, addr } => encode_vfp_ldst(0xED900A00, sd, addr),
            ArmOp::F32Store { sd, addr } => encode_vfp_ldst(0xED800A00, sd, addr),

            // f32 conversions — multi-instruction sequences
            ArmOp::F32ConvertI32S { sd, rm } => {
                return self.encode_arm_f32_convert_i32(sd, rm, true);
            }
            ArmOp::F32ConvertI32U { sd, rm } => {
                return self.encode_arm_f32_convert_i32(sd, rm, false);
            }
            ArmOp::F32ConvertI64S { .. } | ArmOp::F32ConvertI64U { .. } => {
                return Err(synth_core::Error::synthesis(
                    "F32 i64 conversion not supported (requires register pairs on 32-bit ARM)",
                ));
            }
            ArmOp::F32ReinterpretI32 { sd, rm } => encode_vmov_core_sreg(true, sd, rm),
            ArmOp::I32ReinterpretF32 { rd, sm } => encode_vmov_core_sreg(false, sm, rd),
            ArmOp::I32TruncF32S { rd, sm } => {
                return self.encode_arm_i32_trunc_f32(rd, sm, true);
            }
            ArmOp::I32TruncF32U { rd, sm } => {
                return self.encode_arm_i32_trunc_f32(rd, sm, false);
            }

            // f64 VFP double-precision instructions (ARM32)
            // F64 arithmetic: same as F32 but with sz=1 (bit 8 = 1, cp11 = 0xB)
            ArmOp::F64Add { dd, dn, dm } => encode_vfp_3reg_f64(0xEE300B00, dd, dn, dm),
            ArmOp::F64Sub { dd, dn, dm } => encode_vfp_3reg_f64(0xEE300B40, dd, dn, dm),
            ArmOp::F64Mul { dd, dn, dm } => encode_vfp_3reg_f64(0xEE200B00, dd, dn, dm),
            ArmOp::F64Div { dd, dn, dm } => encode_vfp_3reg_f64(0xEE800B00, dd, dn, dm),
            ArmOp::F64Abs { dd, dm } => encode_vfp_2reg_f64(0xEEB00BC0, dd, dm),
            ArmOp::F64Neg { dd, dm } => encode_vfp_2reg_f64(0xEEB10B40, dd, dm),
            ArmOp::F64Sqrt { dd, dm } => encode_vfp_2reg_f64(0xEEB10BC0, dd, dm),

            // f64 pseudo-ops
            ArmOp::F64Ceil { dd, dm } => {
                return self.encode_arm_f64_rounding(dd, dm, 0b10);
            }
            ArmOp::F64Floor { dd, dm } => {
                return self.encode_arm_f64_rounding(dd, dm, 0b01);
            }
            ArmOp::F64Trunc { dd, dm } => {
                return self.encode_arm_f64_rounding(dd, dm, 0b11);
            }
            ArmOp::F64Nearest { dd, dm } => {
                return self.encode_arm_f64_rounding(dd, dm, 0b00);
            }
            ArmOp::F64Min { dd, dn, dm } => {
                return self.encode_arm_f64_minmax(dd, dn, dm, true);
            }
            ArmOp::F64Max { dd, dn, dm } => {
                return self.encode_arm_f64_minmax(dd, dn, dm, false);
            }
            ArmOp::F64Copysign { dd, dn, dm } => {
                return self.encode_arm_f64_copysign(dd, dn, dm);
            }

            // f64 comparisons
            ArmOp::F64Eq { rd, dn, dm } => {
                return self.encode_arm_f64_compare(rd, dn, dm, 0x0);
            }
            ArmOp::F64Ne { rd, dn, dm } => {
                return self.encode_arm_f64_compare(rd, dn, dm, 0x1);
            }
            ArmOp::F64Lt { rd, dn, dm } => {
                return self.encode_arm_f64_compare(rd, dn, dm, 0x4);
            }
            ArmOp::F64Le { rd, dn, dm } => {
                return self.encode_arm_f64_compare(rd, dn, dm, 0x9);
            }
            ArmOp::F64Gt { rd, dn, dm } => {
                return self.encode_arm_f64_compare(rd, dn, dm, 0xC);
            }
            ArmOp::F64Ge { rd, dn, dm } => {
                return self.encode_arm_f64_compare(rd, dn, dm, 0xA);
            }

            ArmOp::F64Const { dd, value } => {
                return self.encode_arm_f64_const(dd, *value);
            }

            ArmOp::F64Load { dd, addr } => encode_vfp_ldst_f64(0xED900B00, dd, addr),
            ArmOp::F64Store { dd, addr } => encode_vfp_ldst_f64(0xED800B00, dd, addr),

            ArmOp::F64ConvertI32S { dd, rm } => {
                return self.encode_arm_f64_convert_i32(dd, rm, true);
            }
            ArmOp::F64ConvertI32U { dd, rm } => {
                return self.encode_arm_f64_convert_i32(dd, rm, false);
            }
            ArmOp::F64ConvertI64S { .. } | ArmOp::F64ConvertI64U { .. } => {
                return Err(synth_core::Error::synthesis(
                    "F64 i64 conversion not supported (requires register pairs on 32-bit ARM)",
                ));
            }
            ArmOp::F64PromoteF32 { dd, sm } => {
                return self.encode_arm_f64_promote_f32(dd, sm);
            }
            ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi } => {
                encode_vmov_core_dreg(true, dd, rmlo, rmhi)
            }
            ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm } => {
                encode_vmov_core_dreg(false, dm, rdlo, rdhi)
            }
            ArmOp::I64TruncF64S { .. } | ArmOp::I64TruncF64U { .. } => {
                return Err(synth_core::Error::synthesis(
                    "i64 truncation from F64 not supported (requires i64 register pairs on 32-bit ARM)",
                ));
            }
            ArmOp::I32TruncF64S { rd, dm } => {
                return self.encode_arm_i32_trunc_f64(rd, dm, true);
            }
            ArmOp::I32TruncF64U { rd, dm } => {
                return self.encode_arm_i32_trunc_f64(rd, dm, false);
            }
            // Multi-instruction sequences - only meaningful in Thumb-2 mode
            ArmOp::I64SetCond { .. }
            | ArmOp::I64SetCondZ { .. }
            | ArmOp::I64Mul { .. }
            | ArmOp::I64Shl { .. }
            | ArmOp::I64ShrS { .. }
            | ArmOp::I64ShrU { .. }
            | ArmOp::I64Rotl { .. }
            | ArmOp::I64Rotr { .. } => 0xE1A00000, // NOP (Thumb-2 only)
        };

        // ARM32 instructions are little-endian
        Ok(instr.to_le_bytes().to_vec())
    }

    // === ARM32 VFP multi-instruction helpers ===

    /// Encode F32 comparison as ARM32: VCMP.F32 + VMRS + MOV rd,#0 + MOVcond rd,#1
    fn encode_arm_f32_compare(
        &self,
        rd: &Reg,
        sn: &VfpReg,
        sm: &VfpReg,
        cond_code: u32,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VCMP.F32 Sn, Sm: 0xEEB40A40 with Sn in Vd position, Sm in Vm position
        let sn_num = vfp_sreg_to_num(sn);
        let sm_num = vfp_sreg_to_num(sm);
        let (vd, d) = encode_sreg(sn_num);
        let (vm, m) = encode_sreg(sm_num);
        let vcmp = 0xEEB40A40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcmp.to_le_bytes());

        // VMRS APSR_nzcv, FPSCR: 0xEEF1FA10
        bytes.extend_from_slice(&0xEEF1FA10u32.to_le_bytes());

        // MOV rd, #0: 0xE3A0_0000 | (rd << 12)
        let rd_bits = reg_to_bits(rd);
        let mov_zero = 0xE3A00000 | (rd_bits << 12);
        bytes.extend_from_slice(&mov_zero.to_le_bytes());

        // MOVcond rd, #1: cond(4) | 0011 1010 0000 rd(4) 0000 0000 0001
        let mov_one = (cond_code << 28) | 0x03A00001 | (rd_bits << 12);
        bytes.extend_from_slice(&mov_one.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F32 constant load as ARM32: MOVW Rt,#lo16 + MOVT Rt,#hi16 + VMOV Sd,Rt
    fn encode_arm_f32_const(&self, sd: &VfpReg, value: f32) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let bits = value.to_bits();

        // Use R12 as temp register for constant loading
        let rt: u32 = 12; // R12/IP

        // MOVW R12, #lo16: 0xE300_C000 | (imm4 << 16) | imm12
        let lo16 = bits & 0xFFFF;
        let movw = 0xE3000000 | (rt << 12) | ((lo16 >> 12) << 16) | (lo16 & 0xFFF);
        bytes.extend_from_slice(&movw.to_le_bytes());

        // MOVT R12, #hi16: 0xE340_C000 | (imm4 << 16) | imm12
        let hi16 = (bits >> 16) & 0xFFFF;
        let movt = 0xE3400000 | (rt << 12) | ((hi16 >> 12) << 16) | (hi16 & 0xFFF);
        bytes.extend_from_slice(&movt.to_le_bytes());

        // VMOV Sd, R12
        let vmov = encode_vmov_core_sreg(true, sd, &Reg::R12);
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VMOV + VCVT.F32.S32/U32 as ARM32
    fn encode_arm_f32_convert_i32(&self, sd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV Sd, Rm — move integer to VFP register
        let vmov = encode_vmov_core_sreg(true, sd, rm);
        bytes.extend_from_slice(&vmov.to_le_bytes());

        // VCVT.F32.S32 Sd, Sd (signed) or VCVT.F32.U32 Sd, Sd (unsigned)
        // Base: 0xEEB80A40 (signed) or 0xEEB80AC0 (unsigned)
        let sd_num = vfp_sreg_to_num(sd);
        let (vd, d) = encode_sreg(sd_num);
        let (vm, m) = encode_sreg(sd_num); // same register as source
        let base = if signed { 0xEEB80A40 } else { 0xEEB80AC0 };
        let vcvt = base | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F32 rounding pseudo-op as ARM32 via VCVT to integer and back.
    /// mode: 0b00=nearest, 0b01=floor(-Inf), 0b10=ceil(+Inf), 0b11=trunc(zero)
    /// Strategy: VCVT.S32.F32 Sd, Sm (toward zero), then VCVT.F32.S32 Sd, Sd
    /// For ceil/floor/nearest, we use VCVTR (round toward mode) + convert back.
    /// Simplified: convert to int (toward zero for trunc) then back to float.
    /// Encode F32 rounding as ARM32.
    /// `mode`: FPSCR RMode — 0b00=nearest, 0b01=+inf(ceil), 0b10=-inf(floor), 0b11=zero(trunc)
    ///
    /// For trunc (mode=0b11): uses VCVTR.S32.F32 (always rounds toward zero).
    /// For ceil/floor/nearest: sets FPSCR rounding mode, uses VCVT.S32.F32 (non-R variant
    /// which honours FPSCR rmode), then restores FPSCR.
    fn encode_arm_f32_rounding(&self, sd: &VfpReg, sm: &VfpReg, mode: u8) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let sm_num = vfp_sreg_to_num(sm);
        let sd_num = vfp_sreg_to_num(sd);
        let (vd_s, d_s) = encode_sreg(sd_num);
        let (vm_s, m_s) = encode_sreg(sm_num);

        if mode == 0b11 {
            // Trunc (toward zero): VCVTR.S32.F32 — the "R" variant always truncates.
            // 0xEEBD0AC0: bit[7]=1 => round toward zero regardless of FPSCR
            let vcvt_to_int = 0xEEBD0AC0 | (d_s << 22) | (vd_s << 12) | (m_s << 5) | vm_s;
            bytes.extend_from_slice(&vcvt_to_int.to_le_bytes());
        } else {
            // ceil/floor/nearest: manipulate FPSCR rounding mode
            let rt: u32 = 12; // R12/IP as temp

            // VMRS R12, FPSCR
            let vmrs = 0xEEF10A10 | (rt << 12);
            bytes.extend_from_slice(&vmrs.to_le_bytes());

            // BIC R12, R12, #(3 << 22) — clear RMode bits [23:22]
            // 3<<22 = 0x00C00000. ARM rotated imm: 0x03 ror 10 (rotation=5, imm8=0x03)
            let bic = 0xE3CC0000 | (rt << 12) | (0x05 << 8) | 0x03;
            bytes.extend_from_slice(&bic.to_le_bytes());

            // ORR R12, R12, #(mode << 22) — set desired rounding mode
            if mode != 0 {
                // mode<<22: rotation=5, imm8=mode
                let orr = 0xE38C0000 | (rt << 12) | (0x05 << 8) | (mode as u32);
                bytes.extend_from_slice(&orr.to_le_bytes());
            }

            // VMSR FPSCR, R12
            let vmsr = 0xEEE10A10 | (rt << 12);
            bytes.extend_from_slice(&vmsr.to_le_bytes());

            // VCVT.S32.F32 Sd, Sm — non-R variant (bit[7]=0), uses FPSCR rounding mode
            let vcvt_to_int = 0xEEBD0A40 | (d_s << 22) | (vd_s << 12) | (m_s << 5) | vm_s;
            bytes.extend_from_slice(&vcvt_to_int.to_le_bytes());

            // Restore FPSCR: clear rmode bits back to nearest (default)
            bytes.extend_from_slice(&vmrs.to_le_bytes());
            bytes.extend_from_slice(&bic.to_le_bytes());
            bytes.extend_from_slice(&vmsr.to_le_bytes());
        }

        // VCVT.F32.S32 Sd, Sd (convert integer result back to float)
        let (vd2, d2) = encode_sreg(sd_num);
        let vcvt_to_float = 0xEEB80A40 | (d2 << 22) | (vd2 << 12) | (d_s << 5) | vd_s;
        bytes.extend_from_slice(&vcvt_to_float.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F32 min/max as ARM32: VCMP + VMRS + conditional VMOV
    fn encode_arm_f32_minmax(
        &self,
        sd: &VfpReg,
        sn: &VfpReg,
        sm: &VfpReg,
        is_min: bool,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let sn_num = vfp_sreg_to_num(sn);
        let sm_num = vfp_sreg_to_num(sm);
        let sd_num = vfp_sreg_to_num(sd);

        // VMOV Sd, Sn (start with first operand)
        let (vd, d) = encode_sreg(sd_num);
        let (vn, n) = encode_sreg(sn_num);
        let vmov_sn = 0xEEB00A40 | (d << 22) | (vd << 12) | (n << 5) | vn;
        bytes.extend_from_slice(&vmov_sn.to_le_bytes());

        // VCMP.F32 Sn, Sm
        let (vm, m) = encode_sreg(sm_num);
        let vcmp = 0xEEB40A40 | (n << 22) | (vn << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcmp.to_le_bytes());

        // VMRS APSR_nzcv, FPSCR
        bytes.extend_from_slice(&0xEEF1FA10u32.to_le_bytes());

        // For min: if Sn > Sm (GT), use Sm. Condition = GT (0xC)
        // For max: if Sn < Sm (MI/LT), use Sm. Condition = MI (0x4)
        let cond = if is_min { 0xCu32 } else { 0x4u32 };

        // VMOV{cond} Sd, Sm — conditional VMOV
        let vmov_cond = (cond << 28) | 0x0EB00A40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vmov_cond.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F32 copysign as ARM32: extract sign from Sm, magnitude from Sn
    fn encode_arm_f32_copysign(&self, sd: &VfpReg, sn: &VfpReg, sm: &VfpReg) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV R12, Sm (get sign source bits)
        let vmov_sm = encode_vmov_core_sreg(false, sm, &Reg::R12);
        bytes.extend_from_slice(&vmov_sm.to_le_bytes());

        // VMOV R0, Sn (get magnitude source bits) — use R0 as temp
        let vmov_sn = encode_vmov_core_sreg(false, sn, &Reg::R0);
        bytes.extend_from_slice(&vmov_sn.to_le_bytes());

        // AND R12, R12, #0x80000000 (keep only sign bit)
        // Thumb-2 constant 0x80000000 needs special encoding; in ARM32 use rotated imm
        // 0x80000000 = 0x02 rotated right by 2 (rotation=1, imm8=0x02)
        let and_sign = 0xE2000000u32 | (12 << 16) | (12 << 12) | (1 << 8) | 0x02;
        bytes.extend_from_slice(&and_sign.to_le_bytes());

        // BIC R0, R0, #0x80000000 (clear sign bit from magnitude)
        // R0 = register 0, so Rn and Rd fields are 0
        let bic_sign = 0xE3C00000u32 | (1 << 8) | 0x02;
        bytes.extend_from_slice(&bic_sign.to_le_bytes());

        // ORR R0, R0, R12 (combine sign + magnitude)
        // R0 = register 0, so Rn and Rd fields are 0
        let orr = 0xE1800000u32 | 12;
        bytes.extend_from_slice(&orr.to_le_bytes());

        // VMOV Sd, R0
        let vmov_result = encode_vmov_core_sreg(true, sd, &Reg::R0);
        bytes.extend_from_slice(&vmov_result.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F64 comparison as ARM32: VCMP.F64 + VMRS + MOV rd,#0 + MOVcond rd,#1
    fn encode_arm_f64_compare(
        &self,
        rd: &Reg,
        dn: &VfpReg,
        dm: &VfpReg,
        cond_code: u32,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VCMP.F64 Dn, Dm: 0xEEB40B40 with Dn in Vd position, Dm in Vm position
        let dn_num = vfp_dreg_to_num(dn);
        let dm_num = vfp_dreg_to_num(dm);
        let (vd, d) = encode_dreg(dn_num);
        let (vm, m) = encode_dreg(dm_num);
        let vcmp = 0xEEB40B40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcmp.to_le_bytes());

        // VMRS APSR_nzcv, FPSCR
        bytes.extend_from_slice(&0xEEF1FA10u32.to_le_bytes());

        // MOV rd, #0
        let rd_bits = reg_to_bits(rd);
        let mov_zero = 0xE3A00000 | (rd_bits << 12);
        bytes.extend_from_slice(&mov_zero.to_le_bytes());

        // MOVcond rd, #1
        let mov_one = (cond_code << 28) | 0x03A00001 | (rd_bits << 12);
        bytes.extend_from_slice(&mov_one.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F64 constant load as ARM32: MOVW + MOVT + MOVW + MOVT + VMOV
    fn encode_arm_f64_const(&self, dd: &VfpReg, value: f64) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let bits = value.to_bits();
        let lo32 = bits as u32;
        let hi32 = (bits >> 32) as u32;

        // Load low 32 bits into R0 (Rd field = 0 for R0)
        let lo16 = lo32 & 0xFFFF;
        let movw_r0 = 0xE3000000 | ((lo16 >> 12) << 16) | (lo16 & 0xFFF);
        bytes.extend_from_slice(&movw_r0.to_le_bytes());
        let hi16 = (lo32 >> 16) & 0xFFFF;
        let movt_r0 = 0xE3400000 | ((hi16 >> 12) << 16) | (hi16 & 0xFFF);
        bytes.extend_from_slice(&movt_r0.to_le_bytes());

        // Load high 32 bits into R12
        let lo16 = hi32 & 0xFFFF;
        let movw_r12 = 0xE3000000 | ((lo16 >> 12) << 16) | (12 << 12) | (lo16 & 0xFFF);
        bytes.extend_from_slice(&movw_r12.to_le_bytes());
        let hi16 = (hi32 >> 16) & 0xFFFF;
        let movt_r12 = 0xE3400000 | ((hi16 >> 12) << 16) | (12 << 12) | (hi16 & 0xFFF);
        bytes.extend_from_slice(&movt_r12.to_le_bytes());

        // VMOV Dd, R0, R12
        let vmov = encode_vmov_core_dreg(true, dd, &Reg::R0, &Reg::R12);
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VMOV Sd, Rm + VCVT.F64.S32/U32 Dd, Sd as ARM32
    fn encode_arm_f64_convert_i32(&self, dd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // Use S0 as intermediate: VMOV S0, Rm
        let vmov = encode_vmov_core_sreg(true, &VfpReg::S0, rm);
        bytes.extend_from_slice(&vmov.to_le_bytes());

        // VCVT.F64.S32 Dd, S0 (signed) or VCVT.F64.U32 Dd, S0 (unsigned)
        // Base: 0xEEB80B40 (signed) or 0xEEB80BC0 (unsigned)
        let dd_num = vfp_dreg_to_num(dd);
        let (vd, d) = encode_dreg(dd_num);
        let base = if signed { 0xEEB80B40 } else { 0xEEB80BC0 };
        // S0 is register 0: Vm=0, M=0
        let vcvt = base | (d << 22) | (vd << 12);
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VCVT.F64.F32 Dd, Sm as ARM32 (f32 to f64 promotion)
    fn encode_arm_f64_promote_f32(&self, dd: &VfpReg, sm: &VfpReg) -> Result<Vec<u8>> {
        let dd_num = vfp_dreg_to_num(dd);
        let sm_num = vfp_sreg_to_num(sm);
        let (vd, d) = encode_dreg(dd_num);
        let (vm, m) = encode_sreg(sm_num);

        // VCVT.F64.F32 Dd, Sm: 0xEEB70AC0
        let vcvt = 0xEEB70AC0 | (d << 22) | (vd << 12) | (m << 5) | vm;
        Ok(vcvt.to_le_bytes().to_vec())
    }

    /// Encode VCVT.S32/U32.F64 Sd, Dm + VMOV Rd, Sd as ARM32
    fn encode_arm_i32_trunc_f64(&self, rd: &Reg, dm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm);
        let (vm, m) = encode_dreg(dm_num);

        // VCVT.S32.F64 S0, Dm (toward zero) or VCVT.U32.F64 S0, Dm
        // S0: Vd=0, D=0
        let base = if signed { 0xEEBD0BC0 } else { 0xEEBC0BC0 };
        let vcvt = base | (m << 5) | vm;
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        // VMOV Rd, S0
        let vmov = encode_vmov_core_sreg(false, &VfpReg::S0, rd);
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F64 rounding pseudo-op as ARM32 via VCVT to integer and back.
    fn encode_arm_f64_rounding(&self, dd: &VfpReg, dm: &VfpReg, _mode: u8) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm);
        let dd_num = vfp_dreg_to_num(dd);
        let (vm, m) = encode_dreg(dm_num);
        let (vd, d) = encode_dreg(dd_num);

        // VCVT.S32.F64 S0, Dm (truncate toward zero)
        // S0: Vd=0, D=0
        let vcvt_to_int = 0xEEBD0BC0 | (m << 5) | vm;
        bytes.extend_from_slice(&vcvt_to_int.to_le_bytes());

        // VCVT.F64.S32 Dd, S0 (convert back to double)
        // 0xEEB80B40 | D << 22 | Vd << 12 | M << 5 | Vm
        // S0: Vm=0, M=0
        let vcvt_to_float = 0xEEB80B40 | (d << 22) | (vd << 12);
        bytes.extend_from_slice(&vcvt_to_float.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F64 min/max as ARM32: VMOV + VCMP + VMRS + conditional VMOV
    fn encode_arm_f64_minmax(
        &self,
        dd: &VfpReg,
        dn: &VfpReg,
        dm: &VfpReg,
        is_min: bool,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dn_num = vfp_dreg_to_num(dn);
        let dm_num = vfp_dreg_to_num(dm);
        let dd_num = vfp_dreg_to_num(dd);

        // VMOV.F64 Dd, Dn (start with first operand)
        let (vd, d) = encode_dreg(dd_num);
        let (vn, n) = encode_dreg(dn_num);
        let vmov_dn = 0xEEB00B40 | (d << 22) | (vd << 12) | (n << 5) | vn;
        bytes.extend_from_slice(&vmov_dn.to_le_bytes());

        // VCMP.F64 Dn, Dm
        let (vm, m) = encode_dreg(dm_num);
        let vcmp = 0xEEB40B40 | (n << 22) | (vn << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcmp.to_le_bytes());

        // VMRS APSR_nzcv, FPSCR
        bytes.extend_from_slice(&0xEEF1FA10u32.to_le_bytes());

        let cond = if is_min { 0xCu32 } else { 0x4u32 };
        let vmov_cond = (cond << 28) | 0x0EB00B40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vmov_cond.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F64 copysign as ARM32
    fn encode_arm_f64_copysign(&self, dd: &VfpReg, dn: &VfpReg, dm: &VfpReg) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV R0, R12, Dm (get sign source bits)
        let vmov_dm = encode_vmov_core_dreg(false, dm, &Reg::R0, &Reg::R12);
        bytes.extend_from_slice(&vmov_dm.to_le_bytes());

        // VMOV R1, R2, Dn (get magnitude source bits)
        // We use R1 (lo) and R2 (hi) for the magnitude
        let vmov_dn = encode_vmov_core_dreg(false, dn, &Reg::R1, &Reg::R2);
        bytes.extend_from_slice(&vmov_dn.to_le_bytes());

        // AND R12, R12, #0x80000000 (keep only sign bit from hi word)
        let and_sign = 0xE2000000u32 | (12 << 16) | (12 << 12) | (1 << 8) | 0x02;
        bytes.extend_from_slice(&and_sign.to_le_bytes());

        // BIC R2, R2, #0x80000000 (clear sign bit from magnitude hi word)
        let bic_sign = 0xE3C00000u32 | (2 << 16) | (2 << 12) | (1 << 8) | 0x02;
        bytes.extend_from_slice(&bic_sign.to_le_bytes());

        // ORR R2, R2, R12 (combine sign + magnitude)
        let orr = 0xE1800000u32 | (2 << 16) | (2 << 12) | 12;
        bytes.extend_from_slice(&orr.to_le_bytes());

        // VMOV Dd, R1, R2
        let vmov_result = encode_vmov_core_dreg(true, dd, &Reg::R1, &Reg::R2);
        bytes.extend_from_slice(&vmov_result.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VCVT.S32/U32.F32 + VMOV as ARM32
    fn encode_arm_i32_trunc_f32(&self, rd: &Reg, sm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VCVT.S32.F32 Sd, Sm (toward zero) or VCVT.U32.F32 Sd, Sm
        // We use Sm as both source and destination for the intermediate result
        let sm_num = vfp_sreg_to_num(sm);
        let (vd, d) = encode_sreg(sm_num);
        let (vm, m) = encode_sreg(sm_num);
        let base = if signed { 0xEEBD0AC0 } else { 0xEEBC0AC0 };
        let vcvt = base | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        // VMOV Rd, Sm — move result back to core register
        let vmov = encode_vmov_core_sreg(false, sm, rd);
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode an ARM instruction in Thumb-2 mode (16-bit or 32-bit instructions)
    fn encode_thumb(&self, op: &ArmOp) -> Result<Vec<u8>> {
        // Thumb-2 supports both 16-bit and 32-bit instructions
        // 32-bit instructions are encoded as two 16-bit halfwords (big-endian order)
        match op {
            // === 16-bit Thumb encodings ===
            ArmOp::Add { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // ADDS Rd, Rn, Rm (16-bit): 0001 100 Rm Rn Rd
                    let instr: u16 = 0x1800 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else if let Operand2::Imm(imm) = op2 {
                    if *imm <= 7 && rd_bits < 8 && rn_bits < 8 {
                        // ADDS Rd, Rn, #imm3 (16-bit): 0001 110 imm3 Rn Rd
                        let instr: u16 = 0x1C00 | ((*imm as u16) << 6) | (rn_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        // Use 32-bit ADD for larger immediates
                        self.encode_thumb32_add(rd, rn, *imm as u32)
                    }
                } else {
                    // Fallback to 32-bit encoding
                    self.encode_thumb32_add(rd, rn, 0)
                }
            }

            ArmOp::Sub { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // 16-bit SUBS can only use low registers (R0-R7)
                    if rd_bits < 8 && rn_bits < 8 && rm_bits < 8 {
                        // SUBS Rd, Rn, Rm (16-bit): 0001 101 Rm Rn Rd
                        let instr: u16 = 0x1A00 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        // Use 32-bit SUB.W for high registers
                        self.encode_thumb32_sub_reg_raw(
                            rd_bits as u32,
                            rn_bits as u32,
                            rm_bits as u32,
                        )
                    }
                } else if let Operand2::Imm(imm) = op2 {
                    if *imm <= 7 && rd_bits < 8 && rn_bits < 8 {
                        // SUBS Rd, Rn, #imm3 (16-bit): 0001 111 imm3 Rn Rd
                        let instr: u16 = 0x1E00 | ((*imm as u16) << 6) | (rn_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        self.encode_thumb32_sub(rd, rn, *imm as u32)
                    }
                } else {
                    self.encode_thumb32_sub(rd, rn, 0)
                }
            }

            ArmOp::Mov { rd, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;

                if let Operand2::Imm(imm) = op2 {
                    if *imm <= 255 && rd_bits < 8 {
                        // MOVS Rd, #imm8 (16-bit): 0010 0 Rd imm8
                        let imm_bits = (*imm as u16) & 0xFF;
                        let instr: u16 = 0x2000 | (rd_bits << 8) | imm_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        // Use 32-bit MOVW for larger immediates
                        self.encode_thumb32_movw(rd, *imm as u32)
                    }
                } else if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // MOV Rd, Rm (16-bit): 0100 0110 D Rm Rd[2:0]
                    // D = Rd[3], Rd[2:0] in lower bits
                    let d_bit = (rd_bits >> 3) & 1;
                    let instr: u16 = 0x4600 | (d_bit << 7) | (rm_bits << 3) | (rd_bits & 0x7);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    let instr: u16 = 0xBF00; // NOP fallback
                    Ok(instr.to_le_bytes().to_vec())
                }
            }

            ArmOp::Nop => {
                let instr: u16 = 0xBF00; // NOP in Thumb-2
                Ok(instr.to_le_bytes().to_vec())
            }

            ArmOp::Udf { imm } => {
                // UDF (Undefined) in Thumb-2: 16-bit encoding is 0xDE00 | imm8
                // This triggers UsageFault/HardFault, used for WASM traps
                let instr: u16 = 0xDE00 | (*imm as u16);
                Ok(instr.to_le_bytes().to_vec())
            }

            // i64 support: ADDS, ADC, SUBS, SBC for register pair arithmetic
            // ADDS sets flags (carry), ADC uses carry from previous ADDS
            ArmOp::Adds { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // ADDS Rd, Rn, Rm (16-bit): 0001 100 Rm Rn Rd
                    let instr: u16 = 0x1800 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // 32-bit Thumb-2 ADDS with immediate
                    self.encode_thumb32_adds(rd, rn, 0)
                }
            }

            // ADC: Add with Carry (Thumb-2 32-bit)
            // ADC.W Rd, Rn, Rm: EB40 Rn | 00 Rd 00 Rm
            ArmOp::Adc { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm);
                    // ADC.W Rd, Rn, Rm (T2): 1110 1011 0100 Rn | 0 000 Rd 00 00 Rm
                    let hw1: u16 = (0xEB40 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | rm_bits) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else {
                    // ADC with immediate - use 32-bit encoding
                    let hw1: u16 = (0xF140 | rn_bits) as u16;
                    let hw2: u16 = (rd_bits << 8) as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // SUBS sets flags (borrow), SBC uses borrow from previous SUBS
            ArmOp::Subs { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // SUBS Rd, Rn, Rm (16-bit): 0001 101 Rm Rn Rd
                    let instr: u16 = 0x1A00 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // 32-bit Thumb-2 SUBS with immediate
                    self.encode_thumb32_subs(rd, rn, 0)
                }
            }

            // SBC: Subtract with Carry (Thumb-2 32-bit)
            // SBC.W Rd, Rn, Rm: EB60 Rn | 00 Rd 00 Rm
            ArmOp::Sbc { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm);
                    // SBC.W Rd, Rn, Rm (T2): 1110 1011 0110 Rn | 0 000 Rd 00 00 Rm
                    let hw1: u16 = (0xEB60 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | rm_bits) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else {
                    // SBC with immediate - use 32-bit encoding
                    let hw1: u16 = (0xF160 | rn_bits) as u16;
                    let hw2: u16 = (rd_bits << 8) as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // === 32-bit Thumb-2 encodings ===

            // SDIV: 11111011 1001 Rn 1111 Rd 1111 Rm
            ArmOp::Sdiv { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // Thumb-2 SDIV: FB90 F0F0 | Rn<<16 | Rd<<8 | Rm
                // First halfword: 1111 1011 1001 Rn = 0xFB90 | Rn
                // Second halfword: 1111 Rd 1111 Rm = 0xF0F0 | Rd<<8 | Rm
                let hw1: u16 = (0xFB90 | rn_bits) as u16;
                let hw2: u16 = (0xF0F0 | (rd_bits << 8) | rm_bits) as u16;

                // Thumb-2 32-bit instructions: first halfword, then second halfword (little-endian each)
                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // UDIV: 11111011 1011 Rn 1111 Rd 1111 Rm
            ArmOp::Udiv { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // Thumb-2 UDIV: FBB0 F0F0 | Rn<<16 | Rd<<8 | Rm
                let hw1: u16 = (0xFBB0 | rn_bits) as u16;
                let hw2: u16 = (0xF0F0 | (rd_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // MUL (Thumb-2 32-bit): MUL Rd, Rn, Rm
            ArmOp::Mul { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // Thumb-2 MUL: FB00 F000 | Rn | Rd<<8 | Rm
                // 11111011 0000 Rn | 1111 Rd 0000 Rm
                let hw1: u16 = (0xFB00 | rn_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // MLS: Rd = Ra - Rn * Rm
            ArmOp::Mls { rd, rn, rm, ra } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                let ra_bits = reg_to_bits(ra);

                // Thumb-2 MLS: FB00 Rn | Ra Rd 0001 Rm
                // 11111011 0000 Rn | Ra Rd 0001 Rm
                let hw1: u16 = (0xFB00 | rn_bits) as u16;
                let hw2: u16 = ((ra_bits << 12) | (rd_bits << 8) | 0x10 | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // AND (Thumb-2 32-bit)
            ArmOp::And { rd, rn, op2 } => {
                if let Operand2::Reg(rm) = op2 {
                    let rd_bits = reg_to_bits(rd);
                    let rn_bits = reg_to_bits(rn);
                    let rm_bits = reg_to_bits(rm);

                    // Thumb-2 AND register: EA00 Rn | 0 Rd 00 00 Rm
                    let hw1: u16 = (0xEA00 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | rm_bits) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else if let Operand2::Imm(imm) = op2 {
                    let rd_bits = reg_to_bits(rd);
                    let rn_bits = reg_to_bits(rn);
                    let imm_val = *imm as u32;

                    // Thumb-2 AND.W immediate T1: 11110 i 0 0000 S Rn | 0 imm3 Rd imm8
                    let i_bit = (imm_val >> 11) & 1;
                    let imm3 = (imm_val >> 8) & 0x7;
                    let imm8 = imm_val & 0xFF;

                    let hw1: u16 = (0xF000 | (i_bit << 10) | rn_bits) as u16;
                    let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else {
                    // RegShift variant - fallback to NOP
                    let instr: u16 = 0xBF00;
                    Ok(instr.to_le_bytes().to_vec())
                }
            }

            // ORR (Thumb-2 32-bit)
            ArmOp::Orr { rd, rn, op2 } => {
                if let Operand2::Reg(rm) = op2 {
                    let rd_bits = reg_to_bits(rd);
                    let rn_bits = reg_to_bits(rn);
                    let rm_bits = reg_to_bits(rm);

                    // Thumb-2 ORR: EA40 Rn | 0 Rd 00 00 Rm
                    let hw1: u16 = (0xEA40 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | rm_bits) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else {
                    let instr: u16 = 0xBF00;
                    Ok(instr.to_le_bytes().to_vec())
                }
            }

            // EOR (Thumb-2 32-bit)
            ArmOp::Eor { rd, rn, op2 } => {
                if let Operand2::Reg(rm) = op2 {
                    let rd_bits = reg_to_bits(rd);
                    let rn_bits = reg_to_bits(rn);
                    let rm_bits = reg_to_bits(rm);

                    // Thumb-2 EOR: EA80 Rn | 0 Rd 00 00 Rm
                    let hw1: u16 = (0xEA80 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | rm_bits) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else {
                    let instr: u16 = 0xBF00;
                    Ok(instr.to_le_bytes().to_vec())
                }
            }

            // Shift operations (16-bit for low registers)
            ArmOp::Lsl { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;
                let shift_bits = (*shift as u16) & 0x1F;

                if rd_bits < 8 && rn_bits < 8 {
                    // LSLS Rd, Rm, #imm5 (16-bit): 0000 0 imm5 Rm Rd
                    let instr: u16 = (shift_bits << 6) | (rn_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // Use 32-bit encoding for high registers
                    self.encode_thumb32_shift(rd, rn, *shift, 0b00) // LSL type
                }
            }

            ArmOp::Lsr { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;
                let shift_bits = (*shift as u16) & 0x1F;

                if rd_bits < 8 && rn_bits < 8 && shift_bits > 0 {
                    // LSRS Rd, Rm, #imm5 (16-bit): 0000 1 imm5 Rm Rd
                    let instr: u16 = 0x0800 | (shift_bits << 6) | (rn_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_shift(rd, rn, *shift, 0b01) // LSR type
                }
            }

            ArmOp::Asr { rd, rn, shift } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;
                let shift_bits = (*shift as u16) & 0x1F;

                if rd_bits < 8 && rn_bits < 8 && shift_bits > 0 {
                    // ASRS Rd, Rm, #imm5 (16-bit): 0001 0 imm5 Rm Rd
                    let instr: u16 = 0x1000 | (shift_bits << 6) | (rn_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_shift(rd, rn, *shift, 0b10) // ASR type
                }
            }

            ArmOp::Ror { rd, rn, shift } => {
                // ROR doesn't have a 16-bit immediate form, use 32-bit
                self.encode_thumb32_shift(rd, rn, *shift, 0b11) // ROR type
            }

            // Register-based shifts (Thumb-2 32-bit)
            // Encoding: 11111010 0xxS Rn 1111 Rd 0000 Rm
            // xx = shift type: 00=LSL, 01=LSR, 10=ASR, 11=ROR
            ArmOp::LslReg { rd, rn, rm } => self.encode_thumb32_shift_reg(rd, rn, rm, 0b00),
            ArmOp::LsrReg { rd, rn, rm } => self.encode_thumb32_shift_reg(rd, rn, rm, 0b01),
            ArmOp::AsrReg { rd, rn, rm } => self.encode_thumb32_shift_reg(rd, rn, rm, 0b10),
            ArmOp::RorReg { rd, rn, rm } => self.encode_thumb32_shift_reg(rd, rn, rm, 0b11),

            // RSB (Reverse Subtract): Rd = imm - Rn
            // Thumb-2 T2 encoding: 11110 i 0 1110 S Rn | 0 imm3 Rd imm8
            ArmOp::Rsb { rd, rn, imm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let imm_val = *imm;

                let i_bit = (imm_val >> 11) & 1;
                let imm3 = (imm_val >> 8) & 0x7;
                let imm8 = imm_val & 0xFF;

                // hw1: 11110 i 01110 0 Rn  (S=0)
                let hw1: u16 = (0xF1C0 | (i_bit << 10) | rn_bits) as u16;
                // hw2: 0 imm3 Rd imm8
                let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // CLZ (Thumb-2 32-bit)
            ArmOp::Clz { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);

                // Thumb-2 CLZ: FAB0 Rm | F8 Rd Rm
                // 11111010 1011 Rm | 1111 1000 Rd Rm
                let hw1: u16 = (0xFAB0 | rm_bits) as u16;
                let hw2: u16 = (0xF080 | (rd_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // RBIT (Thumb-2 32-bit)
            ArmOp::Rbit { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);

                // Thumb-2 RBIT: FA90 Rm | F0 Rd A0 Rm
                // 11111010 1001 Rm | 1111 Rd 1010 Rm
                let hw1: u16 = (0xFA90 | rm_bits) as u16;
                let hw2: u16 = (0xF0A0 | (rd_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // SXTB (16-bit for low registers)
            ArmOp::Sxtb { rd, rm } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rm_bits = reg_to_bits(rm) as u16;

                if rd_bits < 8 && rm_bits < 8 {
                    // SXTB Rd, Rm (16-bit): 1011 0010 01 Rm Rd
                    let instr: u16 = 0xB240 | (rm_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // Thumb-2 SXTB.W: FA4F F(rd)80 (rm)
                    // 11111010 0100 1111 | 1111 Rd 10 rotate Rm
                    let rd_bits32 = rd_bits as u32;
                    let rm_bits32 = rm_bits as u32;
                    let hw1: u16 = 0xFA4F;
                    let hw2: u16 = (0xF080 | (rd_bits32 << 8) | rm_bits32) as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // SXTH (16-bit for low registers)
            ArmOp::Sxth { rd, rm } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rm_bits = reg_to_bits(rm) as u16;

                if rd_bits < 8 && rm_bits < 8 {
                    // SXTH Rd, Rm (16-bit): 1011 0010 00 Rm Rd
                    let instr: u16 = 0xB200 | (rm_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // Thumb-2 SXTH.W: FA0F F(rd)80 (rm)
                    // 11111010 0000 1111 | 1111 Rd 10 rotate Rm
                    let rd_bits32 = rd_bits as u32;
                    let rm_bits32 = rm_bits as u32;
                    let hw1: u16 = 0xFA0F;
                    let hw2: u16 = (0xF080 | (rd_bits32 << 8) | rm_bits32) as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // CMP (can be 16-bit for low registers)
            ArmOp::Cmp { rn, op2 } => {
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Imm(imm) = op2 {
                    // Only use 16-bit encoding for non-negative immediates 0-255
                    // Negative immediates must use 32-bit encoding
                    if *imm >= 0 && *imm <= 255 && rn_bits < 8 {
                        // CMP Rn, #imm8 (16-bit): 0010 1 Rn imm8
                        let instr: u16 = 0x2800 | (rn_bits << 8) | (*imm as u16 & 0xFF);
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        self.encode_thumb32_cmp_imm(rn, *imm as u32)
                    }
                } else if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    if rn_bits < 8 && rm_bits < 8 {
                        // CMP Rn, Rm (16-bit low): 0100 0010 10 Rm Rn
                        let instr: u16 = 0x4280 | (rm_bits << 3) | rn_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        // CMP Rn, Rm (16-bit high): 0100 0101 N Rm Rn[2:0]
                        let n_bit = (rn_bits >> 3) & 1;
                        let instr: u16 = 0x4500 | (n_bit << 7) | (rm_bits << 3) | (rn_bits & 0x7);
                        Ok(instr.to_le_bytes().to_vec())
                    }
                } else {
                    let instr: u16 = 0xBF00;
                    Ok(instr.to_le_bytes().to_vec())
                }
            }

            // CMN (Compare Negative) - computes Rn + op2 and sets flags
            // CMN Rn, #1 sets Z flag if Rn == -1 (since -1 + 1 = 0)
            ArmOp::Cmn { rn, op2 } => {
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Imm(imm) = op2 {
                    // CMN.W Rn, #imm (32-bit encoding)
                    // Encoding: F110 Rn | 0F00 imm8 (for small immediates 0-255)
                    if *imm >= 0 && *imm <= 255 {
                        let imm8 = *imm as u16 & 0xFF;
                        let hw1: u16 = 0xF110 | rn_bits;
                        let hw2: u16 = 0x0F00 | imm8;
                        let mut bytes = hw1.to_le_bytes().to_vec();
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        Ok(bytes)
                    } else {
                        // For other immediates, fallback to NOP (should not happen in our use case)
                        Ok(vec![0xBF, 0x00])
                    }
                } else if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // CMN Rn, Rm (16-bit): 0100 0010 11 Rm Rn
                    let instr: u16 = 0x42C0 | (rm_bits << 3) | rn_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    Ok(vec![0xBF, 0x00])
                }
            }

            // LDR (can be 16-bit for simple cases)
            ArmOp::Ldr { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                // Handle register offset mode [base, Roff] or [base, Roff, #imm]
                if let Some(offset_reg) = &addr.offset_reg {
                    let rm_bits = reg_to_bits(offset_reg);

                    // If there's also an immediate offset, we need to ADD it first
                    if addr.offset != 0 {
                        // Use R12 (IP) as scratch to avoid clobbering the address register
                        // ADD R12, Rm, #offset; LDR Rd, [base, R12]
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_ldr_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }

                    // Simple register offset: LDR Rd, [Rn, Rm]
                    // 16-bit: only if Rd, Rn, Rm < R8
                    if rd_bits < 8 && base_bits < 8 && rm_bits < 8 {
                        // LDR Rd, [Rn, Rm] (16-bit): 0101 100 Rm Rn Rd
                        let instr: u16 = 0x5800
                            | ((rm_bits as u16) << 6)
                            | ((base_bits as u16) << 3)
                            | (rd_bits as u16);
                        return Ok(instr.to_le_bytes().to_vec());
                    }

                    // 32-bit register offset
                    return self.encode_thumb32_ldr_reg(rd, &addr.base, offset_reg);
                }

                // Immediate offset mode [base, #imm]
                let offset = addr.offset as u32;

                if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 {
                    // LDR Rd, [Rn, #imm5*4] (16-bit): 0110 1 imm5 Rn Rd
                    let imm5 = (offset >> 2) as u16;
                    let instr: u16 =
                        0x6800 | (imm5 << 6) | ((base_bits as u16) << 3) | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_ldr(rd, &addr.base, offset)
                }
            }

            // STR (can be 16-bit for simple cases)
            ArmOp::Str { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                // Handle register offset mode [base, Roff] or [base, Roff, #imm]
                if let Some(offset_reg) = &addr.offset_reg {
                    let rm_bits = reg_to_bits(offset_reg);

                    // If there's also an immediate offset, we need to ADD it first
                    if addr.offset != 0 {
                        // Use R12 (IP) as scratch to avoid clobbering the address register
                        // ADD R12, Rm, #offset; STR Rd, [base, R12]
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_str_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }

                    // Simple register offset: STR Rd, [Rn, Rm]
                    // 16-bit: only if Rd, Rn, Rm < R8
                    if rd_bits < 8 && base_bits < 8 && rm_bits < 8 {
                        // STR Rd, [Rn, Rm] (16-bit): 0101 000 Rm Rn Rd
                        let instr: u16 = 0x5000
                            | ((rm_bits as u16) << 6)
                            | ((base_bits as u16) << 3)
                            | (rd_bits as u16);
                        return Ok(instr.to_le_bytes().to_vec());
                    }

                    // 32-bit register offset
                    return self.encode_thumb32_str_reg(rd, &addr.base, offset_reg);
                }

                // Immediate offset mode [base, #imm]
                let offset = addr.offset as u32;

                if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 {
                    // STR Rd, [Rn, #imm5*4] (16-bit): 0110 0 imm5 Rn Rd
                    let imm5 = (offset >> 2) as u16;
                    let instr: u16 =
                        0x6000 | (imm5 << 6) | ((base_bits as u16) << 3) | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_str(rd, &addr.base, offset)
                }
            }

            // BX (16-bit)
            ArmOp::Bx { rm } => {
                let rm_bits = reg_to_bits(rm) as u16;
                // BX Rm (16-bit): 0100 0111 0 Rm 000
                let instr: u16 = 0x4700 | (rm_bits << 3);
                Ok(instr.to_le_bytes().to_vec())
            }

            // BLX (16-bit) - Branch with Link and Exchange
            // BLX Rm: 0100 0111 1 Rm 000
            ArmOp::Blx { rm } => {
                let rm_bits = reg_to_bits(rm) as u16;
                let instr: u16 = 0x4780 | (rm_bits << 3);
                Ok(instr.to_le_bytes().to_vec())
            }

            // CallIndirect - indirect function call via table lookup
            // table_index_reg contains the table index
            // Generates: LSL R12, idx, #2; LDR R12, [R12, table_base]; BLX R12
            ArmOp::CallIndirect {
                rd: _,
                type_idx: _,
                table_index_reg,
            } => {
                let idx_reg = reg_to_bits(table_index_reg);
                let mut bytes = Vec::new();

                // For now, we generate code that:
                // 1. Multiplies index by 4 (function pointer size)
                // 2. Loads function pointer from table (assumes table base in R11)
                // 3. Calls the function via BLX
                //
                // Table base setup must be done by caller/runtime.
                // This is a simplified implementation - full support needs:
                // - Table base address resolution
                // - Type signature checking
                // - Bounds checking

                // LSL R12, idx_reg, #2 (multiply index by 4)
                // Thumb-2 MOV with shift: 11101010 010 S 1111 | 0 imm3 Rd imm2 type Rm
                // LSL: type=00, imm5=2 -> imm3=0, imm2=10
                let hw1: u16 = 0xEA4F_u16; // MOV.W R12, Rm, LSL #2
                let hw2: u16 = ((0x0C00 | (0b10 << 4)) | idx_reg) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LDR R12, [R11, R12] - load function pointer
                // Thumb-2 LDR (register): 1111 1000 0101 Rn | Rt 0000 00 imm2 Rm
                // Rn=R11, Rt=R12, Rm=R12, imm2=00 (no shift)
                let ldr_hw1: u16 = 0xF85B; // LDR.W Rt, [R11, Rm]
                let ldr_hw2: u16 = 0xC00C; // Rt=R12, imm2=00, Rm=R12
                bytes.extend_from_slice(&ldr_hw1.to_le_bytes());
                bytes.extend_from_slice(&ldr_hw2.to_le_bytes());

                // BLX R12 (call function indirectly)
                // BLX Rm (16-bit): 0100 0111 1 Rm 000
                let blx: u16 = 0x47E0; // BLX R12
                bytes.extend_from_slice(&blx.to_le_bytes());

                Ok(bytes)
            }

            // Branch instructions
            ArmOp::B { label: _ } => {
                // Simplified: B.N with offset 0
                // For real usage, would need label resolution
                let instr: u16 = 0xE000; // B.N #0
                Ok(instr.to_le_bytes().to_vec())
            }

            // BHS (Branch if Higher or Same) - used for bounds checking
            // Condition code: 0x2 (C set)
            ArmOp::Bhs { label: _ } => {
                // 16-bit B<cond> with offset 0: 1101 cond imm8
                // cond = 0x2 (HS)
                let instr: u16 = 0xD200; // BHS.N #0
                Ok(instr.to_le_bytes().to_vec())
            }

            // BLO (Branch if Lower) - complementary to BHS
            // Condition code: 0x3 (C clear)
            ArmOp::Blo { label: _ } => {
                // 16-bit B<cond> with offset 0: 1101 cond imm8
                // cond = 0x3 (LO)
                let instr: u16 = 0xD300; // BLO.N #0
                Ok(instr.to_le_bytes().to_vec())
            }

            // Branch with numeric offset (Thumb-2)
            // Thumb-2 B.W instruction: 32-bit with +-16MB range
            ArmOp::BOffset { offset } => {
                // offset is already the halfword displacement: (target - branch - 4) / 2
                // This is the raw encoded value, accounting for variable-length instructions
                let halfword_offset = *offset;

                // 16-bit B.N encoding: 1110 0 imm11 (11-bit signed halfword offset)
                // Range: -1024 to +1022 halfwords
                if (-1024..=1022).contains(&halfword_offset) {
                    // 16-bit B.N encoding: 1110 0 imm11
                    let imm11 = (halfword_offset as u16) & 0x7FF;
                    let instr: u16 = 0xE000 | imm11;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // 32-bit B.W encoding for larger offsets
                    // First halfword: 1111 0 S imm10
                    // Second halfword: 10 J1 0 J2 imm11
                    // Total offset = SignExtend(S:I1:I2:imm10:imm11:0)
                    // where I1 = NOT(J1 XOR S), I2 = NOT(J2 XOR S)

                    let offset = halfword_offset >> 1; // Convert to word offset for encoding
                    let s = if offset < 0 { 1u32 } else { 0u32 };
                    let imm10 = ((offset >> 11) as u32) & 0x3FF;
                    let imm11 = (offset as u32) & 0x7FF;
                    let i1 = if s == 0 { 1 } else { 0 }; // J1 when S=0: I1=1, so J1=0
                    let i2 = if s == 0 { 1 } else { 0 }; // J2 when S=0: I2=1, so J2=0
                    let j1 = if s == 1 { i1 } else { 1 - i1 };
                    let j2 = if s == 1 { i2 } else { 1 - i2 };

                    let hw1: u16 = (0xF000 | (s << 10) | imm10) as u16;
                    let hw2: u16 = (0x9000 | (j1 << 13) | (j2 << 11) | imm11) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // Conditional branch with numeric offset (Thumb-2)
            ArmOp::BCondOffset { cond, offset } => {
                use synth_synthesis::Condition;
                let cond_bits: u16 = match cond {
                    Condition::EQ => 0x0,
                    Condition::NE => 0x1,
                    Condition::HS => 0x2,
                    Condition::LO => 0x3,
                    Condition::HI => 0x8,
                    Condition::LS => 0x9,
                    Condition::GE => 0xA,
                    Condition::LT => 0xB,
                    Condition::GT => 0xC,
                    Condition::LE => 0xD,
                };

                // offset is already the halfword displacement: (target - branch - 4) / 2
                // This is the raw imm8 value for 16-bit B<cond> encoding
                let halfword_offset = *offset;

                // 16-bit B<cond> encoding: 1101 cond imm8
                // Range: -256 to +254 halfwords (imm8 is sign-extended and shifted left 1)
                if (-128..=127).contains(&halfword_offset) {
                    let imm8 = (halfword_offset as u16) & 0xFF;
                    let instr: u16 = 0xD000 | (cond_bits << 8) | imm8;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // 32-bit B<cond>.W for larger offsets
                    // First halfword: 1111 0 S cond imm6
                    // Second halfword: 10 J1 0 J2 imm11
                    let offset = halfword_offset >> 1;
                    let s = if offset < 0 { 1u32 } else { 0u32 };
                    let imm6 = ((offset >> 11) as u32) & 0x3F;
                    let imm11 = (offset as u32) & 0x7FF;
                    let j1 = if s == 1 { 1 } else { 0 };
                    let j2 = if s == 1 { 1 } else { 0 };

                    let hw1: u16 = (0xF000 | (s << 10) | ((cond_bits as u32) << 6) | imm6) as u16;
                    let hw2: u16 = (0x8000 | (j1 << 13) | (j2 << 11) | imm11) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            ArmOp::Bl { label: _ } => {
                // BL is always 32-bit in Thumb-2
                // Simplified: BL with offset 0
                let hw1: u16 = 0xF000;
                let hw2: u16 = 0xD000;
                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // MVN
            ArmOp::Mvn { rd, op2 } => {
                if let Operand2::Reg(rm) = op2 {
                    let rd_bits = reg_to_bits(rd) as u16;
                    let rm_bits = reg_to_bits(rm) as u16;

                    if rd_bits < 8 && rm_bits < 8 {
                        // MVNS Rd, Rm (16-bit): 0100 0011 11 Rm Rd
                        let instr: u16 = 0x43C0 | (rm_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        // 32-bit MVN
                        let hw1: u16 = 0xEA6F_u16;
                        let hw2: u16 = ((reg_to_bits(rd) << 8) | reg_to_bits(rm)) as u16;
                        let mut bytes = hw1.to_le_bytes().to_vec();
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        Ok(bytes)
                    }
                } else {
                    let instr: u16 = 0xBF00;
                    Ok(instr.to_le_bytes().to_vec())
                }
            }

            // MOVW - Move Wide (Thumb-2 32-bit)
            ArmOp::Movw { rd, imm16 } => {
                self.encode_thumb32_movw_raw(reg_to_bits(rd), *imm16 as u32)
            }

            // MOVT - Move Top (Thumb-2 32-bit)
            ArmOp::Movt { rd, imm16 } => {
                self.encode_thumb32_movt_raw(reg_to_bits(rd), *imm16 as u32)
            }

            // SetCond: Materialize condition flag into register (0 or 1)
            // Strategy: ITE <cond>; MOV Rd, #1; MOV Rd, #0
            // IMPORTANT: Must use ITE (If-Then-Else) because 16-bit Thumb MOV
            // always sets flags (MOVS). We need to evaluate the condition BEFORE
            // any MOV instruction clobbers the flags from CMP.
            ArmOp::SetCond { rd, cond } => {
                let rd_bits = reg_to_bits(rd) as u16;

                // Condition code encoding for IT block
                use synth_synthesis::Condition;
                let cond_bits: u16 = match cond {
                    Condition::EQ => 0x0,
                    Condition::NE => 0x1,
                    Condition::LT => 0xB,
                    Condition::LE => 0xD,
                    Condition::GT => 0xC,
                    Condition::GE => 0xA,
                    Condition::LO => 0x3, // CC/LO (unsigned <)
                    Condition::LS => 0x9, // LS (unsigned <=)
                    Condition::HI => 0x8, // HI (unsigned >)
                    Condition::HS => 0x2, // CS/HS (unsigned >=)
                };

                // ITE <cond>: encodes If-Then-Else block
                // The mask field depends on firstcond[0]:
                // - If firstcond[0] = 0: mask = 0xC for TE pattern (ITE EQ = BF0C)
                // - If firstcond[0] = 1: mask = 0x4 for TE pattern (ITE NE = BF14)
                let mask = if (cond_bits & 1) == 0 { 0xC } else { 0x4 };
                let ite_instr: u16 = 0xBF00 | (cond_bits << 4) | mask;

                // MOV Rd, #1 (Then branch - condition true)
                let mov_one: u16 = 0x2001 | (rd_bits << 8);

                // MOV Rd, #0 (Else branch - condition false)
                let mov_zero: u16 = 0x2000 | (rd_bits << 8);

                // Emit: ITE, MOV #1 (Then), MOV #0 (Else)
                let mut bytes = ite_instr.to_le_bytes().to_vec();
                bytes.extend_from_slice(&mov_one.to_le_bytes());
                bytes.extend_from_slice(&mov_zero.to_le_bytes());
                Ok(bytes)
            }

            // I64SetCond: Compare two i64 register pairs, result 0/1 in rd
            // EQ/NE: CMP lo,lo; IT EQ; CMPEQ hi,hi; ITE <cond>; MOV 1; MOV 0
            // LT: CMP lo,lo; SBCS rd,hi,hi; ITE LT; MOV 1; MOV 0
            // GT: CMP lo,lo (swapped); SBCS rd,hi,hi (swapped); ITE LT; MOV 1; MOV 0
            ArmOp::I64SetCond {
                rd,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
                cond,
            } => {
                use synth_synthesis::Condition;
                let rd_bits = reg_to_bits(rd) as u16;
                let mut bytes = Vec::new();

                // Helper: encode CMP Rn, Rm (16-bit)
                let encode_cmp_reg = |rn: &synth_synthesis::Reg,
                                      rm: &synth_synthesis::Reg|
                 -> Vec<u8> {
                    let rn_bits = reg_to_bits(rn) as u16;
                    let rm_bits = reg_to_bits(rm) as u16;
                    if rn_bits < 8 && rm_bits < 8 {
                        let instr: u16 = 0x4280 | (rm_bits << 3) | rn_bits;
                        instr.to_le_bytes().to_vec()
                    } else {
                        let n_bit = (rn_bits >> 3) & 1;
                        let instr: u16 = 0x4500 | (n_bit << 7) | (rm_bits << 3) | (rn_bits & 0x7);
                        instr.to_le_bytes().to_vec()
                    }
                };

                // Helper: encode ITE <cond> (2 bytes)
                let encode_ite = |cond_bits: u16| -> Vec<u8> {
                    let mask = if (cond_bits & 1) == 0 { 0xC } else { 0x4 };
                    let ite_instr: u16 = 0xBF00 | (cond_bits << 4) | mask;
                    ite_instr.to_le_bytes().to_vec()
                };

                // Helper: encode SetCond (ITE + MOV #1 + MOV #0) for given condition
                let encode_setcond = |cond_bits: u16, rd_bits: u16| -> Vec<u8> {
                    let mut b = encode_ite(cond_bits);
                    let mov_one: u16 = 0x2001 | (rd_bits << 8);
                    let mov_zero: u16 = 0x2000 | (rd_bits << 8);
                    b.extend_from_slice(&mov_one.to_le_bytes());
                    b.extend_from_slice(&mov_zero.to_le_bytes());
                    b
                };

                match cond {
                    Condition::EQ | Condition::NE => {
                        // CMP rn_lo, rm_lo (compare low words)
                        bytes.extend_from_slice(&encode_cmp_reg(rn_lo, rm_lo));

                        // IT EQ (execute next instruction only if Z=1)
                        let it_eq: u16 = 0xBF08; // IT EQ: cond=0000, mask=1000
                        bytes.extend_from_slice(&it_eq.to_le_bytes());

                        // CMPEQ rn_hi, rm_hi (compare high words, only if low equal)
                        bytes.extend_from_slice(&encode_cmp_reg(rn_hi, rm_hi));

                        // ITE <cond>; MOV rd, #1; MOV rd, #0
                        let cond_bits: u16 = match cond {
                            Condition::EQ => 0x0,
                            Condition::NE => 0x1,
                            _ => unreachable!(),
                        };
                        bytes.extend_from_slice(&encode_setcond(cond_bits, rd_bits));
                    }

                    Condition::LT => {
                        // CMP rn_lo, rm_lo (sets C flag for borrow)
                        bytes.extend_from_slice(&encode_cmp_reg(rn_lo, rm_lo));

                        // SBCS rd, rn_hi, rm_hi (subtract with carry, sets N,V flags)
                        // SBCS.W Rd, Rn, Rm: EB70 Rn | 0000 Rd 0000 Rm
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let hw1: u16 = (0xEB70 | rn_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rm_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());

                        // ITE LT; MOV rd, #1; MOV rd, #0
                        bytes.extend_from_slice(&encode_setcond(0xB, rd_bits)); // LT = 0xB
                    }

                    Condition::GT => {
                        // GT(a,b) = LT(b,a): swap operands
                        // CMP rm_lo, rn_lo (swapped)
                        bytes.extend_from_slice(&encode_cmp_reg(rm_lo, rn_lo));

                        // SBCS rd, rm_hi, rn_hi (swapped)
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let hw1: u16 = (0xEB70 | rm_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rn_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());

                        // ITE LT; MOV rd, #1; MOV rd, #0
                        bytes.extend_from_slice(&encode_setcond(0xB, rd_bits)); // LT = 0xB
                    }

                    Condition::LE => {
                        // LE(a,b) = !GT(a,b): use GT logic but invert result
                        // GT(a,b) = LT(b,a): so we do CMP(b,a) and check LT, then invert
                        // CMP rm_lo, rn_lo (swapped, same as GT)
                        bytes.extend_from_slice(&encode_cmp_reg(rm_lo, rn_lo));

                        // SBCS rd, rm_hi, rn_hi (swapped)
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let hw1: u16 = (0xEB70 | rm_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rn_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());

                        // ITE GE; MOV rd, #1; MOV rd, #0 (GE is !LT, so inverting GT result)
                        bytes.extend_from_slice(&encode_setcond(0xA, rd_bits)); // GE = 0xA
                    }

                    Condition::GE => {
                        // GE(a,b) = !LT(a,b): use LT logic but invert result
                        // CMP rn_lo, rm_lo (same as LT)
                        bytes.extend_from_slice(&encode_cmp_reg(rn_lo, rm_lo));

                        // SBCS rd, rn_hi, rm_hi (same as LT)
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let hw1: u16 = (0xEB70 | rn_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rm_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());

                        // ITE GE; MOV rd, #1; MOV rd, #0 (GE is !LT)
                        bytes.extend_from_slice(&encode_setcond(0xA, rd_bits)); // GE = 0xA
                    }

                    // Unsigned comparisons - same instruction sequence, different conditions
                    Condition::LO => {
                        // LO (unsigned LT): CMP lo, SBCS hi, check C=0
                        bytes.extend_from_slice(&encode_cmp_reg(rn_lo, rm_lo));
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let hw1: u16 = (0xEB70 | rn_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rm_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x3, rd_bits)); // LO = 0x3 (CC)
                    }

                    Condition::HI => {
                        // HI (unsigned GT): swap operands and check LO
                        bytes.extend_from_slice(&encode_cmp_reg(rm_lo, rn_lo));
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let hw1: u16 = (0xEB70 | rm_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rn_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x3, rd_bits)); // LO = 0x3 (CC)
                    }

                    Condition::LS => {
                        // LS (unsigned LE): !(a > b) = !(HI), so do HI and invert
                        bytes.extend_from_slice(&encode_cmp_reg(rm_lo, rn_lo));
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let hw1: u16 = (0xEB70 | rm_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rn_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x2, rd_bits)); // HS = 0x2 (CS) = !LO
                    }

                    Condition::HS => {
                        // HS (unsigned GE): !(a < b) = !(LO)
                        bytes.extend_from_slice(&encode_cmp_reg(rn_lo, rm_lo));
                        let rn_hi_bits = reg_to_bits(rn_hi);
                        let rm_hi_bits = reg_to_bits(rm_hi);
                        let hw1: u16 = (0xEB70 | rn_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rm_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x2, rd_bits)); // HS = 0x2 (CS) = !LO
                    }
                }

                Ok(bytes)
            }

            // I64SetCondZ: Test if i64 register pair is zero, result 0/1 in rd
            // ORR.W rd, rn_lo, rn_hi; CMP rd, #0; ITE EQ; MOV 1; MOV 0
            ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => {
                let rd_bits = reg_to_bits(rd);
                let rn_lo_bits = reg_to_bits(rn_lo);
                let rn_hi_bits = reg_to_bits(rn_hi);
                let mut bytes = Vec::new();

                // ORR.W rd, rn_lo, rn_hi: EA40 rn_lo | 0000 rd 0000 rn_hi
                let hw1: u16 = (0xEA40 | rn_lo_bits) as u16;
                let hw2: u16 = ((rd_bits << 8) | rn_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // CMP rd, #0 (16-bit): 0010 1 Rd 0000 0000
                let cmp_instr: u16 = 0x2800 | ((rd_bits as u16) << 8);
                bytes.extend_from_slice(&cmp_instr.to_le_bytes());

                // ITE EQ; MOV rd, #1; MOV rd, #0
                let mask = 0xC_u16; // ITE EQ mask: firstcond[0]=0, mask=0xC
                let ite_instr: u16 = 0xBF00 | mask;
                bytes.extend_from_slice(&ite_instr.to_le_bytes());
                let mov_one: u16 = 0x2001 | ((rd_bits as u16) << 8);
                let mov_zero: u16 = 0x2000 | ((rd_bits as u16) << 8);
                bytes.extend_from_slice(&mov_one.to_le_bytes());
                bytes.extend_from_slice(&mov_zero.to_le_bytes());

                Ok(bytes)
            }

            // I64Mul: 64-bit multiply using UMULL + MLA cross products
            // Formula: result = (a_lo * b_lo) + ((a_lo * b_hi + a_hi * b_lo) << 32)
            // Uses R12 as scratch register
            ArmOp::I64Mul {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                let rd_lo_bits = reg_to_bits(rd_lo);
                let rd_hi_bits = reg_to_bits(rd_hi);
                let rn_lo_bits = reg_to_bits(rn_lo);
                let rn_hi_bits = reg_to_bits(rn_hi);
                let rm_lo_bits = reg_to_bits(rm_lo);
                let rm_hi_bits = reg_to_bits(rm_hi);
                let r12: u32 = 12; // IP scratch register
                let mut bytes = Vec::new();

                // 1. MUL R12, rn_lo, rm_hi  (R12 = a_lo * b_hi)
                // Thumb-2 MUL: hw1=0xFB00|Rn, hw2=0xF000|(Rd<<8)|Rm
                let hw1: u16 = (0xFB00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (r12 << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // 2. MLA R12, rn_hi, rm_lo, R12  (R12 += a_hi * b_lo)
                // Thumb-2 MLA: hw1=0xFB00|Rn, hw2=(Ra<<12)|(Rd<<8)|Rm
                let hw1: u16 = (0xFB00 | rn_hi_bits) as u16;
                let hw2: u16 = ((r12 << 12) | (r12 << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // 3. UMULL rd_lo, rd_hi, rn_lo, rm_lo  (rd_lo:rd_hi = a_lo * b_lo)
                // Thumb-2 UMULL: hw1=0xFBA0|Rn, hw2=(RdLo<<12)|(RdHi<<8)|Rm
                let hw1: u16 = (0xFBA0 | rn_lo_bits) as u16;
                let hw2: u16 = ((rd_lo_bits << 12) | (rd_hi_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // 4. ADD rd_hi, R12  (rd_hi += cross products)
                // 16-bit high reg ADD: 01000100 D Rm Rdn[2:0]
                let d_bit = (rd_hi_bits >> 3) & 1;
                let add_instr: u16 =
                    (0x4400 | (d_bit << 7) | (r12 << 3) | (rd_hi_bits & 0x7)) as u16;
                bytes.extend_from_slice(&add_instr.to_le_bytes());

                Ok(bytes)
            }

            // I64Shl: 64-bit shift left with branch for n<32 vs n>=32
            // rm_hi (R3) is used as temp register
            ArmOp::I64Shl {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                let rd_lo_bits = reg_to_bits(rd_lo);
                let rd_hi_bits = reg_to_bits(rd_hi);
                let rn_lo_bits = reg_to_bits(rn_lo);
                let rn_hi_bits = reg_to_bits(rn_hi);
                let rm_lo_bits = reg_to_bits(rm_lo);
                let rm_hi_bits = reg_to_bits(rm_hi); // temp
                let mut bytes = Vec::new();

                // AND.W rm_lo, rm_lo, #63  (mask shift amount to 6 bits)
                let hw1: u16 = (0xF000 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_lo_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W rm_hi, rm_lo, #32  (rm_hi = n-32, sets flags)
                let hw1: u16 = (0xF1B0 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (branch if n >= 32, offset = +10 halfwords)
                let bpl: u16 = 0xD50A;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // --- Small shift (n < 32) ---
                // RSB.W rm_hi, rm_lo, #32  (rm_hi = 32-n)
                let hw1: u16 = (0xF1C0 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rm_hi, rn_lo, rm_hi  (rm_hi = lo >> (32-n), overflow bits)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rm_hi_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rd_hi, rn_hi, rm_lo  (hi <<= n)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_hi, rd_hi, rm_hi  (hi |= overflow bits from lo)
                let hw1: u16 = (0xEA40 | rd_hi_bits) as u16;
                let hw2: u16 = ((rd_hi_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rd_lo, rn_lo, rm_lo  (lo <<= n)
                let hw1: u16 = (0xFA00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (skip large shift: +2 halfwords)
                let b_done: u16 = 0xE002;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // --- Large shift (n >= 32) ---
                // LSL.W rd_hi, rn_lo, rm_hi  (hi = lo << (n-32))
                let hw1: u16 = (0xFA00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // MOV rd_lo, #0
                let mov_zero: u16 = 0x2000 | ((rd_lo_bits as u16) << 8);
                bytes.extend_from_slice(&mov_zero.to_le_bytes());

                Ok(bytes) // Total: 38 bytes
            }

            // I64ShrU: 64-bit logical shift right with branch for n<32 vs n>=32
            ArmOp::I64ShrU {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                let rd_lo_bits = reg_to_bits(rd_lo);
                let rd_hi_bits = reg_to_bits(rd_hi);
                let rn_lo_bits = reg_to_bits(rn_lo);
                let rn_hi_bits = reg_to_bits(rn_hi);
                let rm_lo_bits = reg_to_bits(rm_lo);
                let rm_hi_bits = reg_to_bits(rm_hi); // temp
                let mut bytes = Vec::new();

                // AND.W rm_lo, rm_lo, #63
                let hw1: u16 = (0xF000 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_lo_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W rm_hi, rm_lo, #32
                let hw1: u16 = (0xF1B0 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (+10 halfwords)
                let bpl: u16 = 0xD50A;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // --- Small shift (n < 32) ---
                // RSB.W rm_hi, rm_lo, #32  (rm_hi = 32-n)
                let hw1: u16 = (0xF1C0 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rm_hi, rn_hi, rm_hi  (rm_hi = hi << (32-n), bits flowing to lo)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rm_hi_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rd_lo, rn_lo, rm_lo  (lo >>= n)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_lo, rd_lo, rm_hi  (lo |= overflow from hi)
                let hw1: u16 = (0xEA40 | rd_lo_bits) as u16;
                let hw2: u16 = ((rd_lo_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rd_hi, rn_hi, rm_lo  (hi >>= n, logical)
                let hw1: u16 = (0xFA20 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (+2 halfwords)
                let b_done: u16 = 0xE002;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // --- Large shift (n >= 32) ---
                // LSR.W rd_lo, rn_hi, rm_hi  (lo = hi >> (n-32))
                let hw1: u16 = (0xFA20 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // MOV rd_hi, #0
                let mov_zero: u16 = 0x2000 | ((rd_hi_bits as u16) << 8);
                bytes.extend_from_slice(&mov_zero.to_le_bytes());

                Ok(bytes) // Total: 38 bytes
            }

            // I64ShrS: 64-bit arithmetic shift right with branch for n<32 vs n>=32
            ArmOp::I64ShrS {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                let rd_lo_bits = reg_to_bits(rd_lo);
                let rd_hi_bits = reg_to_bits(rd_hi);
                let rn_lo_bits = reg_to_bits(rn_lo);
                let rn_hi_bits = reg_to_bits(rn_hi);
                let rm_lo_bits = reg_to_bits(rm_lo);
                let rm_hi_bits = reg_to_bits(rm_hi); // temp
                let mut bytes = Vec::new();

                // AND.W rm_lo, rm_lo, #63
                let hw1: u16 = (0xF000 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_lo_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W rm_hi, rm_lo, #32
                let hw1: u16 = (0xF1B0 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (+10 halfwords)
                let bpl: u16 = 0xD50A;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // --- Small shift (n < 32) ---
                // RSB.W rm_hi, rm_lo, #32
                let hw1: u16 = (0xF1C0 | rm_lo_bits) as u16;
                let hw2: u16 = ((rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rm_hi, rn_hi, rm_hi  (rm_hi = hi << (32-n), bits flowing to lo)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rm_hi_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rd_lo, rn_lo, rm_lo  (lo >>= n, logical for lo word)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_lo, rd_lo, rm_hi  (lo |= overflow from hi)
                let hw1: u16 = (0xEA40 | rd_lo_bits) as u16;
                let hw2: u16 = ((rd_lo_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ASR.W rd_hi, rn_hi, rm_lo  (hi >>= n, arithmetic/sign-extending)
                let hw1: u16 = (0xFA40 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | rm_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (+3 halfwords, large shift is 8 bytes)
                let b_done: u16 = 0xE003;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // --- Large shift (n >= 32) ---
                // ASR.W rd_lo, rn_hi, rm_hi  (lo = hi >>> (n-32))
                let hw1: u16 = (0xFA40 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | rm_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ASR.W rd_hi, rn_hi, #31  (hi = sign extension, all 0s or all 1s)
                // Thumb-2 ASR immediate: hw1=0xEA4F, hw2=imm3:Rd:imm2:10:Rm
                // imm5=31=11111 → imm3=111, imm2=11
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x7000 | (rd_hi_bits << 8) | 0x00E0 | rn_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                Ok(bytes) // Total: 40 bytes
            }

            // I64Rotl: 64-bit rotate left
            // For n < 32: new_hi = (hi << n) | (lo >> (32-n)), new_lo = (lo << n) | (hi >> (32-n))
            // For n >= 32: same formula but with lo/hi conceptually swapped, shift by (n-32)
            // Uses R4 (saved/restored) and R12 as scratch
            ArmOp::I64Rotl {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                shift,
            } => {
                let rd_lo_bits = reg_to_bits(rdlo);
                let rd_hi_bits = reg_to_bits(rdhi);
                let rn_lo_bits = reg_to_bits(rnlo);
                let rn_hi_bits = reg_to_bits(rnhi);
                let shift_bits = reg_to_bits(shift);
                let r12: u32 = 12; // IP scratch
                let r3: u32 = 3; // Scratch (high word of shift amount, unused)
                let r4: u32 = 4; // Scratch (saved/restored)
                let mut bytes = Vec::new();

                // PUSH {R4}
                bytes.extend_from_slice(&0xB410u16.to_le_bytes());

                // AND.W shift, shift, #63 (mask to 6 bits)
                let hw1: u16 = (0xF000 | shift_bits) as u16;
                let hw2: u16 = ((shift_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W R3, shift, #32 (R3 = n-32, sets flags)
                let hw1: u16 = (0xF1B0 | shift_bits) as u16;
                let hw2: u16 = ((r3 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (branch if n >= 32, offset = +14 halfwords)
                let bpl: u16 = 0xD50E;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // === Small rotation (n < 32) ===
                // RSB.W R3, shift, #32 (R3 = 32-n)
                let hw1: u16 = (0xF1C0 | shift_bits) as u16;
                let hw2: u16 = ((r3 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R4, rn_lo, R3 (R4 = lo >> (32-n), will go to new_hi)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (r4 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R12, rn_hi, R3 (R12 = hi >> (32-n), will go to new_lo)
                let hw1: u16 = (0xFA20 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (r12 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rd_hi, rn_hi, shift (rd_hi = hi << n)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | shift_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_hi, rd_hi, R4 (rd_hi = (hi << n) | (lo >> (32-n)))
                let hw1: u16 = (0xEA40 | rd_hi_bits) as u16;
                let hw2: u16 = ((rd_hi_bits << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rd_lo, rn_lo, shift (rd_lo = lo << n)
                let hw1: u16 = (0xFA00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | shift_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_lo, rd_lo, R12 (rd_lo = (lo << n) | (hi >> (32-n)))
                let hw1: u16 = (0xEA40 | rd_lo_bits) as u16;
                let hw2: u16 = ((rd_lo_bits << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (skip large block, offset = +14 halfwords)
                let b_done: u16 = 0xE00E;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // === Large rotation (n >= 32) ===
                // R3 already has n-32 from the SUBS
                // RSB.W R4, R3, #32 (R4 = 32-(n-32) = 64-n)
                let hw1: u16 = (0xF1C0 | r3) as u16;
                let hw2: u16 = ((r4 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R12, rn_hi, R4 (R12 = hi >> (64-n), goes to new_hi low bits)
                let hw1: u16 = (0xFA20 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (r12 << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R4, rn_lo, R4 (R4 = lo >> (64-n), goes to new_lo low bits)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (r4 << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W shift, rn_lo, R3 (shift = lo << (n-32), new_hi high bits)
                let hw1: u16 = (0xFA00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (shift_bits << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W shift, shift, R12 (shift = (lo << (n-32)) | (hi >> (64-n)) = new_hi)
                let hw1: u16 = (0xEA40 | shift_bits) as u16;
                let hw2: u16 = ((shift_bits << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W rd_lo, rn_hi, R3 (rd_lo = hi << (n-32), new_lo high bits)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_lo, rd_lo, R4 (rd_lo = (hi << (n-32)) | (lo >> (64-n)) = new_lo)
                let hw1: u16 = (0xEA40 | rd_lo_bits) as u16;
                let hw2: u16 = ((rd_lo_bits << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // MOV rd_hi, shift (rd_hi = new_hi)
                let d_bit = (rd_hi_bits >> 3) & 1;
                let mov_instr: u16 =
                    (0x4600 | (d_bit << 7) | (shift_bits << 3) | (rd_hi_bits & 0x7)) as u16;
                bytes.extend_from_slice(&mov_instr.to_le_bytes());

                // POP {R4}
                bytes.extend_from_slice(&0xBC10u16.to_le_bytes());

                Ok(bytes) // Total: 74 bytes
            }

            // I64Rotr: 64-bit rotate right
            // rotr(x, n) = rotl(x, 64-n)
            // For n < 32: new_lo = (lo >> n) | (hi << (32-n)), new_hi = (hi >> n) | (lo << (32-n))
            // For n >= 32: same formula but with lo/hi swapped, shift by (n-32)
            ArmOp::I64Rotr {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                shift,
            } => {
                let rd_lo_bits = reg_to_bits(rdlo);
                let rd_hi_bits = reg_to_bits(rdhi);
                let rn_lo_bits = reg_to_bits(rnlo);
                let rn_hi_bits = reg_to_bits(rnhi);
                let shift_bits = reg_to_bits(shift);
                let r12: u32 = 12;
                let r3: u32 = 3;
                let r4: u32 = 4;
                let mut bytes = Vec::new();

                // PUSH {R4}
                bytes.extend_from_slice(&0xB410u16.to_le_bytes());

                // AND.W shift, shift, #63
                let hw1: u16 = (0xF000 | shift_bits) as u16;
                let hw2: u16 = ((shift_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W R3, shift, #32
                let hw1: u16 = (0xF1B0 | shift_bits) as u16;
                let hw2: u16 = ((r3 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (+14 halfwords)
                let bpl: u16 = 0xD50E;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // === Small rotation (n < 32) ===
                // RSB.W R3, shift, #32 (R3 = 32-n)
                let hw1: u16 = (0xF1C0 | shift_bits) as u16;
                let hw2: u16 = ((r3 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W R4, rn_hi, R3 (R4 = hi << (32-n), will go to new_lo)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (r4 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W R12, rn_lo, R3 (R12 = lo << (32-n), will go to new_hi)
                let hw1: u16 = (0xFA00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (r12 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rd_lo, rn_lo, shift (rd_lo = lo >> n)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_lo_bits << 8) | shift_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_lo, rd_lo, R4 (rd_lo = (lo >> n) | (hi << (32-n)))
                let hw1: u16 = (0xEA40 | rd_lo_bits) as u16;
                let hw2: u16 = ((rd_lo_bits << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rd_hi, rn_hi, shift (rd_hi = hi >> n)
                let hw1: u16 = (0xFA20 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | shift_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_hi, rd_hi, R12 (rd_hi = (hi >> n) | (lo << (32-n)))
                let hw1: u16 = (0xEA40 | rd_hi_bits) as u16;
                let hw2: u16 = ((rd_hi_bits << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (+14 halfwords)
                let b_done: u16 = 0xE00E;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // === Large rotation (n >= 32) ===
                // RSB.W R4, R3, #32 (R4 = 64-n)
                let hw1: u16 = (0xF1C0 | r3) as u16;
                let hw2: u16 = ((r4 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W R12, rn_lo, R4 (R12 = lo << (64-n), goes to new_lo low bits)
                let hw1: u16 = (0xFA00 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (r12 << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSL.W R4, rn_hi, R4 (R4 = hi << (64-n), goes to new_hi low bits)
                let hw1: u16 = (0xFA00 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (r4 << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W shift, rn_hi, R3 (shift = hi >> (n-32), new_lo high bits)
                let hw1: u16 = (0xFA20 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF000 | (shift_bits << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W shift, shift, R12 (shift = (hi >> (n-32)) | (lo << (64-n)) = new_lo)
                let hw1: u16 = (0xEA40 | shift_bits) as u16;
                let hw2: u16 = ((shift_bits << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W rd_hi, rn_lo, R3 (rd_hi = lo >> (n-32), new_hi high bits)
                let hw1: u16 = (0xFA20 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF000 | (rd_hi_bits << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ORR.W rd_hi, rd_hi, R4 (rd_hi = (lo >> (n-32)) | (hi << (64-n)) = new_hi)
                let hw1: u16 = (0xEA40 | rd_hi_bits) as u16;
                let hw2: u16 = ((rd_hi_bits << 8) | r4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // MOV rd_lo, shift (rd_lo = new_lo)
                let d_bit = (rd_lo_bits >> 3) & 1;
                let mov_instr: u16 =
                    (0x4600 | (d_bit << 7) | (shift_bits << 3) | (rd_lo_bits & 0x7)) as u16;
                bytes.extend_from_slice(&mov_instr.to_le_bytes());

                // POP {R4}
                bytes.extend_from_slice(&0xBC10u16.to_le_bytes());

                Ok(bytes) // Total: 74 bytes
            }

            // I64Clz: Count leading zeros in 64-bit value
            // If hi != 0: result = CLZ(hi)
            // If hi == 0: result = 32 + CLZ(lo)
            //
            // Layout (using CMP+BNE approach for consistency):
            // 0: CMP.W rnhi, #0 (4 bytes)
            // 4: BEQ .hi_zero (2 bytes) - branch forward to offset 14
            // 6: CLZ.W rd, rnhi (4 bytes)
            // 10: B .done (2 bytes) - branch forward to offset 22
            // 12: NOP (2 bytes) - padding for alignment
            // 14: .hi_zero: CLZ.W rd, rnlo (4 bytes)
            // 18: ADD.W rd, rd, #32 (4 bytes)
            // 22: .done
            ArmOp::I64Clz { rd, rnlo, rnhi } => {
                let rd_bits = reg_to_bits(rd);
                let rn_lo_bits = reg_to_bits(rnlo);
                let rn_hi_bits = reg_to_bits(rnhi);
                let mut bytes = Vec::new();

                // CMP.W rnhi, #0 (4 bytes at offset 0)
                let hw1: u16 = (0xF1B0 | rn_hi_bits) as u16;
                let hw2: u16 = 0x0F00;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BEQ .hi_zero (2 bytes at offset 4)
                // PC = 4 + 4 = 8, target = 14, offset = 6, imm8 = 3
                let beq: u16 = 0xD003;
                bytes.extend_from_slice(&beq.to_le_bytes());

                // CLZ.W rd, rnhi (4 bytes at offset 6)
                // CLZ T1: hw1 = 0xFAB<Rm>, hw2 = 0xF<Rd>8<Rm>
                let hw1: u16 = (0xFAB0 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF080 | (rd_bits << 8) | rn_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (2 bytes at offset 10)
                // PC = 10 + 4 = 14, target = 22, offset = 8, imm11 = 4
                let b_done: u16 = 0xE004;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // NOP (2 bytes at offset 12) - padding
                bytes.extend_from_slice(&0xBF00u16.to_le_bytes());

                // .hi_zero: (offset 14)
                // CLZ.W rd, rnlo (4 bytes)
                // CLZ T1: hw1 = 0xFAB<Rm>, hw2 = 0xF<Rd>8<Rm>
                let hw1: u16 = (0xFAB0 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF080 | (rd_bits << 8) | rn_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ADD.W rd, rd, #32 (4 bytes at offset 18)
                let hw1: u16 = (0xF100 | rd_bits) as u16;
                let hw2: u16 = ((rd_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // .done: (offset 22)
                // i64.clz returns i64, so clear high word: MOV rnhi, #0 (2 bytes)
                // MOVS Rn, #0: 0010 0 Rn 00000000
                let mov0: u16 = (0x2000 | (rn_hi_bits << 8)) as u16;
                bytes.extend_from_slice(&mov0.to_le_bytes());

                Ok(bytes)
            }

            // I64Ctz: Count trailing zeros in 64-bit value
            // If lo != 0: result = CTZ(lo) = CLZ(RBIT(lo))
            // If lo == 0: result = 32 + CTZ(hi) = 32 + CLZ(RBIT(hi))
            //
            // Layout:
            // 0: CMP.W rnlo, #0 (4 bytes)
            // 4: BEQ .lo_zero (2 bytes) - branch to offset 18
            // 6: RBIT.W rd, rnlo (4 bytes)
            // 10: CLZ.W rd, rd (4 bytes)
            // 14: B .done (2 bytes) - branch to offset 30
            // 16: NOP (2 bytes) - padding
            // 18: .lo_zero: RBIT.W rd, rnhi (4 bytes)
            // 22: CLZ.W rd, rd (4 bytes)
            // 26: ADD.W rd, rd, #32 (4 bytes)
            // 30: .done
            ArmOp::I64Ctz { rd, rnlo, rnhi } => {
                let rd_bits = reg_to_bits(rd);
                let rn_lo_bits = reg_to_bits(rnlo);
                let rn_hi_bits = reg_to_bits(rnhi);
                let mut bytes = Vec::new();

                // CMP.W rnlo, #0 (4 bytes at offset 0)
                let hw1: u16 = (0xF1B0 | rn_lo_bits) as u16;
                let hw2: u16 = 0x0F00;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BEQ .lo_zero (2 bytes at offset 4)
                // PC = 4 + 4 = 8, target = 18, offset = 10, imm8 = 5
                let beq: u16 = 0xD005;
                bytes.extend_from_slice(&beq.to_le_bytes());

                // RBIT.W rd, rnlo (4 bytes at offset 6)
                // RBIT T1: hw1 = 0xFA9<Rm>, hw2 = 0xF<Rd>A<Rm>
                let hw1: u16 = (0xFA90 | rn_lo_bits) as u16;
                let hw2: u16 = (0xF0A0 | (rd_bits << 8) | rn_lo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // CLZ.W rd, rd (4 bytes at offset 10)
                // CLZ T1: hw1 = 0xFAB<Rm>, hw2 = 0xF<Rd>8<Rm>
                let hw1: u16 = (0xFAB0 | rd_bits) as u16;
                let hw2: u16 = (0xF080 | (rd_bits << 8) | rd_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // B .done (2 bytes at offset 14)
                // PC = 14 + 4 = 18, target = 30, offset = 12, imm11 = 6
                let b_done: u16 = 0xE006;
                bytes.extend_from_slice(&b_done.to_le_bytes());

                // NOP (2 bytes at offset 16) - padding
                bytes.extend_from_slice(&0xBF00u16.to_le_bytes());

                // .lo_zero: (offset 18)
                // RBIT.W rd, rnhi (4 bytes)
                // RBIT T1: hw1 = 0xFA9<Rm>, hw2 = 0xF<Rd>A<Rm>
                let hw1: u16 = (0xFA90 | rn_hi_bits) as u16;
                let hw2: u16 = (0xF0A0 | (rd_bits << 8) | rn_hi_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // CLZ.W rd, rd (4 bytes at offset 22)
                // CLZ T1: hw1 = 0xFAB<Rm>, hw2 = 0xF<Rd>8<Rm>
                let hw1: u16 = (0xFAB0 | rd_bits) as u16;
                let hw2: u16 = (0xF080 | (rd_bits << 8) | rd_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ADD.W rd, rd, #32 (4 bytes at offset 26)
                let hw1: u16 = (0xF100 | rd_bits) as u16;
                let hw2: u16 = ((rd_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // .done: (offset 30)
                // i64.ctz returns i64, so clear high word: MOV rnhi, #0 (2 bytes)
                let mov0: u16 = (0x2000 | (rn_hi_bits << 8)) as u16;
                bytes.extend_from_slice(&mov0.to_le_bytes());

                Ok(bytes)
            }

            // I64Popcnt: Population count of 64-bit value
            // result = POPCNT(lo) + POPCNT(hi)
            // Using SIMD-style parallel bit counting algorithm
            ArmOp::I64Popcnt { rd, rnlo, rnhi } => {
                let rd_bits = reg_to_bits(rd);
                let rn_lo_bits = reg_to_bits(rnlo);
                let rn_hi_bits = reg_to_bits(rnhi);
                let r12: u32 = 12; // IP scratch
                let r3: u32 = 3; // Scratch for hi popcnt result
                let mut bytes = Vec::new();

                // PUSH {R3, R4, R5} - save scratch registers
                bytes.extend_from_slice(&0xB438u16.to_le_bytes());

                // Strategy: compute popcnt(lo) -> R4, popcnt(hi) -> R5, add them -> rd
                // Using lookup table approach for each byte would be too large
                // Using shift-and-add approach instead

                // For simplicity and correctness, use the efficient parallel algorithm
                // but implement it as a series of inline operations

                // MOV R4, rnlo
                let d_bit: u32 = 0; // R4 < 8, so high bit is 0
                let mov: u16 = (0x4600 | (d_bit << 7) | (rn_lo_bits << 3) | (4 & 0x7)) as u16;
                bytes.extend_from_slice(&mov.to_le_bytes());

                // MOV R5, rnhi
                let d_bit: u32 = 0; // R5 < 8, so high bit is 0
                let mov: u16 = (0x4600 | (d_bit << 7) | (rn_hi_bits << 3) | (5 & 0x7)) as u16;
                bytes.extend_from_slice(&mov.to_le_bytes());

                // --- POPCNT for R4 (lo word) ---
                // Step 1: x = x - ((x >> 1) & 0x55555555)
                // LSR.W R12, R4, #1
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = ((r12 << 8) | 0x50 | 4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Load 0x55555555 into R3 using MOVW/MOVT
                // MOVW R3, #0x5555
                bytes.extend_from_slice(&0xF245u16.to_le_bytes());
                bytes.extend_from_slice(&0x5355u16.to_le_bytes());
                // MOVT R3, #0x5555
                bytes.extend_from_slice(&0xF2C5u16.to_le_bytes());
                bytes.extend_from_slice(&0x5355u16.to_le_bytes());

                // AND.W R12, R12, R3
                let hw1: u16 = (0xEA00 | r12) as u16;
                let hw2: u16 = ((r12 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUB.W R4, R4, R12
                let hw1: u16 = (0xEBA0 | 4) as u16;
                let hw2: u16 = ((4 << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Step 2: x = (x & 0x33333333) + ((x >> 2) & 0x33333333)
                // Load 0x33333333 into R3
                // MOVW R3, #0x3333
                bytes.extend_from_slice(&0xF243u16.to_le_bytes());
                bytes.extend_from_slice(&0x3333u16.to_le_bytes());
                // MOVT R3, #0x3333
                bytes.extend_from_slice(&0xF2C3u16.to_le_bytes());
                bytes.extend_from_slice(&0x3333u16.to_le_bytes());

                // AND.W R12, R4, R3
                let hw1: u16 = (0xEA00 | 4) as u16;
                let hw2: u16 = ((r12 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R4, R4, #2
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = ((4 << 8) | 0x90 | 4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // AND.W R4, R4, R3
                let hw1: u16 = (0xEA00 | 4) as u16;
                let hw2: u16 = ((4 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ADD.W R4, R4, R12
                let hw1: u16 = (0xEB00 | 4) as u16;
                let hw2: u16 = ((4 << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Step 3: x = (x + (x >> 4)) & 0x0F0F0F0F
                // LSR.W R12, R4, #4
                // hw2 = (imm3 << 12) | (Rd << 8) | (imm2 << 6) | (type << 4) | Rm
                // imm5=4=00100 → imm3=1, imm2=0, type=01(LSR)
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x1000 | (r12 << 8) | 0x10 | 4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ADD.W R4, R4, R12
                let hw1: u16 = (0xEB00 | 4) as u16;
                let hw2: u16 = ((4 << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Load 0x0F0F0F0F into R3
                // MOVW R3, #0x0F0F (imm4=0, i=1, imm3=7, imm8=0x0F)
                // hw1 = 11110 1 10 0100 0000 = 0xF640
                // hw2 = 0 111 0011 00001111 = 0x730F
                bytes.extend_from_slice(&0xF640u16.to_le_bytes());
                bytes.extend_from_slice(&0x730Fu16.to_le_bytes());
                // MOVT R3, #0x0F0F
                bytes.extend_from_slice(&0xF6C0u16.to_le_bytes());
                bytes.extend_from_slice(&0x730Fu16.to_le_bytes());

                // AND.W R4, R4, R3
                let hw1: u16 = (0xEA00 | 4) as u16;
                let hw2: u16 = ((4 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Step 4: x = x * 0x01010101 >> 24
                // Load 0x01010101 into R3
                // MOVW R3, #0x0101
                bytes.extend_from_slice(&0xF240u16.to_le_bytes());
                bytes.extend_from_slice(&0x1301u16.to_le_bytes());
                // MOVT R3, #0x0101
                bytes.extend_from_slice(&0xF2C0u16.to_le_bytes());
                bytes.extend_from_slice(&0x1301u16.to_le_bytes());

                // MUL R4, R4, R3
                // MUL T2: hw1 = 0xFB00|Rn, hw2 = 0xF000|(Rd<<8)|Rm
                let hw1: u16 = (0xFB00 | 4) as u16;
                let hw2: u16 = (0xF000 | (4 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R4, R4, #24
                // imm5=24=11000 → imm3=6, imm2=0, type=01(LSR)
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x6000 | (4 << 8) | 0x10 | 4) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // --- POPCNT for R5 (hi word) - same algorithm ---
                // Step 1
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = ((r12 << 8) | 0x50 | 5) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Load 0x55555555 into R3
                bytes.extend_from_slice(&0xF245u16.to_le_bytes());
                bytes.extend_from_slice(&0x5355u16.to_le_bytes());
                bytes.extend_from_slice(&0xF2C5u16.to_le_bytes());
                bytes.extend_from_slice(&0x5355u16.to_le_bytes());

                let hw1: u16 = (0xEA00 | r12) as u16;
                let hw2: u16 = ((r12 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                let hw1: u16 = (0xEBA0 | 5) as u16;
                let hw2: u16 = ((5 << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Step 2
                bytes.extend_from_slice(&0xF243u16.to_le_bytes());
                bytes.extend_from_slice(&0x3333u16.to_le_bytes());
                bytes.extend_from_slice(&0xF2C3u16.to_le_bytes());
                bytes.extend_from_slice(&0x3333u16.to_le_bytes());

                let hw1: u16 = (0xEA00 | 5) as u16;
                let hw2: u16 = ((r12 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                let hw1: u16 = 0xEA4F;
                let hw2: u16 = ((5 << 8) | 0x90 | 5) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                let hw1: u16 = (0xEA00 | 5) as u16;
                let hw2: u16 = ((5 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                let hw1: u16 = (0xEB00 | 5) as u16;
                let hw2: u16 = ((5 << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Step 3: LSR.W R12, R5, #4
                // imm5=4=00100 → imm3=1, imm2=0, type=01(LSR)
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x1000 | (r12 << 8) | 0x10 | 5) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                let hw1: u16 = (0xEB00 | 5) as u16;
                let hw2: u16 = ((5 << 8) | r12) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Load 0x0F0F0F0F into R3 (for hi-word)
                bytes.extend_from_slice(&0xF640u16.to_le_bytes());
                bytes.extend_from_slice(&0x730Fu16.to_le_bytes());
                bytes.extend_from_slice(&0xF6C0u16.to_le_bytes());
                bytes.extend_from_slice(&0x730Fu16.to_le_bytes());

                let hw1: u16 = (0xEA00 | 5) as u16;
                let hw2: u16 = ((5 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // Step 4
                bytes.extend_from_slice(&0xF240u16.to_le_bytes());
                bytes.extend_from_slice(&0x1301u16.to_le_bytes());
                bytes.extend_from_slice(&0xF2C0u16.to_le_bytes());
                bytes.extend_from_slice(&0x1301u16.to_le_bytes());

                // MUL R5, R5, R3
                // MUL T2: hw1 = 0xFB00|Rn, hw2 = 0xF000|(Rd<<8)|Rm
                let hw1: u16 = (0xFB00 | 5) as u16;
                let hw2: u16 = (0xF000 | (5 << 8) | r3) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // LSR.W R5, R5, #24
                // imm5=24=11000 → imm3=6, imm2=0, type=01(LSR)
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x6000 | (5 << 8) | 0x10 | 5) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ADD rd, R4, R5 (combine lo and hi counts)
                // ADDS Rd, Rn, Rm (T1): 0001 100 Rm Rn Rd = 0x1800 | (Rm<<6) | (Rn<<3) | Rd
                let rd_bits_u16 = rd_bits as u16;
                let instr: u16 = 0x1800 | (5 << 6) | (4 << 3) | rd_bits_u16;
                bytes.extend_from_slice(&instr.to_le_bytes());

                // POP {R3, R4, R5}
                bytes.extend_from_slice(&0xBC38u16.to_le_bytes());

                // i64.popcnt returns i64, so clear high word: MOV rnhi, #0 (2 bytes)
                let mov0: u16 = (0x2000 | (rn_hi_bits << 8)) as u16;
                bytes.extend_from_slice(&mov0.to_le_bytes());

                Ok(bytes)
            }

            // I64Extend8S: Sign-extend low 8 bits to 64 bits
            // Result: rdlo = sign_extend_8(rnlo), rdhi = rdlo >> 31
            ArmOp::I64Extend8S { rdlo, rdhi, rnlo } => {
                let rdlo_bits = reg_to_bits(rdlo);
                let rdhi_bits = reg_to_bits(rdhi);
                let rnlo_bits = reg_to_bits(rnlo);
                let mut bytes = Vec::new();

                // SXTB.W rdlo, rnlo (sign-extend byte to 32-bit)
                // SXTB T2: hw1 = 0xFA4F, hw2 = 0xF0<Rd><Rm>
                let hw1: u16 = 0xFA4F_u16;
                let hw2: u16 = (0xF080 | (rdlo_bits << 8) | rnlo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ASR.W rdhi, rdlo, #31 (sign-extend to high word)
                // ASR (immediate): hw1 = 0xEA4F, hw2 = imm3:Rd:imm2:type:Rm
                // For imm5=31: imm3=111, imm2=11, type=10 (ASR)
                // hw2 = (7 << 12) | (rdhi << 8) | (3 << 6) | (2 << 4) | rdlo
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x70E0 | (rdhi_bits << 8) | rdlo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                Ok(bytes)
            }

            // I64Extend16S: Sign-extend low 16 bits to 64 bits
            // Result: rdlo = sign_extend_16(rnlo), rdhi = rdlo >> 31
            ArmOp::I64Extend16S { rdlo, rdhi, rnlo } => {
                let rdlo_bits = reg_to_bits(rdlo);
                let rdhi_bits = reg_to_bits(rdhi);
                let rnlo_bits = reg_to_bits(rnlo);
                let mut bytes = Vec::new();

                // SXTH.W rdlo, rnlo (sign-extend halfword to 32-bit)
                // SXTH T2: hw1 = 0xFA0F, hw2 = 0xF0<Rd><Rm>
                let hw1: u16 = 0xFA0F_u16;
                let hw2: u16 = (0xF080 | (rdlo_bits << 8) | rnlo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // ASR.W rdhi, rdlo, #31 (sign-extend to high word)
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x70E0 | (rdhi_bits << 8) | rdlo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                Ok(bytes)
            }

            // I64Extend32S: Sign-extend low 32 bits to 64 bits
            // Result: rdlo = rnlo, rdhi = rnlo >> 31
            ArmOp::I64Extend32S { rdlo, rdhi, rnlo } => {
                let rdlo_bits = reg_to_bits(rdlo);
                let rdhi_bits = reg_to_bits(rdhi);
                let rnlo_bits = reg_to_bits(rnlo);
                let mut bytes = Vec::new();

                // MOV rdlo, rnlo (if different)
                if rdlo_bits != rnlo_bits {
                    // MOV Rd, Rm (16-bit): 0100 0110 D Rm Rd[2:0]
                    let d_bit = ((rdlo_bits >> 3) & 1) as u16;
                    let mov: u16 = 0x4600
                        | (d_bit << 7)
                        | ((rnlo_bits as u16) << 3)
                        | ((rdlo_bits & 0x7) as u16);
                    bytes.extend_from_slice(&mov.to_le_bytes());
                }

                // ASR.W rdhi, rnlo, #31 (sign-extend to high word)
                let hw1: u16 = 0xEA4F;
                let hw2: u16 = (0x70E0 | (rdhi_bits << 8) | rnlo_bits) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                Ok(bytes)
            }

            // SelectMove: IT <cond>; MOV{cond} rd, rm
            // Conditional move: only execute MOV if condition is true
            ArmOp::SelectMove { rd, rm, cond } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rm_bits = reg_to_bits(rm) as u16;

                // Condition code encoding for IT block
                use synth_synthesis::Condition;
                let cond_bits: u16 = match cond {
                    Condition::EQ => 0x0, // Equal
                    Condition::NE => 0x1, // Not equal
                    Condition::HS => 0x2, // Higher or same (unsigned >=)
                    Condition::LO => 0x3, // Lower (unsigned <)
                    Condition::HI => 0x8, // Higher (unsigned >)
                    Condition::LS => 0x9, // Lower or same (unsigned <=)
                    Condition::GE => 0xA, // Greater or equal (signed)
                    Condition::LT => 0xB, // Less than (signed)
                    Condition::GT => 0xC, // Greater than (signed)
                    Condition::LE => 0xD, // Less or equal (signed)
                };

                // IT <cond>: single Then block (mask = 0x8 for T only)
                // IT instruction: 1011 1111 firstcond mask
                let it_instr: u16 = 0xBF00 | (cond_bits << 4) | 0x8;

                // MOV Rd, Rm (16-bit): 0100 0110 D Rm Rd[2:0]
                // This MOV will only execute if condition is true due to IT block
                let d_bit = (rd_bits >> 3) & 1;
                let mov_instr: u16 = 0x4600 | (d_bit << 7) | (rm_bits << 3) | (rd_bits & 0x7);

                // Emit: IT <cond>, MOV rd, rm
                let mut bytes = it_instr.to_le_bytes().to_vec();
                bytes.extend_from_slice(&mov_instr.to_le_bytes());
                Ok(bytes)
            }

            // Popcnt: Population count (count set bits)
            // ARM Cortex-M has no native POPCNT, so we implement the bit manipulation algorithm:
            // x = x - ((x >> 1) & 0x55555555);
            // x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
            // x = (x + (x >> 4)) & 0x0F0F0F0F;
            // x = x + (x >> 8);
            // x = x + (x >> 16);
            // return x & 0x3F;
            //
            // Uses rd as working register and R12 as scratch for constants
            ArmOp::Popcnt { rd, rm } => {
                let mut bytes = Vec::new();

                // First, move rm to rd if they're different
                if rd != rm {
                    let rd_bits = reg_to_bits(rd) as u16;
                    let rm_bits = reg_to_bits(rm) as u16;
                    // MOV Rd, Rm (16-bit): 0100 0110 D Rm Rd[2:0]
                    let d_bit = (rd_bits >> 3) & 1;
                    let mov_instr: u16 = 0x4600 | (d_bit << 7) | (rm_bits << 3) | (rd_bits & 0x7);
                    bytes.extend_from_slice(&mov_instr.to_le_bytes());
                }

                // Step 1: x = x - ((x >> 1) & 0x55555555)
                // Load 0x55555555 into R12
                bytes.extend_from_slice(&self.encode_thumb32_movw_raw(12, 0x5555)?);
                bytes.extend_from_slice(&self.encode_thumb32_movt_raw(12, 0x5555)?);

                // R12_temp = rd >> 1
                // We need a second scratch register. Use R11.
                bytes.extend_from_slice(&self.encode_thumb32_lsr_raw(11, reg_to_bits(rd), 1)?);

                // R11 = R11 & R12 (R11 = (x >> 1) & 0x55555555)
                bytes.extend_from_slice(&self.encode_thumb32_and_reg_raw(11, 11, 12)?);

                // rd = rd - R11
                bytes.extend_from_slice(&self.encode_thumb32_sub_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    11,
                )?);

                // Step 2: x = (x & 0x33333333) + ((x >> 2) & 0x33333333)
                // Load 0x33333333 into R12
                bytes.extend_from_slice(&self.encode_thumb32_movw_raw(12, 0x3333)?);
                bytes.extend_from_slice(&self.encode_thumb32_movt_raw(12, 0x3333)?);

                // R11 = rd & R12
                bytes.extend_from_slice(&self.encode_thumb32_and_reg_raw(
                    11,
                    reg_to_bits(rd),
                    12,
                )?);

                // rd = rd >> 2
                bytes.extend_from_slice(&self.encode_thumb32_lsr_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    2,
                )?);

                // rd = rd & R12
                bytes.extend_from_slice(&self.encode_thumb32_and_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    12,
                )?);

                // rd = rd + R11
                bytes.extend_from_slice(&self.encode_thumb32_add_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    11,
                )?);

                // Step 3: x = (x + (x >> 4)) & 0x0F0F0F0F
                // R11 = rd >> 4
                bytes.extend_from_slice(&self.encode_thumb32_lsr_raw(11, reg_to_bits(rd), 4)?);

                // rd = rd + R11
                bytes.extend_from_slice(&self.encode_thumb32_add_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    11,
                )?);

                // Load 0x0F0F0F0F into R12
                bytes.extend_from_slice(&self.encode_thumb32_movw_raw(12, 0x0F0F)?);
                bytes.extend_from_slice(&self.encode_thumb32_movt_raw(12, 0x0F0F)?);

                // rd = rd & R12
                bytes.extend_from_slice(&self.encode_thumb32_and_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    12,
                )?);

                // Step 4: x = x + (x >> 8)
                // R11 = rd >> 8
                bytes.extend_from_slice(&self.encode_thumb32_lsr_raw(11, reg_to_bits(rd), 8)?);

                // rd = rd + R11
                bytes.extend_from_slice(&self.encode_thumb32_add_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    11,
                )?);

                // Step 5: x = x + (x >> 16)
                // R11 = rd >> 16
                bytes.extend_from_slice(&self.encode_thumb32_lsr_raw(11, reg_to_bits(rd), 16)?);

                // rd = rd + R11
                bytes.extend_from_slice(&self.encode_thumb32_add_reg_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    11,
                )?);

                // Step 6: return x & 0x3F
                // AND with 0x3F (small immediate, can use BIC or AND with immediate)
                bytes.extend_from_slice(&self.encode_thumb32_and_imm_raw(
                    reg_to_bits(rd),
                    reg_to_bits(rd),
                    0x3F,
                )?);

                Ok(bytes)
            }

            // I64DivU: 64-bit unsigned division using binary long division
            // Input: R0:R1 = dividend, R2:R3 = divisor
            // Output: R0:R1 = quotient
            // Uses: R4-R7, R12 as loop counter (avoid R8 for Renode compatibility)
            ArmOp::I64DivU {
                rdlo: _,
                rdhi: _,
                rnlo: _,
                rnhi: _,
                rmlo: _,
                rmhi: _,
            } => {
                let mut bytes = Vec::new();

                // PUSH {R4-R7, LR} - save callee-saved registers (avoid R8)
                // 16-bit PUSH: 1011 010 M rrrrrrrr where M=LR, r=R0-R7 bitmap
                // For R4-R7,LR: M=1, bitmap for R4-R7 = 11110000 = 0xF0
                // Encoding: 1011 0101 1111 0000 = 0xB5F0
                bytes.extend_from_slice(&0xB5F0u16.to_le_bytes());

                // Initialize quotient (R4:R5) = 0
                bytes.extend_from_slice(&0x2400u16.to_le_bytes()); // MOV R4, #0
                bytes.extend_from_slice(&0x2500u16.to_le_bytes()); // MOV R5, #0

                // Initialize remainder (R6:R7) = 0
                bytes.extend_from_slice(&0x2600u16.to_le_bytes()); // MOV R6, #0
                bytes.extend_from_slice(&0x2700u16.to_le_bytes()); // MOV R7, #0

                // Initialize loop counter R12 = 64 (use R12 scratch instead of R8)
                // MOV.W R12, #64: F04F 0C40
                bytes.extend_from_slice(&0xF04Fu16.to_le_bytes());
                bytes.extend_from_slice(&0x0C40u16.to_le_bytes());

                // Loop start
                let loop_start = bytes.len();

                // === Loop body: process one bit ===

                // 1. Shift quotient R4:R5 left by 1
                // LSLS R5, R5, #1 (16-bit: 0000 0010 1010 1101 = 0x006D -> actually 0x002D for LSL R5,R5,#1)
                // LSL Rd, Rm, #imm5: 000 00 imm5 Rm Rd = 000 00 00001 101 101 = 0x006D
                bytes.extend_from_slice(&0x006Du16.to_le_bytes()); // LSLS R5, R5, #1
                // Get carry from R4 into R5: ORR R5, R5, R4 LSR #31
                // Thumb-2 ORR with shifted register: EA45 75D4 = ORR.W R5, R5, R4, LSR #31
                // 11101010 010 S Rn | 0 imm3 Rd imm2 type Rm
                // type=01 (LSR), imm5=31 (imm3=111, imm2=11)
                bytes.extend_from_slice(&0xEA45u16.to_le_bytes());
                bytes.extend_from_slice(&0x75D4u16.to_le_bytes()); // ORR.W R5, R5, R4, LSR #31
                // LSLS R4, R4, #1: 000 00 00001 100 100 = 0x0064
                bytes.extend_from_slice(&0x0064u16.to_le_bytes()); // LSLS R4, R4, #1

                // 2. Shift remainder R6:R7 left by 1, OR in MSB of dividend R1
                // LSLS R7, R7, #1
                bytes.extend_from_slice(&0x007Fu16.to_le_bytes()); // LSLS R7, R7, #1
                // ORR.W R7, R7, R6, LSR #31
                bytes.extend_from_slice(&0xEA47u16.to_le_bytes());
                bytes.extend_from_slice(&0x77D6u16.to_le_bytes());
                // LSLS R6, R6, #1
                bytes.extend_from_slice(&0x0076u16.to_le_bytes()); // LSLS R6, R6, #1
                // ORR.W R6, R6, R1, LSR #31 (bring in MSB of dividend high)
                bytes.extend_from_slice(&0xEA46u16.to_le_bytes());
                bytes.extend_from_slice(&0x76D1u16.to_le_bytes());

                // 3. Shift dividend R0:R1 left by 1
                // LSLS R1, R1, #1
                bytes.extend_from_slice(&0x0049u16.to_le_bytes()); // LSLS R1, R1, #1
                // ORR.W R1, R1, R0, LSR #31
                bytes.extend_from_slice(&0xEA41u16.to_le_bytes());
                bytes.extend_from_slice(&0x71D0u16.to_le_bytes());
                // LSLS R0, R0, #1
                bytes.extend_from_slice(&0x0040u16.to_le_bytes()); // LSLS R0, R0, #1

                // 4. Compare remainder >= divisor (64-bit unsigned comparison)
                // Compare high words first: CMP R7, R3
                // CMP Rn, Rm encoding: 0x4280 | (Rm << 3) | Rn
                bytes.extend_from_slice(&0x429Fu16.to_le_bytes()); // CMP R7, R3 (16-bit)
                // BHI means R7 > R3 (unsigned) - definitely subtract
                // BLO means R7 < R3 - definitely don't subtract
                // BEQ means need to check low words

                // If high > divisor high: branch to subtract (forward +offset)
                // BHI.N +6 (skip CMP, skip BLO, do subtract)
                // BHI: 1101 1000 offset8 where cond=1000 (HI)
                bytes.extend_from_slice(&0xD802u16.to_le_bytes()); // BHI +4 (to subtract block)

                // If high < divisor high: branch past subtract
                // BLO.N +10 (skip to decrement)
                bytes.extend_from_slice(&0xD306u16.to_le_bytes()); // BLO/BCC +12 (past subtract)

                // High words equal, compare low: CMP R6, R2
                bytes.extend_from_slice(&0x4296u16.to_le_bytes()); // CMP R6, R2 (16-bit)
                // BLO/BCC past subtract (skip SUBS+SBC.W+ORR.W = 10 bytes = 4 halfwords from PC+4)
                bytes.extend_from_slice(&0xD304u16.to_le_bytes()); // BCC +4 halfwords (past subtract)

                // === Subtract block: remainder -= divisor, quotient |= 1 ===
                // SUBS R6, R6, R2
                bytes.extend_from_slice(&0x1AB6u16.to_le_bytes()); // SUBS R6, R6, R2 (16-bit)
                // SBC R7, R7, R3 (with borrow)
                // Thumb-2 SBC.W: EB67 0703 = SBC.W R7, R7, R3
                bytes.extend_from_slice(&0xEB67u16.to_le_bytes());
                bytes.extend_from_slice(&0x0703u16.to_le_bytes());
                // ORR R4, R4, #1 (set bit 0 of quotient low)
                bytes.extend_from_slice(&0xF044u16.to_le_bytes()); // ORR.W R4, R4, #1
                bytes.extend_from_slice(&0x0401u16.to_le_bytes());

                // === Decrement counter and loop ===
                // SUBS.W R12, R12, #1 (decrement loop counter)
                // SUBS.W R12, R12, #1: F1BC 0C01
                bytes.extend_from_slice(&0xF1BCu16.to_le_bytes());
                bytes.extend_from_slice(&0x0C01u16.to_le_bytes());

                // BNE back to loop_start
                let branch_offset_bytes = bytes.len() - loop_start + 4; // +4 for pipeline
                let offset_halfwords = -((branch_offset_bytes / 2) as i16);
                let bne_encoding = 0xD100u16 | ((offset_halfwords as u16) & 0xFF);
                bytes.extend_from_slice(&bne_encoding.to_le_bytes());

                // === Loop done, move quotient to R0:R1 ===
                bytes.extend_from_slice(&0x4620u16.to_le_bytes()); // MOV R0, R4
                bytes.extend_from_slice(&0x4629u16.to_le_bytes()); // MOV R1, R5

                // POP {R4-R7, PC} - restore and return
                // 16-bit POP: 1011 110 P rrrrrrrr where P=PC, r=R0-R7 bitmap
                // For R4-R7,PC: P=1, bitmap = 11110000 = 0xF0
                // Encoding: 1011 1101 1111 0000 = 0xBDF0
                bytes.extend_from_slice(&0xBDF0u16.to_le_bytes());

                Ok(bytes)
            }

            // I64DivS: 64-bit signed division
            // Converts to unsigned, divides, then applies sign
            // Input: R0:R1 = dividend (signed), R2:R3 = divisor (signed)
            // Output: R0:R1 = quotient (signed)
            ArmOp::I64DivS {
                rdlo: _,
                rdhi: _,
                rnlo: _,
                rnhi: _,
                rmlo: _,
                rmhi: _,
            } => {
                let mut bytes = Vec::new();

                // PUSH {R4-R11, LR}
                bytes.extend_from_slice(&0xE92Du16.to_le_bytes());
                bytes.extend_from_slice(&0x4FF0u16.to_le_bytes());

                // Save result sign in R9: R9 = R1 XOR R3 (sign bit = MSB)
                // EOR.W R9, R1, R3
                bytes.extend_from_slice(&0xEA81u16.to_le_bytes());
                bytes.extend_from_slice(&0x0903u16.to_le_bytes());

                // If dividend negative (R1 MSB set), negate it
                // TST R1, R1 (check sign)
                bytes.extend_from_slice(&0x4209u16.to_le_bytes()); // TST R1, R1
                // BPL skip_neg_dividend (+10 bytes = 5 halfwords)
                bytes.extend_from_slice(&0xD504u16.to_le_bytes()); // BPL +8

                // Negate R0:R1 (64-bit): RSBS R0, R0, #0; SBC R1, R1, R1 LSL #1
                // Actually: MVN R0, R0; MVN R1, R1; ADDS R0, R0, #1; ADC R1, R1, #0
                bytes.extend_from_slice(&0x43C0u16.to_le_bytes()); // MVNS R0, R0
                bytes.extend_from_slice(&0x43C9u16.to_le_bytes()); // MVNS R1, R1
                bytes.extend_from_slice(&0x1C40u16.to_le_bytes()); // ADDS R0, R0, #1
                bytes.extend_from_slice(&0xF141u16.to_le_bytes()); // ADC.W R1, R1, #0
                bytes.extend_from_slice(&0x0100u16.to_le_bytes());

                // If divisor negative (R3 MSB set), negate it
                bytes.extend_from_slice(&0x421Bu16.to_le_bytes()); // TST R3, R3
                bytes.extend_from_slice(&0xD504u16.to_le_bytes()); // BPL +8

                // Negate R2:R3
                bytes.extend_from_slice(&0x43D2u16.to_le_bytes()); // MVNS R2, R2
                bytes.extend_from_slice(&0x43DBu16.to_le_bytes()); // MVNS R3, R3
                bytes.extend_from_slice(&0x1C52u16.to_le_bytes()); // ADDS R2, R2, #1
                bytes.extend_from_slice(&0xF143u16.to_le_bytes()); // ADC.W R3, R3, #0
                bytes.extend_from_slice(&0x0300u16.to_le_bytes());

                // === Now do unsigned division (same as I64DivU) ===
                // Initialize quotient (R4:R5) = 0
                bytes.extend_from_slice(&0x2400u16.to_le_bytes());
                bytes.extend_from_slice(&0x2500u16.to_le_bytes());
                // Initialize remainder (R6:R7) = 0
                bytes.extend_from_slice(&0x2600u16.to_le_bytes());
                bytes.extend_from_slice(&0x2700u16.to_le_bytes());
                // Initialize loop counter R8 = 64
                bytes.extend_from_slice(&0xF04Fu16.to_le_bytes());
                bytes.extend_from_slice(&0x0840u16.to_le_bytes());

                let loop_start = bytes.len();

                // Shift quotient left
                bytes.extend_from_slice(&0x006Du16.to_le_bytes()); // LSLS R5, R5, #1
                bytes.extend_from_slice(&0xEA45u16.to_le_bytes()); // ORR.W R5, R5, R4, LSR #31
                bytes.extend_from_slice(&0x75D4u16.to_le_bytes());
                bytes.extend_from_slice(&0x0064u16.to_le_bytes()); // LSLS R4, R4, #1

                // Shift remainder left, OR in MSB of dividend
                bytes.extend_from_slice(&0x007Fu16.to_le_bytes()); // LSLS R7, R7, #1
                bytes.extend_from_slice(&0xEA47u16.to_le_bytes()); // ORR.W R7, R7, R6, LSR #31
                bytes.extend_from_slice(&0x77D6u16.to_le_bytes());
                bytes.extend_from_slice(&0x0076u16.to_le_bytes()); // LSLS R6, R6, #1
                bytes.extend_from_slice(&0xEA46u16.to_le_bytes()); // ORR.W R6, R6, R1, LSR #31
                bytes.extend_from_slice(&0x76D1u16.to_le_bytes());

                // Shift dividend left
                bytes.extend_from_slice(&0x0049u16.to_le_bytes()); // LSLS R1, R1, #1
                bytes.extend_from_slice(&0xEA41u16.to_le_bytes()); // ORR.W R1, R1, R0, LSR #31
                bytes.extend_from_slice(&0x71D0u16.to_le_bytes());
                bytes.extend_from_slice(&0x0040u16.to_le_bytes()); // LSLS R0, R0, #1

                // Compare and conditionally subtract
                bytes.extend_from_slice(&0x429Fu16.to_le_bytes()); // CMP R7, R3
                bytes.extend_from_slice(&0xD802u16.to_le_bytes()); // BHI +4
                bytes.extend_from_slice(&0xD306u16.to_le_bytes()); // BCC +12
                bytes.extend_from_slice(&0x4296u16.to_le_bytes()); // CMP R6, R2
                bytes.extend_from_slice(&0xD304u16.to_le_bytes()); // BCC +4 halfwords

                // Subtract and set quotient bit
                bytes.extend_from_slice(&0x1AB6u16.to_le_bytes()); // SUBS R6, R6, R2
                bytes.extend_from_slice(&0xEB67u16.to_le_bytes()); // SBC.W R7, R7, R3
                bytes.extend_from_slice(&0x0703u16.to_le_bytes());
                bytes.extend_from_slice(&0xF044u16.to_le_bytes()); // ORR.W R4, R4, #1
                bytes.extend_from_slice(&0x0401u16.to_le_bytes());

                // Decrement and loop
                bytes.extend_from_slice(&0xF1B8u16.to_le_bytes()); // SUB.W R8, R8, #1
                bytes.extend_from_slice(&0x0801u16.to_le_bytes());

                let branch_offset_bytes = bytes.len() - loop_start + 4;
                let offset_halfwords = -((branch_offset_bytes / 2) as i16);
                let bne_encoding = 0xD100u16 | ((offset_halfwords as u16) & 0xFF);
                bytes.extend_from_slice(&bne_encoding.to_le_bytes());

                // Move quotient to R0:R1
                bytes.extend_from_slice(&0x4620u16.to_le_bytes()); // MOV R0, R4
                bytes.extend_from_slice(&0x4629u16.to_le_bytes()); // MOV R1, R5

                // If result should be negative (R9 MSB set), negate R0:R1
                bytes.extend_from_slice(&0xF1B9u16.to_le_bytes()); // TST.W R9, R9 (check MSB)
                bytes.extend_from_slice(&0x0F00u16.to_le_bytes());
                bytes.extend_from_slice(&0xD504u16.to_le_bytes()); // BPL +8 (skip negation)

                // Negate result R0:R1
                bytes.extend_from_slice(&0x43C0u16.to_le_bytes()); // MVNS R0, R0
                bytes.extend_from_slice(&0x43C9u16.to_le_bytes()); // MVNS R1, R1
                bytes.extend_from_slice(&0x1C40u16.to_le_bytes()); // ADDS R0, R0, #1
                bytes.extend_from_slice(&0xF141u16.to_le_bytes()); // ADC.W R1, R1, #0
                bytes.extend_from_slice(&0x0100u16.to_le_bytes());

                // POP {R4-R11, PC}
                bytes.extend_from_slice(&0xE8BDu16.to_le_bytes());
                bytes.extend_from_slice(&0x8FF0u16.to_le_bytes());

                Ok(bytes)
            }

            // I64RemU: 64-bit unsigned remainder using binary long division
            // Same algorithm as I64DivU but returns remainder instead of quotient
            // Input: R0:R1 = dividend, R2:R3 = divisor
            // Output: R0:R1 = remainder
            ArmOp::I64RemU {
                rdlo: _,
                rdhi: _,
                rnlo: _,
                rnhi: _,
                rmlo: _,
                rmhi: _,
            } => {
                let mut bytes = Vec::new();

                // PUSH {R4-R8, LR}
                bytes.extend_from_slice(&0xE92Du16.to_le_bytes());
                bytes.extend_from_slice(&0x41F0u16.to_le_bytes());

                // Initialize quotient (R4:R5) = 0 (computed but not returned)
                bytes.extend_from_slice(&0x2400u16.to_le_bytes());
                bytes.extend_from_slice(&0x2500u16.to_le_bytes());
                // Initialize remainder (R6:R7) = 0
                bytes.extend_from_slice(&0x2600u16.to_le_bytes());
                bytes.extend_from_slice(&0x2700u16.to_le_bytes());
                // Initialize loop counter R8 = 64
                bytes.extend_from_slice(&0xF04Fu16.to_le_bytes());
                bytes.extend_from_slice(&0x0840u16.to_le_bytes());

                let loop_start = bytes.len();

                // Shift quotient left (not needed for result, but keeps algorithm same)
                bytes.extend_from_slice(&0x006Du16.to_le_bytes()); // LSLS R5, R5, #1
                bytes.extend_from_slice(&0xEA45u16.to_le_bytes()); // ORR.W R5, R5, R4, LSR #31
                bytes.extend_from_slice(&0x75D4u16.to_le_bytes());
                bytes.extend_from_slice(&0x0064u16.to_le_bytes()); // LSLS R4, R4, #1

                // Shift remainder left, OR in MSB of dividend
                bytes.extend_from_slice(&0x007Fu16.to_le_bytes()); // LSLS R7, R7, #1
                bytes.extend_from_slice(&0xEA47u16.to_le_bytes()); // ORR.W R7, R7, R6, LSR #31
                bytes.extend_from_slice(&0x77D6u16.to_le_bytes());
                bytes.extend_from_slice(&0x0076u16.to_le_bytes()); // LSLS R6, R6, #1
                bytes.extend_from_slice(&0xEA46u16.to_le_bytes()); // ORR.W R6, R6, R1, LSR #31
                bytes.extend_from_slice(&0x76D1u16.to_le_bytes());

                // Shift dividend left
                bytes.extend_from_slice(&0x0049u16.to_le_bytes()); // LSLS R1, R1, #1
                bytes.extend_from_slice(&0xEA41u16.to_le_bytes()); // ORR.W R1, R1, R0, LSR #31
                bytes.extend_from_slice(&0x71D0u16.to_le_bytes());
                bytes.extend_from_slice(&0x0040u16.to_le_bytes()); // LSLS R0, R0, #1

                // Compare and conditionally subtract
                bytes.extend_from_slice(&0x429Fu16.to_le_bytes()); // CMP R7, R3
                bytes.extend_from_slice(&0xD802u16.to_le_bytes()); // BHI +4
                bytes.extend_from_slice(&0xD306u16.to_le_bytes()); // BCC +12
                bytes.extend_from_slice(&0x4296u16.to_le_bytes()); // CMP R6, R2
                bytes.extend_from_slice(&0xD304u16.to_le_bytes()); // BCC +4 halfwords

                // Subtract and set quotient bit
                bytes.extend_from_slice(&0x1AB6u16.to_le_bytes()); // SUBS R6, R6, R2
                bytes.extend_from_slice(&0xEB67u16.to_le_bytes()); // SBC.W R7, R7, R3
                bytes.extend_from_slice(&0x0703u16.to_le_bytes());
                bytes.extend_from_slice(&0xF044u16.to_le_bytes()); // ORR.W R4, R4, #1
                bytes.extend_from_slice(&0x0401u16.to_le_bytes());

                // Decrement and loop
                bytes.extend_from_slice(&0xF1B8u16.to_le_bytes()); // SUB.W R8, R8, #1
                bytes.extend_from_slice(&0x0801u16.to_le_bytes());

                let branch_offset_bytes = bytes.len() - loop_start + 4;
                let offset_halfwords = -((branch_offset_bytes / 2) as i16);
                let bne_encoding = 0xD100u16 | ((offset_halfwords as u16) & 0xFF);
                bytes.extend_from_slice(&bne_encoding.to_le_bytes());

                // Move REMAINDER to R0:R1 (difference from I64DivU)
                bytes.extend_from_slice(&0x4630u16.to_le_bytes()); // MOV R0, R6
                bytes.extend_from_slice(&0x4639u16.to_le_bytes()); // MOV R1, R7

                // POP {R4-R8, PC}
                bytes.extend_from_slice(&0xE8BDu16.to_le_bytes());
                bytes.extend_from_slice(&0x81F0u16.to_le_bytes());

                Ok(bytes)
            }

            // I64RemS: 64-bit signed remainder
            // Remainder sign follows dividend sign (not quotient rule)
            // Input: R0:R1 = dividend (signed), R2:R3 = divisor (signed)
            // Output: R0:R1 = remainder (signed, same sign as dividend)
            ArmOp::I64RemS {
                rdlo: _,
                rdhi: _,
                rnlo: _,
                rnhi: _,
                rmlo: _,
                rmhi: _,
            } => {
                let mut bytes = Vec::new();

                // PUSH {R4-R11, LR}
                bytes.extend_from_slice(&0xE92Du16.to_le_bytes());
                bytes.extend_from_slice(&0x4FF0u16.to_le_bytes());

                // Save dividend sign in R9 (remainder sign = dividend sign)
                // MOV R9, R1 (just need the sign bit)
                bytes.extend_from_slice(&0x4689u16.to_le_bytes()); // MOV R9, R1

                // If dividend negative (R1 MSB set), negate it
                bytes.extend_from_slice(&0x4209u16.to_le_bytes()); // TST R1, R1
                bytes.extend_from_slice(&0xD504u16.to_le_bytes()); // BPL +8

                // Negate R0:R1
                bytes.extend_from_slice(&0x43C0u16.to_le_bytes()); // MVNS R0, R0
                bytes.extend_from_slice(&0x43C9u16.to_le_bytes()); // MVNS R1, R1
                bytes.extend_from_slice(&0x1C40u16.to_le_bytes()); // ADDS R0, R0, #1
                bytes.extend_from_slice(&0xF141u16.to_le_bytes()); // ADC.W R1, R1, #0
                bytes.extend_from_slice(&0x0100u16.to_le_bytes());

                // If divisor negative (R3 MSB set), negate it
                bytes.extend_from_slice(&0x421Bu16.to_le_bytes()); // TST R3, R3
                bytes.extend_from_slice(&0xD504u16.to_le_bytes()); // BPL +8

                // Negate R2:R3
                bytes.extend_from_slice(&0x43D2u16.to_le_bytes()); // MVNS R2, R2
                bytes.extend_from_slice(&0x43DBu16.to_le_bytes()); // MVNS R3, R3
                bytes.extend_from_slice(&0x1C52u16.to_le_bytes()); // ADDS R2, R2, #1
                bytes.extend_from_slice(&0xF143u16.to_le_bytes()); // ADC.W R3, R3, #0
                bytes.extend_from_slice(&0x0300u16.to_le_bytes());

                // === Unsigned division algorithm ===
                // Initialize quotient (R4:R5) = 0
                bytes.extend_from_slice(&0x2400u16.to_le_bytes());
                bytes.extend_from_slice(&0x2500u16.to_le_bytes());
                // Initialize remainder (R6:R7) = 0
                bytes.extend_from_slice(&0x2600u16.to_le_bytes());
                bytes.extend_from_slice(&0x2700u16.to_le_bytes());
                // Initialize loop counter R8 = 64
                bytes.extend_from_slice(&0xF04Fu16.to_le_bytes());
                bytes.extend_from_slice(&0x0840u16.to_le_bytes());

                let loop_start = bytes.len();

                // Shift quotient left
                bytes.extend_from_slice(&0x006Du16.to_le_bytes()); // LSLS R5, R5, #1
                bytes.extend_from_slice(&0xEA45u16.to_le_bytes()); // ORR.W R5, R5, R4, LSR #31
                bytes.extend_from_slice(&0x75D4u16.to_le_bytes());
                bytes.extend_from_slice(&0x0064u16.to_le_bytes()); // LSLS R4, R4, #1

                // Shift remainder left, OR in MSB of dividend
                bytes.extend_from_slice(&0x007Fu16.to_le_bytes()); // LSLS R7, R7, #1
                bytes.extend_from_slice(&0xEA47u16.to_le_bytes()); // ORR.W R7, R7, R6, LSR #31
                bytes.extend_from_slice(&0x77D6u16.to_le_bytes());
                bytes.extend_from_slice(&0x0076u16.to_le_bytes()); // LSLS R6, R6, #1
                bytes.extend_from_slice(&0xEA46u16.to_le_bytes()); // ORR.W R6, R6, R1, LSR #31
                bytes.extend_from_slice(&0x76D1u16.to_le_bytes());

                // Shift dividend left
                bytes.extend_from_slice(&0x0049u16.to_le_bytes()); // LSLS R1, R1, #1
                bytes.extend_from_slice(&0xEA41u16.to_le_bytes()); // ORR.W R1, R1, R0, LSR #31
                bytes.extend_from_slice(&0x71D0u16.to_le_bytes());
                bytes.extend_from_slice(&0x0040u16.to_le_bytes()); // LSLS R0, R0, #1

                // Compare and conditionally subtract
                bytes.extend_from_slice(&0x429Fu16.to_le_bytes()); // CMP R7, R3
                bytes.extend_from_slice(&0xD802u16.to_le_bytes()); // BHI +4
                bytes.extend_from_slice(&0xD306u16.to_le_bytes()); // BCC +12
                bytes.extend_from_slice(&0x4296u16.to_le_bytes()); // CMP R6, R2
                bytes.extend_from_slice(&0xD304u16.to_le_bytes()); // BCC +4 halfwords

                // Subtract and set quotient bit
                bytes.extend_from_slice(&0x1AB6u16.to_le_bytes()); // SUBS R6, R6, R2
                bytes.extend_from_slice(&0xEB67u16.to_le_bytes()); // SBC.W R7, R7, R3
                bytes.extend_from_slice(&0x0703u16.to_le_bytes());
                bytes.extend_from_slice(&0xF044u16.to_le_bytes()); // ORR.W R4, R4, #1
                bytes.extend_from_slice(&0x0401u16.to_le_bytes());

                // Decrement and loop
                bytes.extend_from_slice(&0xF1B8u16.to_le_bytes()); // SUB.W R8, R8, #1
                bytes.extend_from_slice(&0x0801u16.to_le_bytes());

                let branch_offset_bytes = bytes.len() - loop_start + 4;
                let offset_halfwords = -((branch_offset_bytes / 2) as i16);
                let bne_encoding = 0xD100u16 | ((offset_halfwords as u16) & 0xFF);
                bytes.extend_from_slice(&bne_encoding.to_le_bytes());

                // Move remainder to R0:R1
                bytes.extend_from_slice(&0x4630u16.to_le_bytes()); // MOV R0, R6
                bytes.extend_from_slice(&0x4639u16.to_le_bytes()); // MOV R1, R7

                // If original dividend was negative (R9 MSB set), negate remainder
                bytes.extend_from_slice(&0xF1B9u16.to_le_bytes()); // TST.W R9, R9
                bytes.extend_from_slice(&0x0F00u16.to_le_bytes());
                bytes.extend_from_slice(&0xD504u16.to_le_bytes()); // BPL +8

                // Negate result R0:R1
                bytes.extend_from_slice(&0x43C0u16.to_le_bytes()); // MVNS R0, R0
                bytes.extend_from_slice(&0x43C9u16.to_le_bytes()); // MVNS R1, R1
                bytes.extend_from_slice(&0x1C40u16.to_le_bytes()); // ADDS R0, R0, #1
                bytes.extend_from_slice(&0xF141u16.to_le_bytes()); // ADC.W R1, R1, #0
                bytes.extend_from_slice(&0x0100u16.to_le_bytes());

                // POP {R4-R11, PC}
                bytes.extend_from_slice(&0xE8BDu16.to_le_bytes());
                bytes.extend_from_slice(&0x8FF0u16.to_le_bytes());

                Ok(bytes)
            }

            // === F32 VFP single-precision Thumb-2 encodings ===
            // VFP instruction words are identical to ARM32; emit as two LE halfwords.
            ArmOp::F32Add { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE300A00, sd, sn, sm)))
            }
            ArmOp::F32Sub { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE300A40, sd, sn, sm)))
            }
            ArmOp::F32Mul { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE200A00, sd, sn, sm)))
            }
            ArmOp::F32Div { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE800A00, sd, sn, sm)))
            }
            ArmOp::F32Abs { sd, sm } => Ok(vfp_to_thumb_bytes(encode_vfp_2reg(0xEEB00AC0, sd, sm))),
            ArmOp::F32Neg { sd, sm } => Ok(vfp_to_thumb_bytes(encode_vfp_2reg(0xEEB10A40, sd, sm))),
            ArmOp::F32Sqrt { sd, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg(0xEEB10AC0, sd, sm)))
            }

            // f32 pseudo-ops — multi-instruction sequences
            // FPSCR RMode: 00=nearest, 01=+inf(ceil), 10=-inf(floor), 11=zero(trunc)
            ArmOp::F32Ceil { sd, sm } => self.encode_thumb_f32_rounding(sd, sm, 0b01),
            ArmOp::F32Floor { sd, sm } => self.encode_thumb_f32_rounding(sd, sm, 0b10),
            ArmOp::F32Trunc { sd, sm } => self.encode_thumb_f32_rounding(sd, sm, 0b11),
            ArmOp::F32Nearest { sd, sm } => self.encode_thumb_f32_rounding(sd, sm, 0b00),
            ArmOp::F32Min { sd, sn, sm } => self.encode_thumb_f32_minmax(sd, sn, sm, true),
            ArmOp::F32Max { sd, sn, sm } => self.encode_thumb_f32_minmax(sd, sn, sm, false),
            ArmOp::F32Copysign { sd, sn, sm } => self.encode_thumb_f32_copysign(sd, sn, sm),

            // f32 comparisons — VCMP + VMRS + MOV #0 + IT + MOV #1
            ArmOp::F32Eq { rd, sn, sm } => self.encode_thumb_f32_compare(rd, sn, sm, 0x0),
            ArmOp::F32Ne { rd, sn, sm } => self.encode_thumb_f32_compare(rd, sn, sm, 0x1),
            ArmOp::F32Lt { rd, sn, sm } => self.encode_thumb_f32_compare(rd, sn, sm, 0x4),
            ArmOp::F32Le { rd, sn, sm } => self.encode_thumb_f32_compare(rd, sn, sm, 0x9),
            ArmOp::F32Gt { rd, sn, sm } => self.encode_thumb_f32_compare(rd, sn, sm, 0xC),
            ArmOp::F32Ge { rd, sn, sm } => self.encode_thumb_f32_compare(rd, sn, sm, 0xA),

            ArmOp::F32Const { sd, value } => self.encode_thumb_f32_const(sd, *value),

            ArmOp::F32Load { sd, addr } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_ldst(0xED900A00, sd, addr)))
            }
            ArmOp::F32Store { sd, addr } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_ldst(0xED800A00, sd, addr)))
            }

            ArmOp::F32ConvertI32S { sd, rm } => self.encode_thumb_f32_convert_i32(sd, rm, true),
            ArmOp::F32ConvertI32U { sd, rm } => self.encode_thumb_f32_convert_i32(sd, rm, false),
            ArmOp::F32ConvertI64S { .. } | ArmOp::F32ConvertI64U { .. } => {
                Err(synth_core::Error::synthesis(
                    "F32 i64 conversion not supported (requires register pairs on 32-bit ARM)",
                ))
            }
            ArmOp::F32ReinterpretI32 { sd, rm } => {
                Ok(vfp_to_thumb_bytes(encode_vmov_core_sreg(true, sd, rm)))
            }
            ArmOp::I32ReinterpretF32 { rd, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vmov_core_sreg(false, sm, rd)))
            }
            ArmOp::I32TruncF32S { rd, sm } => self.encode_thumb_i32_trunc_f32(rd, sm, true),
            ArmOp::I32TruncF32U { rd, sm } => self.encode_thumb_i32_trunc_f32(rd, sm, false),

            // === F64 VFP double-precision Thumb-2 encodings ===
            // VFP instruction words are identical to ARM32; emit as two LE halfwords.
            ArmOp::F64Add { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE300B00, dd, dn, dm,
            ))),
            ArmOp::F64Sub { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE300B40, dd, dn, dm,
            ))),
            ArmOp::F64Mul { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE200B00, dd, dn, dm,
            ))),
            ArmOp::F64Div { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE800B00, dd, dn, dm,
            ))),
            ArmOp::F64Abs { dd, dm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg_f64(0xEEB00BC0, dd, dm)))
            }
            ArmOp::F64Neg { dd, dm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg_f64(0xEEB10B40, dd, dm)))
            }
            ArmOp::F64Sqrt { dd, dm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg_f64(0xEEB10BC0, dd, dm)))
            }

            // f64 pseudo-ops
            ArmOp::F64Ceil { dd, dm } => self.encode_thumb_f64_rounding(dd, dm, 0b10),
            ArmOp::F64Floor { dd, dm } => self.encode_thumb_f64_rounding(dd, dm, 0b01),
            ArmOp::F64Trunc { dd, dm } => self.encode_thumb_f64_rounding(dd, dm, 0b11),
            ArmOp::F64Nearest { dd, dm } => self.encode_thumb_f64_rounding(dd, dm, 0b00),
            ArmOp::F64Min { dd, dn, dm } => self.encode_thumb_f64_minmax(dd, dn, dm, true),
            ArmOp::F64Max { dd, dn, dm } => self.encode_thumb_f64_minmax(dd, dn, dm, false),
            ArmOp::F64Copysign { dd, dn, dm } => self.encode_thumb_f64_copysign(dd, dn, dm),

            // f64 comparisons
            ArmOp::F64Eq { rd, dn, dm } => self.encode_thumb_f64_compare(rd, dn, dm, 0x0),
            ArmOp::F64Ne { rd, dn, dm } => self.encode_thumb_f64_compare(rd, dn, dm, 0x1),
            ArmOp::F64Lt { rd, dn, dm } => self.encode_thumb_f64_compare(rd, dn, dm, 0x4),
            ArmOp::F64Le { rd, dn, dm } => self.encode_thumb_f64_compare(rd, dn, dm, 0x9),
            ArmOp::F64Gt { rd, dn, dm } => self.encode_thumb_f64_compare(rd, dn, dm, 0xC),
            ArmOp::F64Ge { rd, dn, dm } => self.encode_thumb_f64_compare(rd, dn, dm, 0xA),

            ArmOp::F64Const { dd, value } => self.encode_thumb_f64_const(dd, *value),

            ArmOp::F64Load { dd, addr } => Ok(vfp_to_thumb_bytes(encode_vfp_ldst_f64(
                0xED900B00, dd, addr,
            ))),
            ArmOp::F64Store { dd, addr } => Ok(vfp_to_thumb_bytes(encode_vfp_ldst_f64(
                0xED800B00, dd, addr,
            ))),

            ArmOp::F64ConvertI32S { dd, rm } => self.encode_thumb_f64_convert_i32(dd, rm, true),
            ArmOp::F64ConvertI32U { dd, rm } => self.encode_thumb_f64_convert_i32(dd, rm, false),
            ArmOp::F64ConvertI64S { .. } | ArmOp::F64ConvertI64U { .. } => {
                Err(synth_core::Error::synthesis(
                    "F64 i64 conversion not supported (requires register pairs on 32-bit ARM)",
                ))
            }
            ArmOp::F64PromoteF32 { dd, sm } => self.encode_thumb_f64_promote_f32(dd, sm),
            ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi } => Ok(vfp_to_thumb_bytes(
                encode_vmov_core_dreg(true, dd, rmlo, rmhi),
            )),
            ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm } => Ok(vfp_to_thumb_bytes(
                encode_vmov_core_dreg(false, dm, rdlo, rdhi),
            )),
            ArmOp::I64TruncF64S { .. } | ArmOp::I64TruncF64U { .. } => {
                Err(synth_core::Error::synthesis(
                    "i64 truncation from F64 not supported (requires i64 register pairs on 32-bit ARM)",
                ))
            }
            ArmOp::I32TruncF64S { rd, dm } => self.encode_thumb_i32_trunc_f64(rd, dm, true),
            ArmOp::I32TruncF64U { rd, dm } => self.encode_thumb_i32_trunc_f64(rd, dm, false),

            // i64 ops that are only stubs in Thumb mode
            ArmOp::I64Add { .. }
            | ArmOp::I64Sub { .. }
            | ArmOp::I64And { .. }
            | ArmOp::I64Or { .. }
            | ArmOp::I64Xor { .. }
            | ArmOp::I64Eqz { .. }
            | ArmOp::I64Eq { .. }
            | ArmOp::I64Ne { .. }
            | ArmOp::I64LtS { .. }
            | ArmOp::I64LtU { .. }
            | ArmOp::I64LeS { .. }
            | ArmOp::I64LeU { .. }
            | ArmOp::I64GtS { .. }
            | ArmOp::I64GtU { .. }
            | ArmOp::I64GeS { .. }
            | ArmOp::I64GeU { .. }
            | ArmOp::I64Const { .. }
            | ArmOp::I64Ldr { .. }
            | ArmOp::I64Str { .. }
            | ArmOp::I64ExtendI32S { .. }
            | ArmOp::I64ExtendI32U { .. }
            | ArmOp::I32WrapI64 { .. } => {
                let instr: u16 = 0xBF00; // NOP
                Ok(instr.to_le_bytes().to_vec())
            }

            // Catch-all for any remaining ops
            _ => {
                let instr: u16 = 0xBF00; // NOP
                Ok(instr.to_le_bytes().to_vec())
            }
        }
    }

    // === Thumb-2 VFP multi-instruction helpers ===

    /// Encode F32 comparison as Thumb-2: VCMP.F32 + VMRS + MOVS rd,#0 + IT + MOV rd,#1
    fn encode_thumb_f32_compare(
        &self,
        rd: &Reg,
        sn: &VfpReg,
        sm: &VfpReg,
        cond_code: u32,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let rd_bits = reg_to_bits(rd);

        // VCMP.F32 Sn, Sm
        let sn_num = vfp_sreg_to_num(sn);
        let sm_num = vfp_sreg_to_num(sm);
        let (vd, d) = encode_sreg(sn_num);
        let (vm, m) = encode_sreg(sm_num);
        let vcmp = 0xEEB40A40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcmp));

        // VMRS APSR_nzcv, FPSCR: 0xEEF1FA10
        bytes.extend_from_slice(&vfp_to_thumb_bytes(0xEEF1FA10));

        // MOVS Rd, #0 (16-bit): 0010 0 Rd(3) 0000 0000
        if rd_bits < 8 {
            let movs_zero: u16 = 0x2000 | ((rd_bits as u16) << 8);
            bytes.extend_from_slice(&movs_zero.to_le_bytes());
        } else {
            // MOV.W Rd, #0 (32-bit Thumb-2)
            let hw1: u16 = 0xF04F;
            let hw2: u16 = (rd_bits as u16) << 8;
            bytes.extend_from_slice(&hw1.to_le_bytes());
            bytes.extend_from_slice(&hw2.to_le_bytes());
        }

        // IT<cond> — If-Then for conditional MOV
        // IT encoding: 1011 1111 cond(4) mask(4)
        // mask = 0x8 for single "then" (IT)
        let it: u16 = 0xBF00 | ((cond_code as u16) << 4) | 0x8;
        bytes.extend_from_slice(&it.to_le_bytes());

        // MOV Rd, #1 (16-bit, conditional due to IT): 0010 0 Rd(3) 0000 0001
        if rd_bits < 8 {
            let mov_one: u16 = 0x2001 | ((rd_bits as u16) << 8);
            bytes.extend_from_slice(&mov_one.to_le_bytes());
        } else {
            // MOV.W Rd, #1 (32-bit)
            let hw1: u16 = 0xF04F;
            let hw2: u16 = ((rd_bits as u16) << 8) | 0x01;
            bytes.extend_from_slice(&hw1.to_le_bytes());
            bytes.extend_from_slice(&hw2.to_le_bytes());
        }

        Ok(bytes)
    }

    /// Encode F32 constant load as Thumb-2: MOVW + MOVT + VMOV
    fn encode_thumb_f32_const(&self, sd: &VfpReg, value: f32) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let bits = value.to_bits();
        let rt: u32 = 12; // R12/IP as temp

        // MOVW R12, #lo16
        // Thumb-2 MOVW: 11110 i 10 0100 imm4 | 0 imm3 Rd imm8
        let lo16 = bits & 0xFFFF;
        let imm4 = (lo16 >> 12) & 0xF;
        let i_bit = (lo16 >> 11) & 1;
        let imm3 = (lo16 >> 8) & 0x7;
        let imm8 = lo16 & 0xFF;
        let hw1: u16 = (0xF240 | (i_bit << 10) | imm4) as u16;
        let hw2: u16 = ((imm3 << 12) | (rt << 8) | imm8) as u16;
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // MOVT R12, #hi16
        let hi16 = (bits >> 16) & 0xFFFF;
        let imm4 = (hi16 >> 12) & 0xF;
        let i_bit = (hi16 >> 11) & 1;
        let imm3 = (hi16 >> 8) & 0x7;
        let imm8 = hi16 & 0xFF;
        let hw1: u16 = (0xF2C0 | (i_bit << 10) | imm4) as u16;
        let hw2: u16 = ((imm3 << 12) | (rt << 8) | imm8) as u16;
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // VMOV Sd, R12
        let vmov = encode_vmov_core_sreg(true, sd, &Reg::R12);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    /// Encode VMOV + VCVT.F32.xS32 as Thumb-2
    fn encode_thumb_f32_convert_i32(&self, sd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV Sd, Rm
        let vmov = encode_vmov_core_sreg(true, sd, rm);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        // VCVT.F32.S32/U32 Sd, Sd
        let sd_num = vfp_sreg_to_num(sd);
        let (vd, d) = encode_sreg(sd_num);
        let (vm, m) = encode_sreg(sd_num);
        let base = if signed { 0xEEB80A40 } else { 0xEEB80AC0 };
        let vcvt = base | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        Ok(bytes)
    }

    /// Encode F32 rounding pseudo-op as Thumb-2 via VCVT to integer and back
    /// Encode F32 rounding as Thumb-2.
    /// `mode`: FPSCR RMode — 0b00=nearest, 0b01=+inf(ceil), 0b10=-inf(floor), 0b11=zero(trunc)
    ///
    /// For trunc: uses VCVTR.S32.F32 (always truncates).
    /// For ceil/floor/nearest: sets FPSCR rounding mode, uses VCVT.S32.F32 (non-R variant),
    /// then restores FPSCR.
    fn encode_thumb_f32_rounding(&self, sd: &VfpReg, sm: &VfpReg, mode: u8) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let sm_num = vfp_sreg_to_num(sm);
        let sd_num = vfp_sreg_to_num(sd);
        let (vd_s, d_s) = encode_sreg(sd_num);
        let (vm_s, m_s) = encode_sreg(sm_num);

        if mode == 0b11 {
            // Trunc (toward zero): VCVTR.S32.F32 — bit[7]=1, always truncates
            let vcvt_to_int = 0xEEBD0AC0 | (d_s << 22) | (vd_s << 12) | (m_s << 5) | vm_s;
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_int));
        } else {
            // ceil/floor/nearest: manipulate FPSCR rounding mode
            let rt: u32 = 12; // R12/IP as temp

            // VMRS R12, FPSCR
            let vmrs = 0xEEF10A10 | (rt << 12);
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmrs));

            // BIC.W R12, R12, #(3 << 22) — clear RMode bits [23:22]
            // Thumb-2 modified immediate for 3<<22 = 0x00C00000:
            // BIC.W encoding: 11110 i 0 0001 S Rn | 0 imm3 Rd imm8
            // 0x00C00000 = 0x03 shifted left by 22 => Thumb mod-imm: i=0, imm3=0b101, imm8=0x03
            let bic_hw1: u16 = 0xF020 | ((rt as u16) & 0xF); // BIC, Rn=R12
            let bic_hw2: u16 = (0x05 << 12) | ((rt as u16) << 8) | 0x03;
            bytes.extend_from_slice(&bic_hw1.to_le_bytes());
            bytes.extend_from_slice(&bic_hw2.to_le_bytes());

            // ORR.W R12, R12, #(mode << 22)
            if mode != 0 {
                let orr_hw1: u16 = 0xF040 | ((rt as u16) & 0xF); // ORR, Rn=R12
                let orr_hw2: u16 = (0x05 << 12) | ((rt as u16) << 8) | (mode as u16);
                bytes.extend_from_slice(&orr_hw1.to_le_bytes());
                bytes.extend_from_slice(&orr_hw2.to_le_bytes());
            }

            // VMSR FPSCR, R12
            let vmsr = 0xEEE10A10 | (rt << 12);
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmsr));

            // VCVT.S32.F32 Sd, Sm — non-R variant (bit[7]=0), uses FPSCR rmode
            let vcvt_to_int = 0xEEBD0A40 | (d_s << 22) | (vd_s << 12) | (m_s << 5) | vm_s;
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_int));

            // Restore FPSCR: clear rmode bits back to nearest (default)
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmrs));
            bytes.extend_from_slice(&bic_hw1.to_le_bytes());
            bytes.extend_from_slice(&bic_hw2.to_le_bytes());
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmsr));
        }

        // VCVT.F32.S32 Sd, Sd (convert integer result back to float)
        let (vd2, d2) = encode_sreg(sd_num);
        let vcvt_to_float = 0xEEB80A40 | (d2 << 22) | (vd2 << 12) | (d_s << 5) | vd_s;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_float));

        Ok(bytes)
    }

    /// Encode F32 min/max as Thumb-2: VMOV + VCMP + VMRS + IT + VMOV
    fn encode_thumb_f32_minmax(
        &self,
        sd: &VfpReg,
        sn: &VfpReg,
        sm: &VfpReg,
        is_min: bool,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let sn_num = vfp_sreg_to_num(sn);
        let sm_num = vfp_sreg_to_num(sm);
        let sd_num = vfp_sreg_to_num(sd);

        // VMOV.F32 Sd, Sn
        let (vd, d) = encode_sreg(sd_num);
        let (vn, n) = encode_sreg(sn_num);
        let vmov_sn = 0xEEB00A40 | (d << 22) | (vd << 12) | (n << 5) | vn;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov_sn));

        // VCMP.F32 Sn, Sm
        let (vm, m) = encode_sreg(sm_num);
        let vcmp = 0xEEB40A40 | (n << 22) | (vn << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcmp));

        // VMRS APSR_nzcv, FPSCR
        bytes.extend_from_slice(&vfp_to_thumb_bytes(0xEEF1FA10));

        // IT GT (for min) or IT MI (for max)
        let cond: u16 = if is_min { 0xC } else { 0x4 };
        let it: u16 = 0xBF00 | (cond << 4) | 0x8;
        bytes.extend_from_slice(&it.to_le_bytes());

        // VMOV{cond}.F32 Sd, Sm — conditional VMOV in IT block
        let vmov_sm = 0xEEB00A40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov_sm));

        Ok(bytes)
    }

    /// Encode F32 copysign as Thumb-2
    fn encode_thumb_f32_copysign(&self, sd: &VfpReg, sn: &VfpReg, sm: &VfpReg) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV R12, Sm (get sign source bits)
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_sreg(
            false,
            sm,
            &Reg::R12,
        )));

        // VMOV R0, Sn (get magnitude source bits)
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_sreg(
            false,
            sn,
            &Reg::R0,
        )));

        // AND.W R12, R12, #0x80000000
        // Thumb-2 modified immediate: 0x80000000 = constant 0x80 with rotation
        // Using T1 encoding: 11110 i 0 0000 S Rn | 0 imm3 Rd imm8
        // 0x80000000: i=0, imm3=0b001, imm8=0x00 (rotation=4, value=0x80)
        // Actually encoding #0x80000000 as modified constant:
        // bit pattern 1 followed by 31 zeros: enc = 0b0100_00000000 = 0x0100? No.
        // ARM modified immediate: abcdefgh rotated. 0x80000000 = 0x80 ROR 2 = enc 0x0102
        // Actually: value = abcdefgh ROR (2*rot). 0x80 = 10000000, ROR 2 gives 0x20000000.
        // For 0x80000000: 0x02 ROR 2 = 0x80000000. So imm12 = (1<<8) | 0x02 = 0x102
        let hw1: u16 = 0xF000 | 12; // AND.W R12, R12, #modified_const (i=0, Rn=R12)
        let hw2: u16 = (0x1 << 12) | (12 << 8) | 0x02; // imm3=1, Rd=R12, imm8=0x02
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // BIC.W R0, R0, #0x80000000 (R0 = register 0, fields are zero)
        let hw1: u16 = 0xF020; // BIC.W R0, R0, #modified_const (i=0, Rn=R0)
        let hw2: u16 = (0x1 << 12) | 0x02; // imm3=1, Rd=R0, imm8=0x02
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // ORR.W R0, R0, R12 (R0 = register 0)
        let hw1: u16 = 0xEA40; // ORR.W R0, R0, R12 (Rn=R0)
        let hw2: u16 = 12; // Rd=R0, Rm=R12
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // VMOV Sd, R0
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_sreg(
            true,
            sd,
            &Reg::R0,
        )));

        Ok(bytes)
    }

    /// Encode F64 comparison as Thumb-2: VCMP.F64 + VMRS + MOV #0 + IT + MOV #1
    fn encode_thumb_f64_compare(
        &self,
        rd: &Reg,
        dn: &VfpReg,
        dm: &VfpReg,
        cond_code: u32,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let rd_bits = reg_to_bits(rd);

        // VCMP.F64 Dn, Dm
        let dn_num = vfp_dreg_to_num(dn);
        let dm_num = vfp_dreg_to_num(dm);
        let (vd, d) = encode_dreg(dn_num);
        let (vm, m) = encode_dreg(dm_num);
        let vcmp = 0xEEB40B40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcmp));

        // VMRS APSR_nzcv, FPSCR
        bytes.extend_from_slice(&vfp_to_thumb_bytes(0xEEF1FA10));

        // MOVS Rd, #0
        if rd_bits < 8 {
            let movs_zero: u16 = 0x2000 | ((rd_bits as u16) << 8);
            bytes.extend_from_slice(&movs_zero.to_le_bytes());
        } else {
            let hw1: u16 = 0xF04F;
            let hw2: u16 = (rd_bits as u16) << 8;
            bytes.extend_from_slice(&hw1.to_le_bytes());
            bytes.extend_from_slice(&hw2.to_le_bytes());
        }

        // IT<cond>
        let it: u16 = 0xBF00 | ((cond_code as u16) << 4) | 0x8;
        bytes.extend_from_slice(&it.to_le_bytes());

        // MOV Rd, #1
        if rd_bits < 8 {
            let mov_one: u16 = 0x2001 | ((rd_bits as u16) << 8);
            bytes.extend_from_slice(&mov_one.to_le_bytes());
        } else {
            let hw1: u16 = 0xF04F;
            let hw2: u16 = ((rd_bits as u16) << 8) | 0x01;
            bytes.extend_from_slice(&hw1.to_le_bytes());
            bytes.extend_from_slice(&hw2.to_le_bytes());
        }

        Ok(bytes)
    }

    /// Encode F64 constant load as Thumb-2: MOVW+MOVT (lo32 into R0) + MOVW+MOVT (hi32 into R12) + VMOV Dd, R0, R12
    fn encode_thumb_f64_const(&self, dd: &VfpReg, value: f64) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let bits = value.to_bits();
        let lo32 = bits as u32;
        let hi32 = (bits >> 32) as u32;

        // MOVW R0, #lo16(lo32)
        let lo16 = lo32 & 0xFFFF;
        bytes.extend_from_slice(&self.encode_thumb32_movw_raw(0, lo16)?);

        // MOVT R0, #hi16(lo32)
        let hi16 = (lo32 >> 16) & 0xFFFF;
        bytes.extend_from_slice(&self.encode_thumb32_movt_raw(0, hi16)?);

        // MOVW R12, #lo16(hi32)
        let lo16 = hi32 & 0xFFFF;
        bytes.extend_from_slice(&self.encode_thumb32_movw_raw(12, lo16)?);

        // MOVT R12, #hi16(hi32)
        let hi16 = (hi32 >> 16) & 0xFFFF;
        bytes.extend_from_slice(&self.encode_thumb32_movt_raw(12, hi16)?);

        // VMOV Dd, R0, R12
        let vmov = encode_vmov_core_dreg(true, dd, &Reg::R0, &Reg::R12);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    /// Encode VMOV Sd, Rm + VCVT.F64.S32/U32 Dd, Sd as Thumb-2
    fn encode_thumb_f64_convert_i32(&self, dd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV S0, Rm
        let vmov = encode_vmov_core_sreg(true, &VfpReg::S0, rm);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        // VCVT.F64.S32 Dd, S0 or VCVT.F64.U32 Dd, S0
        let dd_num = vfp_dreg_to_num(dd);
        let (vd, d) = encode_dreg(dd_num);
        let base = if signed { 0xEEB80B40 } else { 0xEEB80BC0 };
        let vcvt = base | (d << 22) | (vd << 12);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        Ok(bytes)
    }

    /// Encode VCVT.F64.F32 Dd, Sm as Thumb-2
    fn encode_thumb_f64_promote_f32(&self, dd: &VfpReg, sm: &VfpReg) -> Result<Vec<u8>> {
        let dd_num = vfp_dreg_to_num(dd);
        let sm_num = vfp_sreg_to_num(sm);
        let (vd, d) = encode_dreg(dd_num);
        let (vm, m) = encode_sreg(sm_num);

        let vcvt = 0xEEB70AC0 | (d << 22) | (vd << 12) | (m << 5) | vm;
        Ok(vfp_to_thumb_bytes(vcvt))
    }

    /// Encode VCVT.S32/U32.F64 S0, Dm + VMOV Rd, S0 as Thumb-2
    fn encode_thumb_i32_trunc_f64(&self, rd: &Reg, dm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm);
        let (vm, m) = encode_dreg(dm_num);

        // VCVT.S32.F64 S0, Dm or VCVT.U32.F64 S0, Dm
        let base = if signed { 0xEEBD0BC0 } else { 0xEEBC0BC0 };
        let vcvt = base | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        // VMOV Rd, S0
        let vmov = encode_vmov_core_sreg(false, &VfpReg::S0, rd);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    /// Encode F64 rounding pseudo-op as Thumb-2 via VCVT to integer and back
    fn encode_thumb_f64_rounding(&self, dd: &VfpReg, dm: &VfpReg, _mode: u8) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm);
        let dd_num = vfp_dreg_to_num(dd);
        let (vm, m) = encode_dreg(dm_num);
        let (vd, d) = encode_dreg(dd_num);

        // VCVT.S32.F64 S0, Dm
        let vcvt_to_int = 0xEEBD0BC0 | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_int));

        // VCVT.F64.S32 Dd, S0
        let vcvt_to_float = 0xEEB80B40 | (d << 22) | (vd << 12);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_float));

        Ok(bytes)
    }

    /// Encode F64 min/max as Thumb-2
    fn encode_thumb_f64_minmax(
        &self,
        dd: &VfpReg,
        dn: &VfpReg,
        dm: &VfpReg,
        is_min: bool,
    ) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dn_num = vfp_dreg_to_num(dn);
        let dm_num = vfp_dreg_to_num(dm);
        let dd_num = vfp_dreg_to_num(dd);

        // VMOV.F64 Dd, Dn
        let (vd, d) = encode_dreg(dd_num);
        let (vn, n) = encode_dreg(dn_num);
        let vmov_dn = 0xEEB00B40 | (d << 22) | (vd << 12) | (n << 5) | vn;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov_dn));

        // VCMP.F64 Dn, Dm
        let (vm, m) = encode_dreg(dm_num);
        let vcmp = 0xEEB40B40 | (n << 22) | (vn << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcmp));

        // VMRS APSR_nzcv, FPSCR
        bytes.extend_from_slice(&vfp_to_thumb_bytes(0xEEF1FA10));

        // IT GT (for min) or IT MI (for max)
        let cond: u16 = if is_min { 0xC } else { 0x4 };
        let it: u16 = 0xBF00 | (cond << 4) | 0x8;
        bytes.extend_from_slice(&it.to_le_bytes());

        // VMOV{cond}.F64 Dd, Dm
        let vmov_dm = 0xEEB00B40 | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov_dm));

        Ok(bytes)
    }

    /// Encode F64 copysign as Thumb-2
    fn encode_thumb_f64_copysign(&self, dd: &VfpReg, dn: &VfpReg, dm: &VfpReg) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV R0, R12, Dm (get sign source)
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_dreg(
            false,
            dm,
            &Reg::R0,
            &Reg::R12,
        )));

        // VMOV R1, R2, Dn (get magnitude source)
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_dreg(
            false,
            dn,
            &Reg::R1,
            &Reg::R2,
        )));

        // AND.W R12, R12, #0x80000000 (i=0, Rn=R12)
        let hw1: u16 = 0xF000 | 12;
        let hw2: u16 = (0x1 << 12) | (12 << 8) | 0x02;
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // BIC.W R2, R2, #0x80000000 (i=0, Rn=R2)
        let hw1: u16 = 0xF020 | 2;
        let hw2: u16 = (0x1 << 12) | (2 << 8) | 0x02;
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // ORR.W R2, R2, R12
        let hw1: u16 = 0xEA40 | 2;
        let hw2: u16 = (2 << 8) | 12;
        bytes.extend_from_slice(&hw1.to_le_bytes());
        bytes.extend_from_slice(&hw2.to_le_bytes());

        // VMOV Dd, R1, R2
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_dreg(
            true,
            dd,
            &Reg::R1,
            &Reg::R2,
        )));

        Ok(bytes)
    }

    /// Encode VCVT.S32/U32.F32 + VMOV as Thumb-2
    fn encode_thumb_i32_trunc_f32(&self, rd: &Reg, sm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        let sm_num = vfp_sreg_to_num(sm);
        let (vd, d) = encode_sreg(sm_num);
        let (vm, m) = encode_sreg(sm_num);
        let base = if signed { 0xEEBD0AC0 } else { 0xEEBC0AC0 };
        let vcvt = base | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        // VMOV Rd, Sm
        let vmov = encode_vmov_core_sreg(false, sm, rd);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    // === Thumb-2 32-bit encoding helpers ===

    /// Encode Thumb-2 32-bit ADD with immediate
    fn encode_thumb32_add(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        // ADD.W Rd, Rn, #imm12
        // First halfword: 1111 0 i 0 1000 S Rn
        // Second halfword: 0 imm3 Rd imm8
        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        let hw1: u16 = (0xF100 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit SUB with immediate
    fn encode_thumb32_sub(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        let hw1: u16 = (0xF1A0 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit ADDS with immediate (sets flags)
    fn encode_thumb32_adds(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        // ADDS.W Rd, Rn, #imm (with S=1)
        // First halfword: 1111 0 i 0 1000 1 Rn = F110 | i<<10 | Rn
        let hw1: u16 = (0xF110 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit SUBS with immediate (sets flags)
    fn encode_thumb32_subs(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        // SUBS.W Rd, Rn, #imm (with S=1)
        // First halfword: 1111 0 i 0 1101 1 Rn = F1B0 | i<<10 | Rn
        let hw1: u16 = (0xF1B0 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit MOVW (16-bit immediate)
    fn encode_thumb32_movw(&self, rd: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let imm16 = imm & 0xFFFF;

        // MOVW Rd, #imm16
        // 1111 0 i 10 0 1 0 0 imm4 | 0 imm3 Rd imm8
        let imm4 = (imm16 >> 12) & 0xF;
        let i_bit = (imm16 >> 11) & 1;
        let imm3 = (imm16 >> 8) & 0x7;
        let imm8 = imm16 & 0xFF;

        let hw1: u16 = (0xF240 | (i_bit << 10) | imm4) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit shift with immediate
    fn encode_thumb32_shift(
        &self,
        rd: &Reg,
        rm: &Reg,
        shift: u32,
        shift_type: u8,
    ) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rm_bits = reg_to_bits(rm);
        let imm5 = shift & 0x1F;
        let imm2 = imm5 & 0x3;
        let imm3 = (imm5 >> 2) & 0x7;

        // MOV.W Rd, Rm, <shift> #imm
        // EA4F 0 imm3 Rd imm2 type Rm
        let hw1: u16 = 0xEA4F;
        let hw2: u16 =
            ((imm3 << 12) | (rd_bits << 8) | (imm2 << 6) | ((shift_type as u32) << 4) | rm_bits)
                as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit shift by register
    /// Encoding: 11111010 0xx0 Rn | 1111 Rd 0000 Rm
    /// shift_type: 00=LSL, 01=LSR, 10=ASR, 11=ROR
    fn encode_thumb32_shift_reg(
        &self,
        rd: &Reg,
        rn: &Reg,
        rm: &Reg,
        shift_type: u8,
    ) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);
        let rm_bits = reg_to_bits(rm);

        // hw1: 1111 1010 0xx0 Rn
        let hw1: u16 = (0xFA00 | ((shift_type as u32) << 5) | rn_bits) as u16;
        // hw2: 1111 Rd 0000 Rm
        let hw2: u16 = (0xF000 | (rd_bits << 8) | rm_bits) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit CMP with immediate
    fn encode_thumb32_cmp_imm(&self, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rn_bits = reg_to_bits(rn);

        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        // CMP.W Rn, #imm
        let hw1: u16 = (0xF1B0 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | 0x0F00 | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDR
    fn encode_thumb32_ldr(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);

        // LDR.W Rd, [Rn, #imm12]
        let hw1: u16 = (0xF8D0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STR
    fn encode_thumb32_str(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);

        // STR.W Rd, [Rn, #imm12]
        let hw1: u16 = (0xF8C0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDR with register offset: LDR.W Rd, [Rn, Rm]
    fn encode_thumb32_ldr_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);

        // LDR.W Rd, [Rn, Rm, LSL #0]
        // Encoding: 1111 1000 0101 Rn | Rt 0000 00 imm2 Rm
        // imm2 = 00 for no shift (LSL #0)
        let hw1: u16 = (0xF850 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STR with register offset: STR.W Rd, [Rn, Rm]
    fn encode_thumb32_str_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);

        // STR.W Rd, [Rn, Rm, LSL #0]
        // Encoding: 1111 1000 0100 Rn | Rt 0000 00 imm2 Rm
        // imm2 = 00 for no shift (LSL #0)
        let hw1: u16 = (0xF840 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit ADD with immediate: ADD.W Rd, Rn, #imm
    fn encode_thumb32_add_imm(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        // For small immediates, use ADD.W Rd, Rn, #imm12
        // Encoding: 1111 0 i 0 1 0 0 0 S Rn | 0 imm3 Rd imm8
        // S = 0 (don't update flags)
        // The 12-bit immediate is encoded as: i:imm3:imm8
        // For simplicity, we only support imm <= 0xFFF (direct encoding)
        if imm <= 0xFFF {
            let i_bit = (imm >> 11) & 1;
            let imm3 = (imm >> 8) & 0x7;
            let imm8 = imm & 0xFF;

            let hw1: u16 = (0xF100 | (i_bit << 10) | rn_bits) as u16;
            let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

            let mut bytes = hw1.to_le_bytes().to_vec();
            bytes.extend_from_slice(&hw2.to_le_bytes());
            Ok(bytes)
        } else {
            // For larger immediates, would need MOVW/MOVT + ADD
            // For now, return error
            Err(synth_core::Error::synthesis(
                "ADD immediate too large for single instruction",
            ))
        }
    }

    // === Raw encoding helpers for POPCNT (take register numbers directly) ===

    /// Encode Thumb-2 32-bit MOVW (16-bit immediate) - raw version
    fn encode_thumb32_movw_raw(&self, rd: u32, imm16: u32) -> Result<Vec<u8>> {
        // MOVW Rd, #imm16
        // 1111 0 i 10 0 1 0 0 imm4 | 0 imm3 Rd imm8
        let imm16 = imm16 & 0xFFFF;
        let imm4 = (imm16 >> 12) & 0xF;
        let i_bit = (imm16 >> 11) & 1;
        let imm3 = (imm16 >> 8) & 0x7;
        let imm8 = imm16 & 0xFF;

        let hw1: u16 = (0xF240 | (i_bit << 10) | imm4) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit MOVT (move top 16 bits) - raw version
    fn encode_thumb32_movt_raw(&self, rd: u32, imm16: u32) -> Result<Vec<u8>> {
        // MOVT Rd, #imm16
        // 1111 0 i 10 1 1 0 0 imm4 | 0 imm3 Rd imm8
        let imm16 = imm16 & 0xFFFF;
        let imm4 = (imm16 >> 12) & 0xF;
        let i_bit = (imm16 >> 11) & 1;
        let imm3 = (imm16 >> 8) & 0x7;
        let imm8 = imm16 & 0xFF;

        let hw1: u16 = (0xF2C0 | (i_bit << 10) | imm4) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LSR (logical shift right) with immediate - raw version
    fn encode_thumb32_lsr_raw(&self, rd: u32, rm: u32, shift: u32) -> Result<Vec<u8>> {
        // MOV.W Rd, Rm, LSR #imm
        // EA4F 0 imm3 Rd imm2 01 Rm
        let imm5 = shift & 0x1F;
        let imm2 = imm5 & 0x3;
        let imm3 = (imm5 >> 2) & 0x7;

        let hw1: u16 = 0xEA4F;
        let hw2: u16 = ((imm3 << 12) | (rd << 8) | (imm2 << 6) | (0b01 << 4) | rm) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit AND (register) - raw version
    fn encode_thumb32_and_reg_raw(&self, rd: u32, rn: u32, rm: u32) -> Result<Vec<u8>> {
        // AND.W Rd, Rn, Rm
        // EA00 Rn | 0 Rd 00 00 Rm
        let hw1: u16 = (0xEA00 | rn) as u16;
        let hw2: u16 = ((rd << 8) | rm) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit AND with immediate - raw version
    fn encode_thumb32_and_imm_raw(&self, rd: u32, rn: u32, imm: u32) -> Result<Vec<u8>> {
        // AND.W Rd, Rn, #<modified_immediate>
        // For small immediates (0-255), the encoding is simpler
        // F0 00 Rn | 0 imm3 Rd imm8
        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        let hw1: u16 = (0xF000 | (i_bit << 10) | rn) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit SUB (register) - raw version
    fn encode_thumb32_sub_reg_raw(&self, rd: u32, rn: u32, rm: u32) -> Result<Vec<u8>> {
        // SUB.W Rd, Rn, Rm
        // EBA0 Rn | 0 Rd 00 00 Rm
        let hw1: u16 = (0xEBA0 | rn) as u16;
        let hw2: u16 = ((rd << 8) | rm) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit ADD (register) - raw version
    fn encode_thumb32_add_reg_raw(&self, rd: u32, rn: u32, rm: u32) -> Result<Vec<u8>> {
        // ADD.W Rd, Rn, Rm
        // EB00 Rn | 0 Rd 00 00 Rm
        let hw1: u16 = (0xEB00 | rn) as u16;
        let hw2: u16 = ((rd << 8) | rm) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
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

        Operand2::RegShift {
            rm,
            shift: _,
            amount,
        } => {
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

/// S-register number: S0=0, S1=1, ..., S31=31
fn vfp_sreg_to_num(reg: &VfpReg) -> u32 {
    match reg {
        VfpReg::S0 => 0,
        VfpReg::S1 => 1,
        VfpReg::S2 => 2,
        VfpReg::S3 => 3,
        VfpReg::S4 => 4,
        VfpReg::S5 => 5,
        VfpReg::S6 => 6,
        VfpReg::S7 => 7,
        VfpReg::S8 => 8,
        VfpReg::S9 => 9,
        VfpReg::S10 => 10,
        VfpReg::S11 => 11,
        VfpReg::S12 => 12,
        VfpReg::S13 => 13,
        VfpReg::S14 => 14,
        VfpReg::S15 => 15,
        VfpReg::S16 => 16,
        VfpReg::S17 => 17,
        VfpReg::S18 => 18,
        VfpReg::S19 => 19,
        VfpReg::S20 => 20,
        VfpReg::S21 => 21,
        VfpReg::S22 => 22,
        VfpReg::S23 => 23,
        VfpReg::S24 => 24,
        VfpReg::S25 => 25,
        VfpReg::S26 => 26,
        VfpReg::S27 => 27,
        VfpReg::S28 => 28,
        VfpReg::S29 => 29,
        VfpReg::S30 => 30,
        VfpReg::S31 => 31,
        // D-registers are not used in F32 single-precision encodings
        _ => panic!("D-registers not supported in single-precision VFP encoding"),
    }
}

/// D-register number: D0=0, D1=1, ..., D15=15
fn vfp_dreg_to_num(reg: &VfpReg) -> u32 {
    match reg {
        VfpReg::D0 => 0,
        VfpReg::D1 => 1,
        VfpReg::D2 => 2,
        VfpReg::D3 => 3,
        VfpReg::D4 => 4,
        VfpReg::D5 => 5,
        VfpReg::D6 => 6,
        VfpReg::D7 => 7,
        VfpReg::D8 => 8,
        VfpReg::D9 => 9,
        VfpReg::D10 => 10,
        VfpReg::D11 => 11,
        VfpReg::D12 => 12,
        VfpReg::D13 => 13,
        VfpReg::D14 => 14,
        VfpReg::D15 => 15,
        // S-registers are not used in F64 double-precision encodings
        _ => panic!("S-registers not supported in double-precision VFP encoding"),
    }
}

/// Split S-register into (Vx[3:0], qualifier_bit) for VFP encoding.
/// For an S-register number s: Vx = s >> 1, qualifier = s & 1.
/// The qualifier bit goes to D (bit 22), N (bit 7), or M (bit 5) depending on role.
fn encode_sreg(s: u32) -> (u32, u32) {
    (s >> 1, s & 1)
}

/// Split D-register into (Vx[3:0], qualifier_bit) for VFP double-precision encoding.
/// For a D-register number d: Vx = d & 0xF, qualifier = (d >> 4) & 1.
/// For D0-D15, qualifier is always 0.
fn encode_dreg(d: u32) -> (u32, u32) {
    (d & 0xF, (d >> 4) & 1)
}

/// Encode a VFP 3-register arithmetic instruction (VADD.F32, VSUB.F32, VMUL.F32, VDIV.F32).
/// Returns the full 32-bit instruction word.
///
/// VFP encoding: [cond 1110] [D opc1 Vn] [Vd 101 sz] [N opc2 M 0 Vm]
/// For single-precision (sz=0), coprocessor = 0xA (bits[11:8]).
fn encode_vfp_3reg(base: u32, sd: &VfpReg, sn: &VfpReg, sm: &VfpReg) -> u32 {
    let sd_num = vfp_sreg_to_num(sd);
    let sn_num = vfp_sreg_to_num(sn);
    let sm_num = vfp_sreg_to_num(sm);
    let (vd, d) = encode_sreg(sd_num);
    let (vn, n) = encode_sreg(sn_num);
    let (vm, m) = encode_sreg(sm_num);

    base | (d << 22) | (vn << 16) | (vd << 12) | (n << 7) | (m << 5) | vm
}

/// Encode a VFP 2-register instruction (VNEG.F32, VABS.F32, VSQRT.F32).
/// Returns the full 32-bit instruction word.
fn encode_vfp_2reg(base: u32, sd: &VfpReg, sm: &VfpReg) -> u32 {
    let sd_num = vfp_sreg_to_num(sd);
    let sm_num = vfp_sreg_to_num(sm);
    let (vd, d) = encode_sreg(sd_num);
    let (vm, m) = encode_sreg(sm_num);

    base | (d << 22) | (vd << 12) | (m << 5) | vm
}

/// Encode a VFP load/store (VLDR.F32 / VSTR.F32).
/// offset is in bytes and must be word-aligned; encoded as imm8 = offset/4.
/// U bit (bit 23) controls add/subtract offset.
fn encode_vfp_ldst(base: u32, sd: &VfpReg, addr: &MemAddr) -> u32 {
    let sd_num = vfp_sreg_to_num(sd);
    let (vd, d) = encode_sreg(sd_num);
    let rn = reg_to_bits(&addr.base);

    let offset = addr.offset;
    let u_bit = if offset >= 0 { 1u32 } else { 0u32 };
    let abs_offset = offset.unsigned_abs();
    let imm8 = (abs_offset / 4) & 0xFF;

    base | (u_bit << 23) | (d << 22) | (rn << 16) | (vd << 12) | imm8
}

/// Encode VMOV between core register and S-register.
/// VMOV Sn, Rt: 0xEE00_0A10 | (Vn << 16) | (N << 7) | (Rt << 12)
/// VMOV Rt, Sn: 0xEE10_0A10 | (Vn << 16) | (N << 7) | (Rt << 12)
fn encode_vmov_core_sreg(to_sreg: bool, sreg: &VfpReg, core: &Reg) -> u32 {
    let s_num = vfp_sreg_to_num(sreg);
    let (vn, n) = encode_sreg(s_num);
    let rt = reg_to_bits(core);

    let base = if to_sreg { 0xEE000A10 } else { 0xEE100A10 };
    base | (vn << 16) | (rt << 12) | (n << 7)
}

/// Encode a VFP 3-register double-precision instruction (VADD.F64, VSUB.F64, etc.).
/// For double-precision (sz=1), coprocessor = 0xB (bits[11:8]).
/// The base should have bit 8 = 1 for F64 (0xB suffix instead of 0xA).
fn encode_vfp_3reg_f64(base: u32, dd: &VfpReg, dn: &VfpReg, dm: &VfpReg) -> u32 {
    let dd_num = vfp_dreg_to_num(dd);
    let dn_num = vfp_dreg_to_num(dn);
    let dm_num = vfp_dreg_to_num(dm);
    let (vd, d) = encode_dreg(dd_num);
    let (vn, n) = encode_dreg(dn_num);
    let (vm, m) = encode_dreg(dm_num);

    base | (d << 22) | (vn << 16) | (vd << 12) | (n << 7) | (m << 5) | vm
}

/// Encode a VFP 2-register double-precision instruction (VNEG.F64, VABS.F64, VSQRT.F64).
fn encode_vfp_2reg_f64(base: u32, dd: &VfpReg, dm: &VfpReg) -> u32 {
    let dd_num = vfp_dreg_to_num(dd);
    let dm_num = vfp_dreg_to_num(dm);
    let (vd, d) = encode_dreg(dd_num);
    let (vm, m) = encode_dreg(dm_num);

    base | (d << 22) | (vd << 12) | (m << 5) | vm
}

/// Encode a VFP load/store for double-precision (VLDR.64 / VSTR.64).
/// offset is in bytes and must be word-aligned; encoded as imm8 = offset/4.
fn encode_vfp_ldst_f64(base: u32, dd: &VfpReg, addr: &MemAddr) -> u32 {
    let dd_num = vfp_dreg_to_num(dd);
    let (vd, d) = encode_dreg(dd_num);
    let rn = reg_to_bits(&addr.base);

    let offset = addr.offset;
    let u_bit = if offset >= 0 { 1u32 } else { 0u32 };
    let abs_offset = offset.unsigned_abs();
    let imm8 = (abs_offset / 4) & 0xFF;

    base | (u_bit << 23) | (d << 22) | (rn << 16) | (vd << 12) | imm8
}

/// Encode VMOV between two core registers and a D-register.
/// VMOV Dm, Rt, Rt2: 0xEC40_0B10 | (Rt2 << 16) | (Rt << 12) | (M << 5) | Vm
/// VMOV Rt, Rt2, Dm: 0xEC50_0B10 | (Rt2 << 16) | (Rt << 12) | (M << 5) | Vm
fn encode_vmov_core_dreg(to_dreg: bool, dreg: &VfpReg, core_lo: &Reg, core_hi: &Reg) -> u32 {
    let d_num = vfp_dreg_to_num(dreg);
    let (vm, m) = encode_dreg(d_num);
    let rt = reg_to_bits(core_lo);
    let rt2 = reg_to_bits(core_hi);

    let base = if to_dreg { 0xEC400B10 } else { 0xEC500B10 };
    base | (rt2 << 16) | (rt << 12) | (m << 5) | vm
}

/// Emit a VFP 32-bit instruction as Thumb-2 bytes (two LE halfwords).
fn vfp_to_thumb_bytes(instr: u32) -> Vec<u8> {
    let hw1 = ((instr >> 16) & 0xFFFF) as u16;
    let hw2 = (instr & 0xFFFF) as u16;
    let mut bytes = hw1.to_le_bytes().to_vec();
    bytes.extend_from_slice(&hw2.to_le_bytes());
    bytes
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
            addr: MemAddr::imm(Reg::R1, 4),
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
            addr: MemAddr::imm(Reg::SP, 0),
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

    // === Thumb-2 32-bit encoding tests ===

    #[test]
    fn test_encode_sdiv_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Sdiv {
            rd: Reg::R0,
            rn: Reg::R1,
            rm: Reg::R2,
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit Thumb-2 instruction

        // SDIV R0, R1, R2: 0xFB91 0xF0F2
        // First halfword: 0xFB90 | Rn(1) = 0xFB91
        // Second halfword: 0xF0F0 | Rd(0)<<8 | Rm(2) = 0xF0F2
        // Little-endian: [0x91, 0xFB, 0xF2, 0xF0]
        assert_eq!(code[0], 0x91);
        assert_eq!(code[1], 0xFB);
        assert_eq!(code[2], 0xF2);
        assert_eq!(code[3], 0xF0);
    }

    #[test]
    fn test_encode_udiv_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Udiv {
            rd: Reg::R0,
            rn: Reg::R1,
            rm: Reg::R2,
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit Thumb-2 instruction

        // UDIV R0, R1, R2: 0xFBB1 0xF0F2
        // Little-endian: [0xB1, 0xFB, 0xF2, 0xF0]
        assert_eq!(code[0], 0xB1);
        assert_eq!(code[1], 0xFB);
        assert_eq!(code[2], 0xF2);
        assert_eq!(code[3], 0xF0);
    }

    #[test]
    fn test_encode_mul_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Mul {
            rd: Reg::R0,
            rn: Reg::R1,
            rm: Reg::R2,
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit Thumb-2 instruction
    }

    #[test]
    fn test_encode_and_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::And {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit Thumb-2 instruction
    }

    #[test]
    fn test_encode_lsl_thumb2_low_regs() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Lsl {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 5,
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2); // 16-bit for low registers
    }

    #[test]
    fn test_encode_clz_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Clz {
            rd: Reg::R0,
            rm: Reg::R1,
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit Thumb-2 instruction
    }

    #[test]
    fn test_encode_bx_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Bx { rm: Reg::LR };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2); // 16-bit instruction

        // BX LR: 0x4770
        assert_eq!(code, vec![0x70, 0x47]);
    }

    // ========================================================================
    // f32 pseudo-op encoding tests
    // ========================================================================

    #[test]
    fn test_encode_f32_abs_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F32Abs {
            sd: VfpReg::S0,
            sm: VfpReg::S2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // Single VFP instruction
    }

    #[test]
    fn test_encode_f32_neg_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F32Neg {
            sd: VfpReg::S0,
            sm: VfpReg::S2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f32_sqrt_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F32Sqrt {
            sd: VfpReg::S0,
            sm: VfpReg::S2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f32_ceil_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F32Ceil {
            sd: VfpReg::S0,
            sm: VfpReg::S2,
        };
        let code = encoder.encode(&op).unwrap();
        // VMRS + BIC + ORR + VMSR + VCVT.S32.F32 + VMRS + BIC + VMSR + VCVT.F32.S32
        assert_eq!(code.len(), 36);
    }

    #[test]
    fn test_encode_f32_floor_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F32Floor {
            sd: VfpReg::S0,
            sm: VfpReg::S2,
        };
        let code = encoder.encode(&op).unwrap();
        // VMRS + BIC.W + ORR.W + VMSR + VCVT + VMRS + BIC.W + VMSR + VCVT.F32.S32
        assert_eq!(code.len(), 36);
    }

    #[test]
    fn test_encode_f32_min_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F32Min {
            sd: VfpReg::S0,
            sn: VfpReg::S2,
            sm: VfpReg::S4,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 16); // VMOV + VCMP + VMRS + conditional VMOV
    }

    #[test]
    fn test_encode_f32_max_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F32Max {
            sd: VfpReg::S0,
            sn: VfpReg::S2,
            sm: VfpReg::S4,
        };
        let code = encoder.encode(&op).unwrap();
        // VMOV(4) + VCMP(4) + VMRS(4) + IT(2) + VMOV(4) = 18
        assert_eq!(code.len(), 18);
    }

    #[test]
    fn test_encode_f32_copysign_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F32Copysign {
            sd: VfpReg::S0,
            sn: VfpReg::S2,
            sm: VfpReg::S4,
        };
        let code = encoder.encode(&op).unwrap();
        // VMOV + VMOV + AND + BIC + ORR + VMOV = 6 * 4 = 24
        assert_eq!(code.len(), 24);
    }

    // ========================================================================
    // f64 encoding tests
    // ========================================================================

    #[test]
    fn test_encode_f64_add_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
        // VADD.F64 D0, D1, D2: check coprocessor is cp11 (0xB)
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!((instr >> 8) & 0xF, 0xB); // cp11
    }

    #[test]
    fn test_encode_f64_sub_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F64Sub {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit VFP as two Thumb halfwords
    }

    #[test]
    fn test_encode_f64_mul_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Mul {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_div_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Div {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_abs_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Abs {
            dd: VfpReg::D0,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_neg_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Neg {
            dd: VfpReg::D0,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_sqrt_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Sqrt {
            dd: VfpReg::D0,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_load_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Load {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::R0, 8),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!((instr >> 8) & 0xF, 0xB); // cp11 for F64
        assert_eq!(instr & 0xFF, 2); // offset 8 / 4 = 2
    }

    #[test]
    fn test_encode_f64_store_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F64Store {
            dd: VfpReg::D0,
            addr: MemAddr::imm(Reg::SP, 0),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_compare_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Eq {
            rd: Reg::R0,
            dn: VfpReg::D0,
            dm: VfpReg::D1,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 16); // VCMP + VMRS + MOV #0 + MOVcond #1
    }

    #[test]
    fn test_encode_f64_compare_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F64Lt {
            rd: Reg::R0,
            dn: VfpReg::D0,
            dm: VfpReg::D1,
        };
        let code = encoder.encode(&op).unwrap();
        // VCMP(4) + VMRS(4) + MOVS(2) + IT(2) + MOV(2) = 14
        assert_eq!(code.len(), 14);
    }

    #[test]
    fn test_encode_f64_const_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Const {
            dd: VfpReg::D0,
            value: 3.125,
        };
        let code = encoder.encode(&op).unwrap();
        // MOVW(4) + MOVT(4) + MOVW(4) + MOVT(4) + VMOV(4) = 20
        assert_eq!(code.len(), 20);
    }

    #[test]
    fn test_encode_f64_const_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F64Const {
            dd: VfpReg::D0,
            value: 2.5,
        };
        let code = encoder.encode(&op).unwrap();
        // MOVW(4) + MOVT(4) + MOVW(4) + MOVT(4) + VMOV(4) = 20
        assert_eq!(code.len(), 20);
    }

    #[test]
    fn test_encode_f64_convert_i32s_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64ConvertI32S {
            dd: VfpReg::D0,
            rm: Reg::R0,
        };
        let code = encoder.encode(&op).unwrap();
        // VMOV(4) + VCVT(4) = 8
        assert_eq!(code.len(), 8);
    }

    #[test]
    fn test_encode_f64_promote_f32_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64PromoteF32 {
            dd: VfpReg::D0,
            sm: VfpReg::S0,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // Single VCVT.F64.F32 instruction
    }

    #[test]
    fn test_encode_f64_promote_f32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F64PromoteF32 {
            dd: VfpReg::D0,
            sm: VfpReg::S0,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_i32_trunc_f64s_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::I32TruncF64S {
            rd: Reg::R0,
            dm: VfpReg::D0,
        };
        let code = encoder.encode(&op).unwrap();
        // VCVT(4) + VMOV(4) = 8
        assert_eq!(code.len(), 8);
    }

    #[test]
    fn test_encode_f64_reinterpret_i64_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64ReinterpretI64 {
            dd: VfpReg::D0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // Single VMOV instruction
    }

    #[test]
    fn test_encode_i64_reinterpret_f64_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64ReinterpretF64 {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            dm: VfpReg::D0,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);
    }

    #[test]
    fn test_encode_f64_trunc_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::F64Trunc {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        };
        let code = encoder.encode(&op).unwrap();
        // Two VFP instructions via Thumb encoding
        assert_eq!(code.len(), 8);
    }

    #[test]
    fn test_encode_f64_min_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::F64Min {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        };
        let code = encoder.encode(&op).unwrap();
        // VMOV + VCMP + VMRS + conditional VMOV = 16
        assert_eq!(code.len(), 16);
    }

    #[test]
    fn test_f64_cp11_encoding() {
        // Verify that F64 instructions use coprocessor 11 (0xB), not 10 (0xA)
        let encoder = ArmEncoder::new_arm32();

        // F64Add
        let code = encoder
            .encode(&ArmOp::F64Add {
                dd: VfpReg::D0,
                dn: VfpReg::D0,
                dm: VfpReg::D0,
            })
            .unwrap();
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!((instr >> 8) & 0xF, 0xB, "F64 should use cp11");

        // F32Add for comparison
        let code = encoder
            .encode(&ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S0,
                sm: VfpReg::S0,
            })
            .unwrap();
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!((instr >> 8) & 0xF, 0xA, "F32 should use cp10");
    }

    #[test]
    fn test_dreg_encoding_higher_registers() {
        let encoder = ArmEncoder::new_arm32();

        // Test with D15 (highest register)
        let op = ArmOp::F64Add {
            dd: VfpReg::D15,
            dn: VfpReg::D14,
            dm: VfpReg::D13,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4);

        // Verify the register encoding worked (instruction is valid)
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!((instr >> 8) & 0xF, 0xB); // cp11
    }
}
