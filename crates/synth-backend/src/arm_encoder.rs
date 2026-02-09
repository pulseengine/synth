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

            // f32 pseudo-instructions (Phase 2) - encode as NOP for now
            // Real compiler would expand to VFP instructions
            ArmOp::F32Add { .. } => 0xE1A00000, // NOP (real: VADD.F32)
            ArmOp::F32Sub { .. } => 0xE1A00000, // NOP (real: VSUB.F32)
            ArmOp::F32Mul { .. } => 0xE1A00000, // NOP (real: VMUL.F32)
            ArmOp::F32Div { .. } => 0xE1A00000, // NOP (real: VDIV.F32)
            ArmOp::F32Abs { .. } => 0xE1A00000, // NOP (real: VABS.F32)
            ArmOp::F32Neg { .. } => 0xE1A00000, // NOP (real: VNEG.F32)
            ArmOp::F32Sqrt { .. } => 0xE1A00000, // NOP (real: VSQRT.F32)
            ArmOp::F32Ceil { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Floor { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Trunc { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Nearest { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Min { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Max { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Copysign { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F32Eq { .. } => 0xE1A00000,  // NOP (real: VCMP.F32 + VMRS)
            ArmOp::F32Ne { .. } => 0xE1A00000,  // NOP
            ArmOp::F32Lt { .. } => 0xE1A00000,  // NOP
            ArmOp::F32Le { .. } => 0xE1A00000,  // NOP
            ArmOp::F32Gt { .. } => 0xE1A00000,  // NOP
            ArmOp::F32Ge { .. } => 0xE1A00000,  // NOP
            ArmOp::F32Const { .. } => 0xE1A00000, // NOP (real: VMOV.F32 or literal pool)
            ArmOp::F32Load { .. } => 0xE1A00000, // NOP (real: VLDR.32)
            ArmOp::F32Store { .. } => 0xE1A00000, // NOP (real: VSTR.32)
            ArmOp::F32ConvertI32S { .. } => 0xE1A00000, // NOP (real: VMOV + VCVT.F32.S32)
            ArmOp::F32ConvertI32U { .. } => 0xE1A00000, // NOP (real: VMOV + VCVT.F32.U32)
            ArmOp::F32ConvertI64S { .. } => 0xE1A00000, // NOP (complex)
            ArmOp::F32ConvertI64U { .. } => 0xE1A00000, // NOP (complex)
            ArmOp::F32ReinterpretI32 { .. } => 0xE1A00000, // NOP (real: VMOV Sd, Rm)
            ArmOp::I32ReinterpretF32 { .. } => 0xE1A00000, // NOP (real: VMOV Rd, Sm)
            ArmOp::I32TruncF32S { .. } => 0xE1A00000, // NOP (real: VCVT.S32.F32 + VMOV)
            ArmOp::I32TruncF32U { .. } => 0xE1A00000, // NOP (real: VCVT.U32.F32 + VMOV)

            // f64 pseudo-instructions (Phase 2c) - encode as NOP for now
            // Real compiler would expand to VFP double-precision instructions
            ArmOp::F64Add { .. } => 0xE1A00000, // NOP (real: VADD.F64)
            ArmOp::F64Sub { .. } => 0xE1A00000, // NOP (real: VSUB.F64)
            ArmOp::F64Mul { .. } => 0xE1A00000, // NOP (real: VMUL.F64)
            ArmOp::F64Div { .. } => 0xE1A00000, // NOP (real: VDIV.F64)
            ArmOp::F64Abs { .. } => 0xE1A00000, // NOP (real: VABS.F64)
            ArmOp::F64Neg { .. } => 0xE1A00000, // NOP (real: VNEG.F64)
            ArmOp::F64Sqrt { .. } => 0xE1A00000, // NOP (real: VSQRT.F64)
            ArmOp::F64Ceil { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Floor { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Trunc { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Nearest { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Min { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Max { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Copysign { .. } => 0xE1A00000, // NOP (pseudo)
            ArmOp::F64Eq { .. } => 0xE1A00000,  // NOP (real: VCMP.F64 + VMRS)
            ArmOp::F64Ne { .. } => 0xE1A00000,  // NOP
            ArmOp::F64Lt { .. } => 0xE1A00000,  // NOP
            ArmOp::F64Le { .. } => 0xE1A00000,  // NOP
            ArmOp::F64Gt { .. } => 0xE1A00000,  // NOP
            ArmOp::F64Ge { .. } => 0xE1A00000,  // NOP
            ArmOp::F64Const { .. } => 0xE1A00000, // NOP (real: VMOV.F64 or literal pool)
            ArmOp::F64Load { .. } => 0xE1A00000, // NOP (real: VLDR.64)
            ArmOp::F64Store { .. } => 0xE1A00000, // NOP (real: VSTR.64)
            ArmOp::F64ConvertI32S { .. } => 0xE1A00000, // NOP (real: VMOV + VCVT.F64.S32)
            ArmOp::F64ConvertI32U { .. } => 0xE1A00000, // NOP (real: VMOV + VCVT.F64.U32)
            ArmOp::F64ConvertI64S { .. } => 0xE1A00000, // NOP (complex)
            ArmOp::F64ConvertI64U { .. } => 0xE1A00000, // NOP (complex)
            ArmOp::F64PromoteF32 { .. } => 0xE1A00000, // NOP (real: VCVT.F64.F32)
            ArmOp::F64ReinterpretI64 { .. } => 0xE1A00000, // NOP (real: VMOV Dd, Rmlo, Rmhi)
            ArmOp::I64ReinterpretF64 { .. } => 0xE1A00000, // NOP (real: VMOV Rdlo, Rdhi, Dm)
            ArmOp::I64TruncF64S { .. } => 0xE1A00000, // NOP (complex)
            ArmOp::I64TruncF64U { .. } => 0xE1A00000, // NOP (complex)
            ArmOp::I32TruncF64S { .. } => 0xE1A00000, // NOP (real: VCVT.S32.F64 + VMOV)
            ArmOp::I32TruncF64U { .. } => 0xE1A00000, // NOP (real: VCVT.U32.F64 + VMOV)
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u32;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u32;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;
                let rm_bits = reg_to_bits(rm) as u32;

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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;
                let rm_bits = reg_to_bits(rm) as u32;

                // Thumb-2 UDIV: FBB0 F0F0 | Rn<<16 | Rd<<8 | Rm
                let hw1: u16 = (0xFBB0 | rn_bits) as u16;
                let hw2: u16 = (0xF0F0 | (rd_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
            }

            // MUL (Thumb-2 32-bit): MUL Rd, Rn, Rm
            ArmOp::Mul { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;
                let rm_bits = reg_to_bits(rm) as u32;

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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;
                let rm_bits = reg_to_bits(rm) as u32;
                let ra_bits = reg_to_bits(ra) as u32;

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
                    let rd_bits = reg_to_bits(rd) as u32;
                    let rn_bits = reg_to_bits(rn) as u32;
                    let rm_bits = reg_to_bits(rm) as u32;

                    // Thumb-2 AND register: EA00 Rn | 0 Rd 00 00 Rm
                    let hw1: u16 = (0xEA00 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | rm_bits) as u16;

                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else if let Operand2::Imm(imm) = op2 {
                    let rd_bits = reg_to_bits(rd) as u32;
                    let rn_bits = reg_to_bits(rn) as u32;
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
                    let rd_bits = reg_to_bits(rd) as u32;
                    let rn_bits = reg_to_bits(rn) as u32;
                    let rm_bits = reg_to_bits(rm) as u32;

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
                    let rd_bits = reg_to_bits(rd) as u32;
                    let rn_bits = reg_to_bits(rn) as u32;
                    let rm_bits = reg_to_bits(rm) as u32;

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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_bits = reg_to_bits(rn) as u32;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rm_bits = reg_to_bits(rm) as u32;

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
                let rd_bits = reg_to_bits(rd) as u32;
                let rm_bits = reg_to_bits(rm) as u32;

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
                let rd_bits = reg_to_bits(rd) as u32;
                let base_bits = reg_to_bits(&addr.base) as u32;

                // Handle register offset mode [base, Roff] or [base, Roff, #imm]
                if let Some(offset_reg) = &addr.offset_reg {
                    let rm_bits = reg_to_bits(offset_reg) as u32;

                    // If there's also an immediate offset, we need to ADD it first
                    if addr.offset != 0 {
                        // Use R12 (IP) as scratch to avoid clobbering the address register
                        // ADD R12, Rm, #offset; LDR Rd, [base, R12]
                        let scratch = Reg::R12;
                        let mut bytes = self.encode_thumb32_add_imm(
                            &scratch,
                            offset_reg,
                            addr.offset as u32,
                        )?;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let base_bits = reg_to_bits(&addr.base) as u32;

                // Handle register offset mode [base, Roff] or [base, Roff, #imm]
                if let Some(offset_reg) = &addr.offset_reg {
                    let rm_bits = reg_to_bits(offset_reg) as u32;

                    // If there's also an immediate offset, we need to ADD it first
                    if addr.offset != 0 {
                        // Use R12 (IP) as scratch to avoid clobbering the address register
                        // ADD R12, Rm, #offset; STR Rd, [base, R12]
                        let scratch = Reg::R12;
                        let mut bytes = self.encode_thumb32_add_imm(
                            &scratch,
                            offset_reg,
                            addr.offset as u32,
                        )?;
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
                let idx_reg = reg_to_bits(table_index_reg) as u32;
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
                let hw1: u16 = (0xEA4F) as u16; // MOV.W R12, Rm, LSL #2
                let hw2: u16 = (0x0C00 | (0b00 << 6) | (0b10 << 4) | (0b00 << 2) | idx_reg) as u16;
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
                if halfword_offset >= -1024 && halfword_offset <= 1022 {
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
                if halfword_offset >= -128 && halfword_offset <= 127 {
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
                        let hw1: u16 = (0xEA6F | 0) as u16;
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
                self.encode_thumb32_movw_raw(reg_to_bits(rd) as u32, *imm16 as u32)
            }

            // MOVT - Move Top (Thumb-2 32-bit)
            ArmOp::Movt { rd, imm16 } => {
                self.encode_thumb32_movt_raw(reg_to_bits(rd) as u32, *imm16 as u32)
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
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
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
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
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
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
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
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
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
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
                        let hw1: u16 = (0xEB70 | rn_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rm_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x3, rd_bits)); // LO = 0x3 (CC)
                    }

                    Condition::HI => {
                        // HI (unsigned GT): swap operands and check LO
                        bytes.extend_from_slice(&encode_cmp_reg(rm_lo, rn_lo));
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                        let hw1: u16 = (0xEB70 | rm_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rn_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x3, rd_bits)); // LO = 0x3 (CC)
                    }

                    Condition::LS => {
                        // LS (unsigned LE): !(a > b) = !(HI), so do HI and invert
                        bytes.extend_from_slice(&encode_cmp_reg(rm_lo, rn_lo));
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                        let hw1: u16 = (0xEB70 | rm_hi_bits) as u16;
                        let hw2: u16 = ((rd_bits as u32) << 8 | rn_hi_bits) as u16;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        bytes.extend_from_slice(&encode_setcond(0x2, rd_bits)); // HS = 0x2 (CS) = !LO
                    }

                    Condition::HS => {
                        // HS (unsigned GE): !(a < b) = !(LO)
                        bytes.extend_from_slice(&encode_cmp_reg(rn_lo, rm_lo));
                        let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                        let rm_hi_bits = reg_to_bits(rm_hi) as u32;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_lo_bits = reg_to_bits(rn_lo) as u32;
                let rn_hi_bits = reg_to_bits(rn_hi) as u32;
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
                let ite_instr: u16 = 0xBF00 | (0x0 << 4) | mask;
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
                let rd_lo_bits = reg_to_bits(rd_lo) as u32;
                let rd_hi_bits = reg_to_bits(rd_hi) as u32;
                let rn_lo_bits = reg_to_bits(rn_lo) as u32;
                let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                let rm_lo_bits = reg_to_bits(rm_lo) as u32;
                let rm_hi_bits = reg_to_bits(rm_hi) as u32;
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
                let rd_lo_bits = reg_to_bits(rd_lo) as u32;
                let rd_hi_bits = reg_to_bits(rd_hi) as u32;
                let rn_lo_bits = reg_to_bits(rn_lo) as u32;
                let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                let rm_lo_bits = reg_to_bits(rm_lo) as u32;
                let rm_hi_bits = reg_to_bits(rm_hi) as u32; // temp
                let mut bytes = Vec::new();

                // AND.W rm_lo, rm_lo, #63  (mask shift amount to 6 bits)
                let hw1: u16 = (0xF000 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_lo_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W rm_hi, rm_lo, #32  (rm_hi = n-32, sets flags)
                let hw1: u16 = (0xF1B0 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (branch if n >= 32, offset = +10 halfwords)
                let bpl: u16 = 0xD50A;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // --- Small shift (n < 32) ---
                // RSB.W rm_hi, rm_lo, #32  (rm_hi = 32-n)
                let hw1: u16 = (0xF1C0 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_hi_bits << 8) | 0x20) as u16;
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
                let rd_lo_bits = reg_to_bits(rd_lo) as u32;
                let rd_hi_bits = reg_to_bits(rd_hi) as u32;
                let rn_lo_bits = reg_to_bits(rn_lo) as u32;
                let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                let rm_lo_bits = reg_to_bits(rm_lo) as u32;
                let rm_hi_bits = reg_to_bits(rm_hi) as u32; // temp
                let mut bytes = Vec::new();

                // AND.W rm_lo, rm_lo, #63
                let hw1: u16 = (0xF000 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_lo_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W rm_hi, rm_lo, #32
                let hw1: u16 = (0xF1B0 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (+10 halfwords)
                let bpl: u16 = 0xD50A;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // --- Small shift (n < 32) ---
                // RSB.W rm_hi, rm_lo, #32  (rm_hi = 32-n)
                let hw1: u16 = (0xF1C0 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_hi_bits << 8) | 0x20) as u16;
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
                let rd_lo_bits = reg_to_bits(rd_lo) as u32;
                let rd_hi_bits = reg_to_bits(rd_hi) as u32;
                let rn_lo_bits = reg_to_bits(rn_lo) as u32;
                let rn_hi_bits = reg_to_bits(rn_hi) as u32;
                let rm_lo_bits = reg_to_bits(rm_lo) as u32;
                let rm_hi_bits = reg_to_bits(rm_hi) as u32; // temp
                let mut bytes = Vec::new();

                // AND.W rm_lo, rm_lo, #63
                let hw1: u16 = (0xF000 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_lo_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W rm_hi, rm_lo, #32
                let hw1: u16 = (0xF1B0 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_hi_bits << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (+10 halfwords)
                let bpl: u16 = 0xD50A;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // --- Small shift (n < 32) ---
                // RSB.W rm_hi, rm_lo, #32
                let hw1: u16 = (0xF1C0 | rm_lo_bits) as u16;
                let hw2: u16 = (0x0000 | (rm_hi_bits << 8) | 0x20) as u16;
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
                let rd_lo_bits = reg_to_bits(rdlo) as u32;
                let rd_hi_bits = reg_to_bits(rdhi) as u32;
                let rn_lo_bits = reg_to_bits(rnlo) as u32;
                let rn_hi_bits = reg_to_bits(rnhi) as u32;
                let shift_bits = reg_to_bits(shift) as u32;
                let r12: u32 = 12; // IP scratch
                let r3: u32 = 3; // Scratch (high word of shift amount, unused)
                let r4: u32 = 4; // Scratch (saved/restored)
                let mut bytes = Vec::new();

                // PUSH {R4}
                bytes.extend_from_slice(&0xB410u16.to_le_bytes());

                // AND.W shift, shift, #63 (mask to 6 bits)
                let hw1: u16 = (0xF000 | shift_bits) as u16;
                let hw2: u16 = (0x0000 | (shift_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W R3, shift, #32 (R3 = n-32, sets flags)
                let hw1: u16 = (0xF1B0 | shift_bits) as u16;
                let hw2: u16 = (0x0000 | (r3 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (branch if n >= 32, offset = +14 halfwords)
                let bpl: u16 = 0xD50E;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // === Small rotation (n < 32) ===
                // RSB.W R3, shift, #32 (R3 = 32-n)
                let hw1: u16 = (0xF1C0 | shift_bits) as u16;
                let hw2: u16 = (0x0000 | (r3 << 8) | 0x20) as u16;
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
                let hw2: u16 = (0x0000 | (r4 << 8) | 0x20) as u16;
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
                let rd_lo_bits = reg_to_bits(rdlo) as u32;
                let rd_hi_bits = reg_to_bits(rdhi) as u32;
                let rn_lo_bits = reg_to_bits(rnlo) as u32;
                let rn_hi_bits = reg_to_bits(rnhi) as u32;
                let shift_bits = reg_to_bits(shift) as u32;
                let r12: u32 = 12;
                let r3: u32 = 3;
                let r4: u32 = 4;
                let mut bytes = Vec::new();

                // PUSH {R4}
                bytes.extend_from_slice(&0xB410u16.to_le_bytes());

                // AND.W shift, shift, #63
                let hw1: u16 = (0xF000 | shift_bits) as u16;
                let hw2: u16 = (0x0000 | (shift_bits << 8) | 0x3F) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // SUBS.W R3, shift, #32
                let hw1: u16 = (0xF1B0 | shift_bits) as u16;
                let hw2: u16 = (0x0000 | (r3 << 8) | 0x20) as u16;
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());

                // BPL .large (+14 halfwords)
                let bpl: u16 = 0xD50E;
                bytes.extend_from_slice(&bpl.to_le_bytes());

                // === Small rotation (n < 32) ===
                // RSB.W R3, shift, #32 (R3 = 32-n)
                let hw1: u16 = (0xF1C0 | shift_bits) as u16;
                let hw2: u16 = (0x0000 | (r3 << 8) | 0x20) as u16;
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
                let hw2: u16 = (0x0000 | (r4 << 8) | 0x20) as u16;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_lo_bits = reg_to_bits(rnlo) as u32;
                let rn_hi_bits = reg_to_bits(rnhi) as u32;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_lo_bits = reg_to_bits(rnlo) as u32;
                let rn_hi_bits = reg_to_bits(rnhi) as u32;
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
                let rd_bits = reg_to_bits(rd) as u32;
                let rn_lo_bits = reg_to_bits(rnlo) as u32;
                let rn_hi_bits = reg_to_bits(rnhi) as u32;
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
                let d_bit = (4 >> 3) & 1;
                let mov: u16 = (0x4600 | (d_bit << 7) | (rn_lo_bits << 3) | (4 & 0x7)) as u16;
                bytes.extend_from_slice(&mov.to_le_bytes());

                // MOV R5, rnhi
                let d_bit = (5 >> 3) & 1;
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
                let rdlo_bits = reg_to_bits(rdlo) as u32;
                let rdhi_bits = reg_to_bits(rdhi) as u32;
                let rnlo_bits = reg_to_bits(rnlo) as u32;
                let mut bytes = Vec::new();

                // SXTB.W rdlo, rnlo (sign-extend byte to 32-bit)
                // SXTB T2: hw1 = 0xFA4F, hw2 = 0xF0<Rd><Rm>
                let hw1: u16 = (0xFA4F) as u16;
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
                let rdlo_bits = reg_to_bits(rdlo) as u32;
                let rdhi_bits = reg_to_bits(rdhi) as u32;
                let rnlo_bits = reg_to_bits(rnlo) as u32;
                let mut bytes = Vec::new();

                // SXTH.W rdlo, rnlo (sign-extend halfword to 32-bit)
                // SXTH T2: hw1 = 0xFA0F, hw2 = 0xF0<Rd><Rm>
                let hw1: u16 = (0xFA0F) as u16;
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
                let rdlo_bits = reg_to_bits(rdlo) as u32;
                let rdhi_bits = reg_to_bits(rdhi) as u32;
                let rnlo_bits = reg_to_bits(rnlo) as u32;
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

            // Default: NOP for unsupported ops
            _ => {
                let instr: u16 = 0xBF00; // NOP
                Ok(instr.to_le_bytes().to_vec())
            }
        }
    }

    // === Thumb-2 32-bit encoding helpers ===

    /// Encode Thumb-2 32-bit ADD with immediate
    fn encode_thumb32_add(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd) as u32;
        let rn_bits = reg_to_bits(rn) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
        let rn_bits = reg_to_bits(rn) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
        let rn_bits = reg_to_bits(rn) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
        let rn_bits = reg_to_bits(rn) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
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
        let rd_bits = reg_to_bits(rd) as u32;
        let rm_bits = reg_to_bits(rm) as u32;
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
        let rd_bits = reg_to_bits(rd) as u32;
        let rn_bits = reg_to_bits(rn) as u32;
        let rm_bits = reg_to_bits(rm) as u32;

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
        let rn_bits = reg_to_bits(rn) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
        let base_bits = reg_to_bits(base) as u32;

        // LDR.W Rd, [Rn, #imm12]
        let hw1: u16 = (0xF8D0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STR
    fn encode_thumb32_str(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd) as u32;
        let base_bits = reg_to_bits(base) as u32;

        // STR.W Rd, [Rn, #imm12]
        let hw1: u16 = (0xF8C0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDR with register offset: LDR.W Rd, [Rn, Rm]
    fn encode_thumb32_ldr_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd) as u32;
        let base_bits = reg_to_bits(base) as u32;
        let rm_bits = reg_to_bits(offset_reg) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
        let base_bits = reg_to_bits(base) as u32;
        let rm_bits = reg_to_bits(offset_reg) as u32;

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
        let rd_bits = reg_to_bits(rd) as u32;
        let rn_bits = reg_to_bits(rn) as u32;

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
}
