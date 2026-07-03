//! ARM Code Encoder - Converts ARM instructions to binary machine code
//!
//! Generates ARM32/Thumb-2 machine code from ARM instruction structures

use synth_core::Result;
use synth_core::target::FPUPrecision;
use synth_synthesis::contracts::encoding as encoding_contracts;
use synth_synthesis::{ArmOp, MemAddr, MveSize, Operand2, QReg, Reg, VfpReg};

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
    /// #206: encode an ARM32 (A32) load/store whose address uses a register
    /// offset (`[rn, rm{, #off}]`). Returns `None` for ops with no register
    /// offset (the caller falls through to the immediate-form arms). Computes
    /// `ip = base + rm` then re-encodes the op against `[ip, #off]`, which works
    /// uniformly for word/byte/halfword/signed forms. IP (R12) is the scratch
    /// register the selector already treats as clobberable across memory ops.
    fn encode_arm_reg_offset_mem(&self, op: &ArmOp) -> Result<Option<Vec<u8>>> {
        use synth_synthesis::Reg;
        let addr = match op {
            ArmOp::Ldr { addr, .. }
            | ArmOp::Str { addr, .. }
            | ArmOp::Ldrb { addr, .. }
            | ArmOp::Strb { addr, .. }
            | ArmOp::Ldrh { addr, .. }
            | ArmOp::Strh { addr, .. }
            | ArmOp::Ldrsb { addr, .. }
            | ArmOp::Ldrsh { addr, .. } => addr,
            _ => return Ok(None),
        };
        let Some(rm) = addr.offset_reg else {
            return Ok(None);
        };
        let ip = Reg::R12;
        // ADD ip, base, rm  (cond=AL, opcode=ADD, S=0, register operand2)
        let add: u32 = 0xE0800000
            | (reg_to_bits(&addr.base) << 16)
            | (reg_to_bits(&ip) << 12)
            | reg_to_bits(&rm);
        let mut bytes = add.to_le_bytes().to_vec();
        // Re-encode the op against [ip, #off] (immediate form → no offset_reg,
        // so this recursion hits the immediate arms, not this helper again).
        let imm_addr = MemAddr::imm(ip, addr.offset);
        let imm_op = match op {
            ArmOp::Ldr { rd, .. } => ArmOp::Ldr {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Str { rd, .. } => ArmOp::Str {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Ldrb { rd, .. } => ArmOp::Ldrb {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Strb { rd, .. } => ArmOp::Strb {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Ldrh { rd, .. } => ArmOp::Ldrh {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Strh { rd, .. } => ArmOp::Strh {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Ldrsb { rd, .. } => ArmOp::Ldrsb {
                rd: *rd,
                addr: imm_addr,
            },
            ArmOp::Ldrsh { rd, .. } => ArmOp::Ldrsh {
                rd: *rd,
                addr: imm_addr,
            },
            _ => unreachable!(),
        };
        bytes.extend(self.encode_arm(&imm_op)?);
        Ok(Some(bytes))
    }

    /// #594: A32 expansion of `ArmOp::CallIndirect` — mirror of the Thumb-2
    /// arm (same contract: R11 holds the function-pointer table base, entry
    /// `i` is a 4-byte code address, R12 is the encoder-scratch register):
    ///
    /// ```text
    /// MOV r12, idx, LSL #2   ; table byte offset
    /// LDR r12, [r11, r12]    ; load function pointer
    /// BLX r12                ; indirect call
    /// ```
    ///
    /// Bounds and type-signature checks are not emitted — parity with the
    /// Thumb-2 path (tracked separately, see #594's note).
    fn encode_arm_call_indirect(table_index_reg: &Reg) -> Vec<u8> {
        let idx = reg_to_bits(table_index_reg);
        let mut bytes = Vec::with_capacity(12);
        // MOV r12, idx, LSL #2 — data-processing MOV, register op2 with
        // imm5=2/LSL: cond=E, opcode=1101, S=0, Rd=r12.
        let mov: u32 = 0xE1A0C000 | (2 << 7) | idx;
        bytes.extend_from_slice(&mov.to_le_bytes());
        // LDR r12, [r11, r12] — register offset, P=1 U=1 B=0 W=0 L=1.
        let ldr: u32 = 0xE79BC00C;
        bytes.extend_from_slice(&ldr.to_le_bytes());
        // BLX r12 — cond=E, 0001 0010 1111 1111 1111 0011, Rm=r12.
        let blx: u32 = 0xE12FFF3C;
        bytes.extend_from_slice(&blx.to_le_bytes());
        bytes
    }

    fn encode_arm(&self, op: &ArmOp) -> Result<Vec<u8>> {
        // #206: ARM32 register-offset loads/stores. `encode_mem_addr` only
        // returns the 12-bit immediate, so the immediate-form arms below
        // silently DROP `addr.offset_reg` — a runtime address index vanished,
        // turning `ldr rd,[rn,rm,#off]` into `ldr rd,[rn,#off]` (the access went
        // to the wrong address). Compute the effective base into IP and re-encode
        // against `[ip, #off]`, which is uniform for word/byte/halfword/signed.
        if let Some(bytes) = self.encode_arm_reg_offset_mem(op)? {
            return Ok(bytes);
        }
        // #594: call_indirect was encoded as a literal NOP on the A32 path
        // (`--target cortex-r5`) — the call never happened and the function
        // silently returned garbage. Emit the same three-instruction expansion
        // as the Thumb-2 path (R11 = function-pointer table base, R12 scratch):
        //   MOV r12, idx, LSL #2 ; LDR r12, [r11, r12] ; BLX r12
        if let ArmOp::CallIndirect {
            table_index_reg, ..
        } = op
        {
            return Ok(Self::encode_arm_call_indirect(table_index_reg));
        }
        let instr: u32 = match op {
            // Data processing instructions
            ArmOp::Add { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

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
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // SUB encoding: opcode=0010
                0xE0400000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            // i64 support: ADDS, ADC, SUBS, SBC for ARM32
            ArmOp::Adds { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // ADDS encoding: opcode=0100, S=1
                0xE0900000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Adc { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // ADC encoding: opcode=0101
                0xE0A00000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Subs { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // SUBS encoding: opcode=0010, S=1
                0xE0500000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Sbc { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

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

            ArmOp::Umull { rdlo, rdhi, rn, rm } => {
                let rdlo_bits = reg_to_bits(rdlo);
                let rdhi_bits = reg_to_bits(rdhi);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);

                // UMULL encoding: cond(4) | 0000 1000 | RdHi(4) | RdLo(4) | Rm(4) | 1001 | Rn(4)
                0xE0800090 | (rdhi_bits << 16) | (rdlo_bits << 12) | (rm_bits << 8) | rn_bits
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

            ArmOp::Mla { rd, rn, rm, ra } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                let ra_bits = reg_to_bits(ra);

                // MLA encoding: cond(4) | 0000001 S | Rd(4) | Ra(4) | Rm(4) | 1001 | Rn(4)
                // Rd = Ra + (Rn * Rm). Base 0xE0200090 (S=0).
                0xE0200090 | (rd_bits << 16) | (ra_bits << 12) | (rm_bits << 8) | rn_bits
            }

            ArmOp::And { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // AND encoding: opcode=0000
                0xE0000000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Orr { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // ORR encoding: opcode=1100
                0xE1800000 | (i_flag << 25) | (rn_bits << 16) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Eor { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

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

            ArmOp::Uxtb { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);
                // UXTB encoding: cond | 01101110 1111 Rd rotate 00 0111 Rm (rotate=00)
                0xE6EF0070 | (rd_bits << 12) | rm_bits
            }

            ArmOp::Uxth { rd, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rm_bits = reg_to_bits(rm);
                // UXTH encoding: cond | 01101111 1111 Rd rotate 00 0111 Rm (rotate=00)
                0xE6FF0070 | (rd_bits << 12) | rm_bits
            }

            // Move instructions
            ArmOp::Mov { rd, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // MOV encoding: opcode=1101
                0xE1A00000 | (i_flag << 25) | (rd_bits << 12) | op2_bits
            }

            ArmOp::Mvn { rd, op2 } => {
                let rd_bits = reg_to_bits(rd);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

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

            // #237: symbol-relative MOVW/MOVT (ARM mode) — addend in place, the
            // backend records the MOVW_ABS/MOVT_ABS relocation against `symbol`.
            ArmOp::MovwSym { rd, addend, .. } => {
                let rd_bits = reg_to_bits(rd);
                let v = (*addend as u32) & 0xffff;
                0xE3000000 | (((v >> 12) & 0xF) << 16) | (rd_bits << 12) | (v & 0xFFF)
            }
            ArmOp::MovtSym { rd, addend, .. } => {
                let rd_bits = reg_to_bits(rd);
                let v = ((*addend as u32) >> 16) & 0xffff;
                0xE3400000 | (((v >> 12) & 0xF) << 16) | (rd_bits << 12) | (v & 0xFFF)
            }

            // #345: LdrSym is the Thumb-2 literal-pool address load. A32 mode is
            // not used for relocatable native-pointer objects; fail loudly rather
            // than miscompile if it is ever reached here.
            ArmOp::LdrSym { .. } => {
                return Err(synth_core::Error::synthesis(
                    "LdrSym (literal-pool address load) is Thumb-2-only",
                ));
            }

            // Compare
            ArmOp::Cmp { rn, op2 } => {
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

                // CMP encoding: opcode=1010, S=1
                0xE1500000 | (i_flag << 25) | (rn_bits << 16) | op2_bits
            }

            // Compare Negative (CMN) - computes Rn + op2 and sets flags
            ArmOp::Cmn { rn, op2 } => {
                let rn_bits = reg_to_bits(rn);
                let (op2_bits, i_flag) = encode_operand2(op2)?;

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

            // Sub-word loads (ARM32 encoding)
            ArmOp::Ldrb { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);
                // LDRB: LDR with B=1 (byte): cond|01|I|P|U|1|W|L|Rn|Rd|offset
                0xE5D00000 | (base_bits << 16) | (rd_bits << 12) | offset_bits
            }

            ArmOp::Ldrsb { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);
                // LDRSB (misc load): cond|000|P|U|1|W|1|Rn|Rd|imm4H|1101|imm4L
                // Simplified with immediate offset
                let offset_val = offset_bits & 0xFF;
                let imm4h = (offset_val >> 4) & 0xF;
                let imm4l = offset_val & 0xF;
                0xE1D000D0 | (base_bits << 16) | (rd_bits << 12) | (imm4h << 8) | imm4l
            }

            ArmOp::Ldrh { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);
                // LDRH (misc load): cond|000|P|U|1|W|1|Rn|Rd|imm4H|1011|imm4L
                let offset_val = offset_bits & 0xFF;
                let imm4h = (offset_val >> 4) & 0xF;
                let imm4l = offset_val & 0xF;
                0xE1D000B0 | (base_bits << 16) | (rd_bits << 12) | (imm4h << 8) | imm4l
            }

            ArmOp::Ldrsh { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);
                // LDRSH (misc load): cond|000|P|U|1|W|1|Rn|Rd|imm4H|1111|imm4L
                let offset_val = offset_bits & 0xFF;
                let imm4h = (offset_val >> 4) & 0xF;
                let imm4l = offset_val & 0xF;
                0xE1D000F0 | (base_bits << 16) | (rd_bits << 12) | (imm4h << 8) | imm4l
            }

            // Sub-word stores (ARM32 encoding)
            ArmOp::Strb { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);
                // STRB: STR with B=1 (byte): cond|01|I|P|U|1|W|0|Rn|Rd|offset
                0xE5C00000 | (base_bits << 16) | (rd_bits << 12) | offset_bits
            }

            ArmOp::Strh { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let (base_bits, offset_bits) = encode_mem_addr(addr);
                // STRH (misc store): cond|000|P|U|1|W|0|Rn|Rd|imm4H|1011|imm4L
                let offset_val = offset_bits & 0xFF;
                let imm4h = (offset_val >> 4) & 0xF;
                let imm4l = offset_val & 0xF;
                0xE1C000B0 | (base_bits << 16) | (rd_bits << 12) | (imm4h << 8) | imm4l
            }

            // Memory management (ARM32 encoding)
            ArmOp::MemorySize { rd } => {
                let rd_bits = reg_to_bits(rd);
                // MOV rd, R10, LSR #16  (memory size in bytes / 65536 = pages)
                // cond|000|1101|S|0000|Rd|shift5|type|0|Rm
                // LSR #16: shift5=10000, type=01
                0xE1A00820 | (rd_bits << 12) | 0x0A // Rm=R10, shift=16, LSR
            }

            ArmOp::MemoryGrow { rd, .. } => {
                let rd_bits = reg_to_bits(rd);
                // On embedded, always fail: MOV rd, #-1
                0xE3E00000 | (rd_bits << 12) // MVN rd, #0 = MOV rd, #-1
            }

            // Label pseudo-instruction: emits no machine code
            ArmOp::Label { .. } => {
                return Ok(Vec::new());
            }

            // Branch instructions
            ArmOp::B { label: _ } => {
                // B encoding: cond(4) | 1010 | offset(24)
                // Simplified: branch to offset 0 (will be patched by linker/resolver)
                0xEA000000
            }

            // Conditional branch to label (generic)
            ArmOp::Bcc { cond, label: _ } => {
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
                // B<cond> with offset 0 (will be patched)
                (cond_bits << 28) | 0x0A000000
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
                // wrapping_sub keeps the encoder total under fuzzing (#186): an
                // extreme i32::MIN offset would otherwise overflow-panic; for any
                // real branch offset this is identical to `- 2`.
                let adjusted_offset = offset.wrapping_sub(2); // Account for PC+8
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
                // wrapping_sub: total under fuzzing (#186), identical for real offsets.
                let adjusted_offset = offset.wrapping_sub(2); // Account for PC+8
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

            ArmOp::Push { regs } => {
                // STMDB SP!, {regs} encoding: cond(4) | 100100 | 10 | 1101 | register_list(16)
                let mut reg_list: u32 = 0;
                for r in regs {
                    reg_list |= 1 << reg_to_bits(r);
                }
                0xE92D0000 | reg_list
            }

            ArmOp::Pop { regs } => {
                // LDMIA SP!, {regs} encoding: cond(4) | 100010 | 11 | 1101 | register_list(16)
                let mut reg_list: u32 = 0;
                for r in regs {
                    reg_list |= 1 << reg_to_bits(r);
                }
                0xE8BD0000 | reg_list
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

            // #594: CallIndirect is expanded to a real multi-instruction
            // sequence by the early return at the top of this function —
            // it must NEVER fall through to a silent NOP again.
            ArmOp::CallIndirect { .. } => {
                unreachable!("CallIndirect handled by encode_arm_call_indirect (#594)")
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
            ArmOp::F32Add { sd, sn, sm } => encode_vfp_3reg(0xEE300A00, sd, sn, sm)?,
            ArmOp::F32Sub { sd, sn, sm } => encode_vfp_3reg(0xEE300A40, sd, sn, sm)?,
            ArmOp::F32Mul { sd, sn, sm } => encode_vfp_3reg(0xEE200A00, sd, sn, sm)?,
            ArmOp::F32Div { sd, sn, sm } => encode_vfp_3reg(0xEE800A00, sd, sn, sm)?,
            ArmOp::F32Abs { sd, sm } => encode_vfp_2reg(0xEEB00AC0, sd, sm)?,
            ArmOp::F32Neg { sd, sm } => encode_vfp_2reg(0xEEB10A40, sd, sm)?,
            ArmOp::F32Sqrt { sd, sm } => encode_vfp_2reg(0xEEB10AC0, sd, sm)?,

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

            ArmOp::F32Load { sd, addr } => encode_vfp_ldst(0xED900A00, sd, addr)?,
            ArmOp::F32Store { sd, addr } => encode_vfp_ldst(0xED800A00, sd, addr)?,

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
            ArmOp::F32ReinterpretI32 { sd, rm } => encode_vmov_core_sreg(true, sd, rm)?,
            ArmOp::I32ReinterpretF32 { rd, sm } => encode_vmov_core_sreg(false, sm, rd)?,
            ArmOp::I32TruncF32S { rd, sm } => {
                return self.encode_arm_i32_trunc_f32(rd, sm, true);
            }
            ArmOp::I32TruncF32U { rd, sm } => {
                return self.encode_arm_i32_trunc_f32(rd, sm, false);
            }

            // f64 VFP double-precision instructions (ARM32)
            // F64 arithmetic: same as F32 but with sz=1 (bit 8 = 1, cp11 = 0xB)
            ArmOp::F64Add { dd, dn, dm } => encode_vfp_3reg_f64(0xEE300B00, dd, dn, dm)?,
            ArmOp::F64Sub { dd, dn, dm } => encode_vfp_3reg_f64(0xEE300B40, dd, dn, dm)?,
            ArmOp::F64Mul { dd, dn, dm } => encode_vfp_3reg_f64(0xEE200B00, dd, dn, dm)?,
            ArmOp::F64Div { dd, dn, dm } => encode_vfp_3reg_f64(0xEE800B00, dd, dn, dm)?,
            ArmOp::F64Abs { dd, dm } => encode_vfp_2reg_f64(0xEEB00BC0, dd, dm)?,
            ArmOp::F64Neg { dd, dm } => encode_vfp_2reg_f64(0xEEB10B40, dd, dm)?,
            ArmOp::F64Sqrt { dd, dm } => encode_vfp_2reg_f64(0xEEB10BC0, dd, dm)?,

            // f64 pseudo-ops
            // FPSCR RMode: 00=nearest, 01=+inf(ceil), 10=-inf(floor), 11=zero(trunc)
            ArmOp::F64Ceil { dd, dm } => {
                return self.encode_arm_f64_rounding(dd, dm, 0b01);
            }
            ArmOp::F64Floor { dd, dm } => {
                return self.encode_arm_f64_rounding(dd, dm, 0b10);
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

            ArmOp::F64Load { dd, addr } => encode_vfp_ldst_f64(0xED900B00, dd, addr)?,
            ArmOp::F64Store { dd, addr } => encode_vfp_ldst_f64(0xED800B00, dd, addr)?,

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
                encode_vmov_core_dreg(true, dd, rmlo, rmhi)?
            }
            ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm } => {
                encode_vmov_core_dreg(false, dm, rdlo, rdhi)?
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

            // MVE instructions — Thumb-2 only (Cortex-M55 is always Thumb-2)
            ArmOp::MveLoad { .. }
            | ArmOp::MveStore { .. }
            | ArmOp::MveConst { .. }
            | ArmOp::MveAnd { .. }
            | ArmOp::MveOrr { .. }
            | ArmOp::MveEor { .. }
            | ArmOp::MveMvn { .. }
            | ArmOp::MveBic { .. }
            | ArmOp::MveAddI { .. }
            | ArmOp::MveSubI { .. }
            | ArmOp::MveMulI { .. }
            | ArmOp::MveNegI { .. }
            | ArmOp::MveCmpEqI { .. }
            | ArmOp::MveCmpNeI { .. }
            | ArmOp::MveCmpLtS { .. }
            | ArmOp::MveCmpLtU { .. }
            | ArmOp::MveCmpGtS { .. }
            | ArmOp::MveCmpGtU { .. }
            | ArmOp::MveCmpLeS { .. }
            | ArmOp::MveCmpLeU { .. }
            | ArmOp::MveCmpGeS { .. }
            | ArmOp::MveCmpGeU { .. }
            | ArmOp::MveDup { .. }
            | ArmOp::MveExtractLane { .. }
            | ArmOp::MveInsertLane { .. }
            | ArmOp::MveAddF32 { .. }
            | ArmOp::MveSubF32 { .. }
            | ArmOp::MveMulF32 { .. }
            | ArmOp::MveNegF32 { .. }
            | ArmOp::MveAbsF32 { .. }
            | ArmOp::MveCmpEqF32 { .. }
            | ArmOp::MveCmpNeF32 { .. }
            | ArmOp::MveCmpLtF32 { .. }
            | ArmOp::MveCmpLeF32 { .. }
            | ArmOp::MveCmpGtF32 { .. }
            | ArmOp::MveCmpGeF32 { .. }
            | ArmOp::MveDupF32 { .. }
            | ArmOp::MveExtractLaneF32 { .. }
            | ArmOp::MveReplaceLaneF32 { .. }
            | ArmOp::MveDivF32 { .. }
            | ArmOp::MveSqrtF32 { .. } => 0xE1A00000, // NOP (MVE = Thumb-2 only)
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
        let sn_num = vfp_sreg_to_num(sn)?;
        let sm_num = vfp_sreg_to_num(sm)?;
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
        let vmov = encode_vmov_core_sreg(true, sd, &Reg::R12)?;
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VMOV + VCVT.F32.S32/U32 as ARM32
    fn encode_arm_f32_convert_i32(&self, sd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV Sd, Rm — move integer to VFP register
        let vmov = encode_vmov_core_sreg(true, sd, rm)?;
        bytes.extend_from_slice(&vmov.to_le_bytes());

        // VCVT.F32.S32 Sd, Sd (signed) or VCVT.F32.U32 Sd, Sd (unsigned)
        // Base: 0xEEB80A40 (signed) or 0xEEB80AC0 (unsigned)
        let sd_num = vfp_sreg_to_num(sd)?;
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
        let sm_num = vfp_sreg_to_num(sm)?;
        let sd_num = vfp_sreg_to_num(sd)?;
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
        let sn_num = vfp_sreg_to_num(sn)?;
        let sm_num = vfp_sreg_to_num(sm)?;
        let sd_num = vfp_sreg_to_num(sd)?;

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
        let vmov_sm = encode_vmov_core_sreg(false, sm, &Reg::R12)?;
        bytes.extend_from_slice(&vmov_sm.to_le_bytes());

        // VMOV R0, Sn (get magnitude source bits) — use R0 as temp
        let vmov_sn = encode_vmov_core_sreg(false, sn, &Reg::R0)?;
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
        let vmov_result = encode_vmov_core_sreg(true, sd, &Reg::R0)?;
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
        let dn_num = vfp_dreg_to_num(dn)?;
        let dm_num = vfp_dreg_to_num(dm)?;
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
        let vmov = encode_vmov_core_dreg(true, dd, &Reg::R0, &Reg::R12)?;
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VMOV Sd, Rm + VCVT.F64.S32/U32 Dd, Sd as ARM32
    fn encode_arm_f64_convert_i32(&self, dd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // Use S0 as intermediate: VMOV S0, Rm
        let vmov = encode_vmov_core_sreg(true, &VfpReg::S0, rm)?;
        bytes.extend_from_slice(&vmov.to_le_bytes());

        // VCVT.F64.S32 Dd, S0 (signed) or VCVT.F64.U32 Dd, S0 (unsigned)
        // Base: 0xEEB80B40 (signed) or 0xEEB80BC0 (unsigned)
        let dd_num = vfp_dreg_to_num(dd)?;
        let (vd, d) = encode_dreg(dd_num);
        let base = if signed { 0xEEB80B40 } else { 0xEEB80BC0 };
        // S0 is register 0: Vm=0, M=0
        let vcvt = base | (d << 22) | (vd << 12);
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VCVT.F64.F32 Dd, Sm as ARM32 (f32 to f64 promotion)
    fn encode_arm_f64_promote_f32(&self, dd: &VfpReg, sm: &VfpReg) -> Result<Vec<u8>> {
        let dd_num = vfp_dreg_to_num(dd)?;
        let sm_num = vfp_sreg_to_num(sm)?;
        let (vd, d) = encode_dreg(dd_num);
        let (vm, m) = encode_sreg(sm_num);

        // VCVT.F64.F32 Dd, Sm: 0xEEB70AC0
        let vcvt = 0xEEB70AC0 | (d << 22) | (vd << 12) | (m << 5) | vm;
        Ok(vcvt.to_le_bytes().to_vec())
    }

    /// Encode VCVT.S32/U32.F64 Sd, Dm + VMOV Rd, Sd as ARM32
    fn encode_arm_i32_trunc_f64(&self, rd: &Reg, dm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm)?;
        let (vm, m) = encode_dreg(dm_num);

        // VCVT.S32.F64 S0, Dm (toward zero) or VCVT.U32.F64 S0, Dm
        // S0: Vd=0, D=0
        let base = if signed { 0xEEBD0BC0 } else { 0xEEBC0BC0 };
        let vcvt = base | (m << 5) | vm;
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        // VMOV Rd, S0
        let vmov = encode_vmov_core_sreg(false, &VfpReg::S0, rd)?;
        bytes.extend_from_slice(&vmov.to_le_bytes());

        Ok(bytes)
    }

    /// Encode F64 rounding pseudo-op as ARM32 via VCVT to integer and back.
    /// Encode F64 rounding as ARM32.
    /// `mode`: FPSCR RMode — 0b00=nearest, 0b01=+inf(ceil), 0b10=-inf(floor), 0b11=zero(trunc)
    ///
    /// For trunc: uses VCVTR.S32.F64 (always truncates).
    /// For ceil/floor/nearest: sets FPSCR rounding mode, uses VCVT.S32.F64 (non-R variant),
    /// then restores FPSCR.
    fn encode_arm_f64_rounding(&self, dd: &VfpReg, dm: &VfpReg, mode: u8) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm)?;
        let dd_num = vfp_dreg_to_num(dd)?;
        let (vm, m) = encode_dreg(dm_num);
        let (vd, d) = encode_dreg(dd_num);

        if mode == 0b11 {
            // Trunc (toward zero): VCVTR.S32.F64 — bit[7]=1, always truncates
            let vcvt_to_int = 0xEEBD0BC0 | (m << 5) | vm;
            bytes.extend_from_slice(&vcvt_to_int.to_le_bytes());
        } else {
            // ceil/floor/nearest: manipulate FPSCR rounding mode
            let rt: u32 = 12;

            // VMRS R12, FPSCR
            let vmrs = 0xEEF10A10 | (rt << 12);
            bytes.extend_from_slice(&vmrs.to_le_bytes());

            // BIC R12, R12, #(3 << 22)
            let bic = 0xE3CC0000 | (rt << 12) | (0x05 << 8) | 0x03;
            bytes.extend_from_slice(&bic.to_le_bytes());

            // ORR R12, R12, #(mode << 22)
            if mode != 0 {
                let orr = 0xE38C0000 | (rt << 12) | (0x05 << 8) | (mode as u32);
                bytes.extend_from_slice(&orr.to_le_bytes());
            }

            // VMSR FPSCR, R12
            let vmsr = 0xEEE10A10 | (rt << 12);
            bytes.extend_from_slice(&vmsr.to_le_bytes());

            // VCVT.S32.F64 S0, Dm — non-R variant (bit[7]=0), uses FPSCR rmode
            let vcvt_to_int = 0xEEBD0B40 | (m << 5) | vm;
            bytes.extend_from_slice(&vcvt_to_int.to_le_bytes());

            // Restore FPSCR
            bytes.extend_from_slice(&vmrs.to_le_bytes());
            bytes.extend_from_slice(&bic.to_le_bytes());
            bytes.extend_from_slice(&vmsr.to_le_bytes());
        }

        // VCVT.F64.S32 Dd, S0 (convert back to double)
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
        let dn_num = vfp_dreg_to_num(dn)?;
        let dm_num = vfp_dreg_to_num(dm)?;
        let dd_num = vfp_dreg_to_num(dd)?;

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
        let vmov_dm = encode_vmov_core_dreg(false, dm, &Reg::R0, &Reg::R12)?;
        bytes.extend_from_slice(&vmov_dm.to_le_bytes());

        // VMOV R1, R2, Dn (get magnitude source bits)
        // We use R1 (lo) and R2 (hi) for the magnitude
        let vmov_dn = encode_vmov_core_dreg(false, dn, &Reg::R1, &Reg::R2)?;
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
        let vmov_result = encode_vmov_core_dreg(true, dd, &Reg::R1, &Reg::R2)?;
        bytes.extend_from_slice(&vmov_result.to_le_bytes());

        Ok(bytes)
    }

    /// Encode VCVT.S32/U32.F32 + VMOV as ARM32
    fn encode_arm_i32_trunc_f32(&self, rd: &Reg, sm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VCVT.S32.F32 Sd, Sm (toward zero) or VCVT.U32.F32 Sd, Sm
        // We use Sm as both source and destination for the intermediate result
        let sm_num = vfp_sreg_to_num(sm)?;
        let (vd, d) = encode_sreg(sm_num);
        let (vm, m) = encode_sreg(sm_num);
        let base = if signed { 0xEEBD0AC0 } else { 0xEEBC0AC0 };
        let vcvt = base | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vcvt.to_le_bytes());

        // VMOV Rd, Sm — move result back to core register
        let vmov = encode_vmov_core_sreg(false, sm, rd)?;
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
                    // 16-bit ADDS only has 3-bit register fields (R0-R7). For
                    // high registers (e.g. R12, the MemLoad/MemStore base
                    // scratch) the bits overflow into adjacent fields, silently
                    // corrupting the operands — issue #178/#180: `add ip,ip,r0`
                    // was emitted as `adds r4,r5,r1`. Guard on all three regs
                    // being low and fall back to 32-bit ADD.W otherwise, exactly
                    // as the Sub handler below does.
                    if rd_bits < 8 && rn_bits < 8 && rm_bits < 8 {
                        // ADDS Rd, Rn, Rm (16-bit): 0001 100 Rm Rn Rd
                        let instr: u16 = 0x1800 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        // ADD.W Rd, Rn, Rm (32-bit) for high registers
                        self.encode_thumb32_add_reg_raw(
                            rd_bits as u32,
                            rn_bits as u32,
                            rm_bits as u32,
                        )
                    }
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

            ArmOp::Push { regs } => {
                // Thumb-2 PUSH encoding:
                // If all regs in R0-R7 + LR, use 16-bit: 1011 010 M rrrrrrrr
                // Otherwise use 32-bit: STMDB SP!, {regs} = 1110 1001 0010 1101 | 0M0 reglist(13)
                let mut reg_list: u16 = 0;
                let mut need_32bit = false;
                for r in regs {
                    let bit = reg_to_bits(r);
                    if bit >= 8 && *r != Reg::LR {
                        need_32bit = true;
                    }
                    reg_list |= 1 << bit;
                }
                if !need_32bit {
                    // 16-bit PUSH: 1011 010 M rrrrrrrr
                    let m_bit = if reg_list & (1 << 14) != 0 {
                        1u16
                    } else {
                        0u16
                    };
                    let low_regs = reg_list & 0xFF;
                    let instr: u16 = 0xB400 | (m_bit << 8) | low_regs;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // 32-bit STMDB SP!, {regs}: E92D | reglist(16)
                    let hw1: u16 = 0xE92D;
                    let hw2: u16 = reg_list;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            ArmOp::Pop { regs } => {
                // Thumb-2 POP encoding:
                // If all regs in R0-R7 + PC, use 16-bit: 1011 110 P rrrrrrrr
                // Otherwise use 32-bit: LDMIA SP!, {regs} = 1110 1000 1011 1101 | PM0 reglist(13)
                let mut reg_list: u16 = 0;
                let mut need_32bit = false;
                for r in regs {
                    let bit = reg_to_bits(r);
                    if bit >= 8 && *r != Reg::PC {
                        need_32bit = true;
                    }
                    reg_list |= 1 << bit;
                }
                if !need_32bit {
                    // 16-bit POP: 1011 110 P rrrrrrrr
                    let p_bit = if reg_list & (1 << 15) != 0 {
                        1u16
                    } else {
                        0u16
                    };
                    let low_regs = reg_list & 0xFF;
                    let instr: u16 = 0xBC00 | (p_bit << 8) | low_regs;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // 32-bit LDMIA SP!, {regs}: E8BD | reglist(16)
                    let hw1: u16 = 0xE8BD;
                    let hw2: u16 = reg_list;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
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
                let bytes = instr.to_le_bytes().to_vec();
                encoding_contracts::verify_thumb16(&bytes);
                Ok(bytes)
            }

            // i64 support: ADDS, ADC, SUBS, SBC for register pair arithmetic
            // ADDS sets flags (carry), ADC uses carry from previous ADDS
            ArmOp::Adds { rd, rn, op2 } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rn_bits = reg_to_bits(rn) as u16;

                if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // 16-bit ADDS is R0-R7 only; i64 pair allocation can place
                    // operands in R8-R11, which would overflow the 3-bit fields
                    // and corrupt the operands (#178/#180 class). Guard and fall
                    // back to 32-bit ADDS.W for high registers.
                    if rd_bits < 8 && rn_bits < 8 && rm_bits < 8 {
                        // ADDS Rd, Rn, Rm (16-bit): 0001 100 Rm Rn Rd
                        let instr: u16 = 0x1800 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        self.encode_thumb32_adds_reg_raw(
                            rd_bits as u32,
                            rn_bits as u32,
                            rm_bits as u32,
                        )
                    }
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
                    // 16-bit SUBS is R0-R7 only; high-register i64 pair operands
                    // would overflow the 3-bit fields (#178/#180 class). Guard
                    // and fall back to 32-bit SUBS.W for high registers.
                    if rd_bits < 8 && rn_bits < 8 && rm_bits < 8 {
                        // SUBS Rd, Rn, Rm (16-bit): 0001 101 Rm Rn Rd
                        let instr: u16 = 0x1A00 | (rm_bits << 6) | (rn_bits << 3) | rd_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        self.encode_thumb32_subs_reg_raw(
                            rd_bits as u32,
                            rn_bits as u32,
                            rm_bits as u32,
                        )
                    }
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
                reg_bits_checked(rd_bits)?;
                reg_bits_checked(rn_bits)?;
                reg_bits_checked(rm_bits)?;

                // Thumb-2 SDIV: FB90 F0F0 | Rn<<16 | Rd<<8 | Rm
                // First halfword: 1111 1011 1001 Rn = 0xFB90 | Rn
                // Second halfword: 1111 Rd 1111 Rm = 0xF0F0 | Rd<<8 | Rm
                let hw1: u16 = (0xFB90 | rn_bits) as u16;
                let hw2: u16 = (0xF0F0 | (rd_bits << 8) | rm_bits) as u16;

                // Thumb-2 32-bit instructions: first halfword, then second halfword (little-endian each)
                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                encoding_contracts::verify_thumb32(&bytes);
                Ok(bytes)
            }

            // UDIV: 11111011 1011 Rn 1111 Rd 1111 Rm
            ArmOp::Udiv { rd, rn, rm } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                reg_bits_checked(rd_bits)?;
                reg_bits_checked(rn_bits)?;
                reg_bits_checked(rm_bits)?;

                // Thumb-2 UDIV: FBB0 F0F0 | Rn<<16 | Rd<<8 | Rm
                let hw1: u16 = (0xFBB0 | rn_bits) as u16;
                let hw2: u16 = (0xF0F0 | (rd_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                encoding_contracts::verify_thumb32(&bytes);
                Ok(bytes)
            }

            ArmOp::Umull { rdlo, rdhi, rn, rm } => {
                let rdlo_bits = reg_to_bits(rdlo);
                let rdhi_bits = reg_to_bits(rdhi);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                reg_bits_checked(rdlo_bits)?;
                reg_bits_checked(rdhi_bits)?;
                reg_bits_checked(rn_bits)?;
                reg_bits_checked(rm_bits)?;

                // Thumb-2 UMULL: 1111 1011 1010 Rn | RdLo RdHi 0000 Rm
                let hw1: u16 = (0xFBA0 | rn_bits) as u16;
                let hw2: u16 = ((rdlo_bits << 12) | (rdhi_bits << 8) | rm_bits) as u16;

                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                encoding_contracts::verify_thumb32(&bytes);
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

            ArmOp::Mla { rd, rn, rm, ra } => {
                let rd_bits = reg_to_bits(rd);
                let rn_bits = reg_to_bits(rn);
                let rm_bits = reg_to_bits(rm);
                let ra_bits = reg_to_bits(ra);

                // Thumb-2 MLA: FB00 Rn | Ra Rd 0000 Rm — same as MLS without the
                // bit-4 (0x10) op flag. rd = ra + rn*rm.
                let hw1: u16 = (0xFB00 | rn_bits) as u16;
                let hw2: u16 = ((ra_bits << 12) | (rd_bits << 8) | rm_bits) as u16;

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

                    // Thumb-2 AND.W immediate T1: 11110 i 0 0000 S Rn | 0 imm3 Rd imm8.
                    // The i:imm3:imm8 field is a ThumbExpandImm modified immediate —
                    // encode it correctly (or error on an un-encodable value)
                    // rather than packing raw bits, closing the silent-miscompile
                    // class for AND alongside ORR/EOR (#251) / ADD/SUB (#253) /
                    // CMP (#255).
                    let field = try_thumb_expand_imm(*imm as u32).ok_or_else(|| {
                        synth_core::Error::synthesis(
                            "AND immediate is not a valid ThumbExpandImm — materialize into a register",
                        )
                    })?;
                    let i_bit = (field >> 11) & 1;
                    let imm3 = (field >> 8) & 0x7;
                    let imm8 = field & 0xFF;

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
                } else if let Operand2::Imm(imm) = op2 {
                    // ORR.W immediate T1: 11110 i 0 0010 S Rn | 0 imm3 Rd imm8.
                    // Only the zero-extended byte form (imm <= 0xFF) is encoded;
                    // larger modified immediates need ThumbExpandImm — return an
                    // error rather than silently emit a NOP (Ok-or-Err, #180/#185).
                    let imm_val = *imm as u32;
                    if imm_val > 0xFF {
                        return Err(synth_core::Error::synthesis(
                            "ORR immediate > 0xFF requires ThumbExpandImm (not yet implemented)",
                        ));
                    }
                    let rd_bits = reg_to_bits(rd);
                    let rn_bits = reg_to_bits(rn);
                    let hw1: u16 = (0xF040 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | (imm_val & 0xFF)) as u16;
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
                } else if let Operand2::Imm(imm) = op2 {
                    // EOR.W immediate T1: 11110 i 0 0100 S Rn | 0 imm3 Rd imm8.
                    // Byte form only (imm <= 0xFF); larger needs ThumbExpandImm —
                    // error, not a silent NOP (Ok-or-Err, #180/#185).
                    let imm_val = *imm as u32;
                    if imm_val > 0xFF {
                        return Err(synth_core::Error::synthesis(
                            "EOR immediate > 0xFF requires ThumbExpandImm (not yet implemented)",
                        ));
                    }
                    let rd_bits = reg_to_bits(rd);
                    let rn_bits = reg_to_bits(rn);
                    let hw1: u16 = (0xF080 | rn_bits) as u16;
                    let hw2: u16 = ((rd_bits << 8) | (imm_val & 0xFF)) as u16;
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

            // UXTB Rd,Rm — zero-extend byte (rd = rm & 0xff)
            ArmOp::Uxtb { rd, rm } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rm_bits = reg_to_bits(rm) as u16;
                if rd_bits < 8 && rm_bits < 8 {
                    // UXTB Rd, Rm (16-bit): 1011 0010 11 Rm Rd
                    let instr: u16 = 0xB2C0 | (rm_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // Thumb-2 UXTB.W: FA5F F(rd)80 (rm)
                    let hw1: u16 = 0xFA5F;
                    let hw2: u16 = (0xF080 | ((rd_bits as u32) << 8) | rm_bits as u32) as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // UXTH Rd,Rm — zero-extend halfword (rd = rm & 0xffff)
            ArmOp::Uxth { rd, rm } => {
                let rd_bits = reg_to_bits(rd) as u16;
                let rm_bits = reg_to_bits(rm) as u16;
                if rd_bits < 8 && rm_bits < 8 {
                    // UXTH Rd, Rm (16-bit): 1011 0010 10 Rm Rd
                    let instr: u16 = 0xB280 | (rm_bits << 3) | rd_bits;
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // Thumb-2 UXTH.W: FA1F F(rd)80 (rm)
                    let hw1: u16 = 0xFA1F;
                    let hw2: u16 = (0xF080 | ((rd_bits as u32) << 8) | rm_bits as u32) as u16;
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
                    // CMN.W Rn, #imm (32-bit): i:imm3:imm8 is a ThumbExpandImm
                    // modified immediate (the field sits in imm3=hw2[14:12],
                    // imm8=hw2[7:0], i=hw1[10]). Encode it correctly, or error on
                    // an un-encodable value — replacing the old silent `0xBF00`
                    // NOP (the last of the silent-miscompile data-proc encoders).
                    let field = try_thumb_expand_imm(*imm as u32).ok_or_else(|| {
                        synth_core::Error::synthesis(
                            "CMN immediate is not a valid ThumbExpandImm — materialize into a register",
                        )
                    })?;
                    let i_bit = (field >> 11) & 1;
                    let imm3 = (field >> 8) & 0x7;
                    let imm8 = field & 0xFF;
                    let hw1: u16 = (0xF110 | (i_bit << 10) as u16) | rn_bits;
                    let hw2: u16 = (imm3 << 12) as u16 | 0x0F00 | imm8 as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                } else if let Operand2::Reg(rm) = op2 {
                    let rm_bits = reg_to_bits(rm) as u16;
                    // 16-bit CMN (T1) only encodes R0-R7; high registers overflow
                    // the 3-bit fields and corrupt the operands (#184, the #180
                    // class). CMN has no high-register 16-bit form, so fall back
                    // to 32-bit CMN.W (T2): EB10 Rn | 0F00 Rm (ADD.W with S=1 and
                    // Rd discarded as PC/1111).
                    if rn_bits < 8 && rm_bits < 8 {
                        // CMN Rn, Rm (16-bit): 0100 0010 11 Rm Rn
                        let instr: u16 = 0x42C0 | (rm_bits << 3) | rn_bits;
                        Ok(instr.to_le_bytes().to_vec())
                    } else {
                        let hw1: u16 = 0xEB10 | rn_bits;
                        let hw2: u16 = 0x0F00 | rm_bits;
                        let mut bytes = hw1.to_le_bytes().to_vec();
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                        Ok(bytes)
                    }
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

            // LDRB (Thumb-2)
            ArmOp::Ldrb { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                if let Some(offset_reg) = &addr.offset_reg {
                    if addr.offset != 0 {
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_ldrb_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }
                    return self.encode_thumb32_ldrb_reg(rd, &addr.base, offset_reg);
                }

                let offset = addr.offset as u32;
                if rd_bits < 8 && base_bits < 8 && offset <= 31 {
                    // LDRB Rd, [Rn, #imm5] (16-bit): 0111 1 imm5 Rn Rd
                    let instr: u16 = 0x7800
                        | ((offset as u16) << 6)
                        | ((base_bits as u16) << 3)
                        | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_ldrb_imm(rd, &addr.base, offset)
                }
            }

            // LDRSB (Thumb-2)
            ArmOp::Ldrsb { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                if let Some(offset_reg) = &addr.offset_reg {
                    if addr.offset != 0 {
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_ldrsb_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }
                    return self.encode_thumb32_ldrsb_reg(rd, &addr.base, offset_reg);
                }

                let offset = addr.offset as u32;
                // LDRSB has no 16-bit immediate form (only register)
                // For 16-bit reg form: only if Rd, Rn, Rm < R8
                if rd_bits < 8 && base_bits < 8 && offset == 0 {
                    // No immediate 16-bit encoding for LDRSB; use 32-bit
                    self.encode_thumb32_ldrsb_imm(rd, &addr.base, offset)
                } else {
                    self.encode_thumb32_ldrsb_imm(rd, &addr.base, offset)
                }
            }

            // LDRH (Thumb-2)
            ArmOp::Ldrh { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                if let Some(offset_reg) = &addr.offset_reg {
                    if addr.offset != 0 {
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_ldrh_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }
                    return self.encode_thumb32_ldrh_reg(rd, &addr.base, offset_reg);
                }

                let offset = addr.offset as u32;
                if rd_bits < 8 && base_bits < 8 && (offset & 0x1) == 0 && offset <= 62 {
                    // LDRH Rd, [Rn, #imm5*2] (16-bit): 1000 1 imm5 Rn Rd
                    let imm5 = (offset >> 1) as u16;
                    let instr: u16 =
                        0x8800 | (imm5 << 6) | ((base_bits as u16) << 3) | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_ldrh_imm(rd, &addr.base, offset)
                }
            }

            // LDRSH (Thumb-2)
            ArmOp::Ldrsh { rd, addr } => {
                if let Some(offset_reg) = &addr.offset_reg {
                    if addr.offset != 0 {
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_ldrsh_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }
                    return self.encode_thumb32_ldrsh_reg(rd, &addr.base, offset_reg);
                }

                let offset = addr.offset as u32;
                self.encode_thumb32_ldrsh_imm(rd, &addr.base, offset)
            }

            // STRB (Thumb-2)
            ArmOp::Strb { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                if let Some(offset_reg) = &addr.offset_reg {
                    if addr.offset != 0 {
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_strb_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }
                    return self.encode_thumb32_strb_reg(rd, &addr.base, offset_reg);
                }

                let offset = addr.offset as u32;
                if rd_bits < 8 && base_bits < 8 && offset <= 31 {
                    // STRB Rd, [Rn, #imm5] (16-bit): 0111 0 imm5 Rn Rd
                    let instr: u16 = 0x7000
                        | ((offset as u16) << 6)
                        | ((base_bits as u16) << 3)
                        | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_strb_imm(rd, &addr.base, offset)
                }
            }

            // STRH (Thumb-2)
            ArmOp::Strh { rd, addr } => {
                let rd_bits = reg_to_bits(rd);
                let base_bits = reg_to_bits(&addr.base);

                if let Some(offset_reg) = &addr.offset_reg {
                    if addr.offset != 0 {
                        let scratch = Reg::R12;
                        let mut bytes =
                            self.encode_thumb32_add_imm(&scratch, offset_reg, addr.offset as u32)?;
                        bytes.extend(self.encode_thumb32_strh_reg(rd, &addr.base, &scratch)?);
                        return Ok(bytes);
                    }
                    return self.encode_thumb32_strh_reg(rd, &addr.base, offset_reg);
                }

                let offset = addr.offset as u32;
                if rd_bits < 8 && base_bits < 8 && (offset & 0x1) == 0 && offset <= 62 {
                    // STRH Rd, [Rn, #imm5*2] (16-bit): 1000 0 imm5 Rn Rd
                    let imm5 = (offset >> 1) as u16;
                    let instr: u16 =
                        0x8000 | (imm5 << 6) | ((base_bits as u16) << 3) | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    self.encode_thumb32_strh_imm(rd, &addr.base, offset)
                }
            }

            // MemorySize (Thumb-2)
            ArmOp::MemorySize { rd } => {
                // LSR rd, R10, #16 — memory size in bytes / 65536 = pages
                // Thumb-2 16-bit: LSRS Rd, Rm, #imm5 — 0000 1 imm5 Rm Rd
                let rd_bits = reg_to_bits(rd);
                let r10_bits = reg_to_bits(&Reg::R10);
                if rd_bits < 8 && r10_bits < 8 {
                    let instr: u16 =
                        0x0800 | (16u16 << 6) | ((r10_bits as u16) << 3) | (rd_bits as u16);
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // Thumb-2 32-bit LSR: 1110 1010 010 0 1111 | 0 imm3 Rd imm2 01 Rm
                    let imm5: u32 = 16;
                    let imm3 = (imm5 >> 2) & 0x7;
                    let imm2 = imm5 & 0x3;
                    let hw1: u16 = 0xEA4F;
                    let hw2: u16 =
                        ((imm3 << 12) | (rd_bits << 8) | (imm2 << 6) | 0x10 | r10_bits) as u16;
                    let mut bytes = hw1.to_le_bytes().to_vec();
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok(bytes)
                }
            }

            // MemoryGrow (Thumb-2)
            ArmOp::MemoryGrow { rd, .. } => {
                // On embedded with fixed memory, always return -1 (failure)
                // MVN rd, #0 → MOV rd, #-1
                // Thumb-2 32-bit: MVN: 1111 0 i 0 0 0 1 1 0 1111 | 0 imm3 Rd imm8
                let rd_bits = reg_to_bits(rd);
                let hw1: u16 = 0xF06F; // MVN with i=0
                let hw2: u16 = (rd_bits << 8) as u16; // imm8=0 → ~0 = 0xFFFFFFFF = -1
                let mut bytes = hw1.to_le_bytes().to_vec();
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
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
                // LSL: type=00 (bits 5:4), imm5=2 -> imm3=000, imm2=10 (bits 7:6)
                // #597: the shift amount was previously shifted into bits 5:4 —
                // the TYPE field — encoding `mov.w ip, rm, ASR #32`, which
                // destroyed the index and dispatched table entry 0 for every
                // call. imm2 lives at bits 7:6.
                let hw1: u16 = 0xEA4F_u16; // MOV.W R12, Rm, LSL #2
                let hw2: u16 = ((0x0C00 | (0b10 << 6)) | idx_reg) as u16;
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

            // Label pseudo-instruction: emits no machine code
            ArmOp::Label { .. } => Ok(Vec::new()),

            // Conditional branch to label (generic) - offset 0, will be patched
            ArmOp::Bcc { cond, label: _ } => {
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
                // 16-bit B<cond> with offset 0: 1101 cond imm8
                let instr: u16 = 0xD000 | (cond_bits << 8);
                Ok(instr.to_le_bytes().to_vec())
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

                    // The B.W (T4) encoding packs the signed offset as:
                    //   S:I1:I2:imm10:imm11:0  (25-bit signed, halfword-aligned)
                    // where J1 = NOT(I1 XOR S), J2 = NOT(I2 XOR S)
                    // Input halfword_offset already equals (target - PC - 4) / 2,
                    // so the full byte offset = halfword_offset << 1.
                    // The encoding fields split that 25-bit signed value (including the
                    // implicit trailing zero) as: S | imm10 | imm11
                    // with I1 = bit 23 and I2 = bit 22 of the signed offset.
                    let signed_offset = halfword_offset << 1; // byte offset
                    let s = if signed_offset < 0 { 1u32 } else { 0u32 };
                    let uoffset = signed_offset as u32;
                    let imm10 = (uoffset >> 12) & 0x3FF; // bits [21:12]
                    let imm11 = (uoffset >> 1) & 0x7FF; // bits [11:1]
                    let i1 = (uoffset >> 23) & 1; // bit 23
                    let i2 = (uoffset >> 22) & 1; // bit 22
                    let j1 = (!(i1 ^ s)) & 1; // J1 = NOT(I1 XOR S)
                    let j2 = (!(i2 ^ s)) & 1; // J2 = NOT(I2 XOR S)

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
                // BL is always 32-bit in Thumb-2, encoded here as a relocatable
                // placeholder; an R_ARM_THM_CALL relocation patches the target
                // (see arm_backend.rs). The placeholder must carry an embedded
                // addend of -4 so the relocation nets to exactly the symbol S.
                //
                // Thumb BL computes `target = (P + 4) + signed_offset`. Under
                // R_ARM_THM_CALL the linker resolves using the in-place addend;
                // a 0xF800 placeholder (addend 0) lands at S+4 — every call one
                // instruction past the callee entry (#174). The correct
                // placeholder is what `gas` emits for `bl <extern>`:
                //   f7ff fffe  ->  `bl <self>`  (S=1, J1=J2=1, imm = -4 addend),
                // i.e. hw1=0xF7FF, hw2=0xFFFE. This nets to S, not S+4.
                // (The earlier 0xD000 was worse still — a ~+0x600000 addend,
                // the garbage `bl c0000c` and "truncated to fit" of #167.)
                let hw1: u16 = 0xF7FF;
                let hw2: u16 = 0xFFFE;
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

            // #237: symbol-relative MOVW/MOVT. Encode the addend's low/high 16
            // bits in place; the backend records an R_ARM_MOVW_ABS_NC /
            // R_ARM_MOVT_ABS relocation against `symbol`, so the linker adds the
            // symbol's final address to the in-place addend (REL semantics).
            ArmOp::MovwSym { rd, addend, .. } => {
                self.encode_thumb32_movw_raw(reg_to_bits(rd), (*addend as u32) & 0xffff)
            }
            ArmOp::MovtSym { rd, addend, .. } => {
                self.encode_thumb32_movt_raw(reg_to_bits(rd), ((*addend as u32) >> 16) & 0xffff)
            }

            // #345: literal-pool address load — emit a PLACEHOLDER `LDR.W rd,
            // [pc, #0]` (U=1, imm12=0). The backend (arm_backend.rs) places the
            // 4-byte pool word at the end of the function, records the R_ARM_ABS32
            // relocation against `symbol+addend`, and patches the imm12 with the
            // real PC-relative distance once the pool offset is known.
            // Encoding T2: 1111 1000 1101 1111 | Rt(4) imm12(12), with the literal
            // base = Align(PC,4) and PC = address of this instruction + 4.
            ArmOp::LdrSym { rd, .. } => {
                let rt = reg_to_bits(rd) as u16;
                let hw1: u16 = 0xF8DF; // LDR.W (literal), U=1
                let hw2: u16 = rt << 12; // imm12 = 0 placeholder
                let mut bytes = Vec::with_capacity(4);
                bytes.extend_from_slice(&hw1.to_le_bytes());
                bytes.extend_from_slice(&hw2.to_le_bytes());
                Ok(bytes)
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

                // Materialize 0/1 into Rd. The 16-bit MOVS (T1) encodes Rd in a
                // 3-bit field (bits[10:8]) — only R0–R7. For a high register
                // (R8–R12) `rd_bits << 8` overflows into bit 11 and silently
                // turns MOVS into CMP (00100 → 00101), corrupting the result
                // (this mis-materialized gale's `has_waiter`, so its `local.set`
                // stored a stale register → the binary-sem WAKE dispatch read
                // garbage). Use the 32-bit MOV.W (T2) for high registers, which
                // has a 4-bit Rd field. MOV.W with S=0 doesn't set flags, which
                // is fine inside the ITE (the materialized value is the result;
                // the flags are not consumed afterwards).
                let mut bytes = ite_instr.to_le_bytes().to_vec();
                let push_mov = |bytes: &mut Vec<u8>, imm: u16| {
                    if rd_bits <= 7 {
                        let m: u16 = 0x2000 | (rd_bits << 8) | imm; // 16-bit MOVS Rd,#imm
                        bytes.extend_from_slice(&m.to_le_bytes());
                    } else {
                        // 32-bit MOV.W Rd, #imm (T2): F04F | (Rd<<8) | imm8
                        let hw1: u16 = 0xF04F;
                        let hw2: u16 = (rd_bits << 8) | imm;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                    }
                };
                push_mov(&mut bytes, 1); // Then branch (condition true)  → 1
                push_mov(&mut bytes, 0); // Else branch (condition false) → 0
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
                    if rd_bits < 8 {
                        let mov_one: u16 = 0x2001 | (rd_bits << 8);
                        let mov_zero: u16 = 0x2000 | (rd_bits << 8);
                        b.extend_from_slice(&mov_one.to_le_bytes());
                        b.extend_from_slice(&mov_zero.to_le_bytes());
                    } else {
                        // #311: rd >= R8 — the 16-bit MOV imm8 form has a 3-bit
                        // rd field; rd_bits<<8 overflows into bit 11 and
                        // TRANSMUTES the MOV into CMP (0x2001|0x0800 = 0x2801 =
                        // CMP r0,#1): the boolean dies in the flags and the
                        // consumer reads a stale register. Use the 32-bit
                        // MOV.W (T2: F04F 0000|rd<<8|imm8) — IT-legal,
                        // flag-preserving. Same class as H-CODE-9 / #180.
                        for imm in [1u16, 0u16] {
                            let hw1: u16 = 0xF04F;
                            let hw2: u16 = (rd_bits << 8) | imm;
                            b.extend_from_slice(&hw1.to_le_bytes());
                            b.extend_from_slice(&hw2.to_le_bytes());
                        }
                    }
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

                // CMP rd, #0 — 16-bit form only for r0-r7 (3-bit rd field);
                // high registers take CMP.W (T2: F1B0|rn 0F00|imm8). This was
                // H-CODE-9: rd_bits<<8 overflowing the field compared the
                // WRONG register. Same hardening as the #311 SetCond fix.
                if rd_bits < 8 {
                    let cmp_instr: u16 = 0x2800 | ((rd_bits as u16) << 8);
                    bytes.extend_from_slice(&cmp_instr.to_le_bytes());
                } else {
                    let hw1: u16 = 0xF1B0 | (rd_bits as u16);
                    let hw2: u16 = 0x0F00;
                    bytes.extend_from_slice(&hw1.to_le_bytes());
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                }

                // ITE EQ; MOV rd, #1; MOV rd, #0 (32-bit MOV.W for rd >= R8,
                // #311 — see I64SetCond)
                let mask = 0xC_u16; // ITE EQ mask: firstcond[0]=0, mask=0xC
                let ite_instr: u16 = 0xBF00 | mask;
                bytes.extend_from_slice(&ite_instr.to_le_bytes());
                if rd_bits < 8 {
                    let mov_one: u16 = 0x2001 | ((rd_bits as u16) << 8);
                    let mov_zero: u16 = 0x2000 | ((rd_bits as u16) << 8);
                    bytes.extend_from_slice(&mov_one.to_le_bytes());
                    bytes.extend_from_slice(&mov_zero.to_le_bytes());
                } else {
                    for imm in [1u16, 0u16] {
                        let hw1: u16 = 0xF04F;
                        let hw2: u16 = ((rd_bits as u16) << 8) | imm;
                        bytes.extend_from_slice(&hw1.to_le_bytes());
                        bytes.extend_from_slice(&hw2.to_le_bytes());
                    }
                }

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

                // PUSH {R4-R7} - save scratch registers (NO LR — this is inline code)
                // 16-bit PUSH: 1011 010 M rrrrrrrr where M=0 (no LR), r=R4-R7 = 0xF0
                // Encoding: 1011 0100 1111 0000 = 0xB4F0
                bytes.extend_from_slice(&0xB4F0u16.to_le_bytes());

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

                // POP {R4-R7} - restore scratch registers (NO PC — inline code continues)
                // 16-bit POP: 1011 110 P rrrrrrrr where P=0 (no PC), r=R4-R7 = 0xF0
                // Encoding: 1011 1100 1111 0000 = 0xBCF0
                bytes.extend_from_slice(&0xBCF0u16.to_le_bytes());

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

                // PUSH {R4-R11} - save scratch registers (NO LR — inline code)
                bytes.extend_from_slice(&0xE92Du16.to_le_bytes());
                bytes.extend_from_slice(&0x0FF0u16.to_le_bytes());

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

                // POP {R4-R11} - restore scratch registers (NO PC — inline code continues)
                bytes.extend_from_slice(&0xE8BDu16.to_le_bytes());
                bytes.extend_from_slice(&0x0FF0u16.to_le_bytes());

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

                // PUSH {R4-R8} - save scratch registers (NO LR — inline code)
                bytes.extend_from_slice(&0xE92Du16.to_le_bytes());
                bytes.extend_from_slice(&0x01F0u16.to_le_bytes());

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

                // POP {R4-R8} - restore scratch registers (NO PC — inline code continues)
                bytes.extend_from_slice(&0xE8BDu16.to_le_bytes());
                bytes.extend_from_slice(&0x01F0u16.to_le_bytes());

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

                // PUSH {R4-R11} - save scratch registers (NO LR — inline code)
                bytes.extend_from_slice(&0xE92Du16.to_le_bytes());
                bytes.extend_from_slice(&0x0FF0u16.to_le_bytes());

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

                // POP {R4-R11} - restore scratch registers (NO PC — inline code continues)
                bytes.extend_from_slice(&0xE8BDu16.to_le_bytes());
                bytes.extend_from_slice(&0x0FF0u16.to_le_bytes());

                Ok(bytes)
            }

            // === F32 VFP single-precision Thumb-2 encodings ===
            // VFP instruction words are identical to ARM32; emit as two LE halfwords.
            ArmOp::F32Add { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE300A00, sd, sn, sm)?))
            }
            ArmOp::F32Sub { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE300A40, sd, sn, sm)?))
            }
            ArmOp::F32Mul { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE200A00, sd, sn, sm)?))
            }
            ArmOp::F32Div { sd, sn, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_3reg(0xEE800A00, sd, sn, sm)?))
            }
            ArmOp::F32Abs { sd, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg(0xEEB00AC0, sd, sm)?))
            }
            ArmOp::F32Neg { sd, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg(0xEEB10A40, sd, sm)?))
            }
            ArmOp::F32Sqrt { sd, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg(0xEEB10AC0, sd, sm)?))
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
                Ok(vfp_to_thumb_bytes(encode_vfp_ldst(0xED900A00, sd, addr)?))
            }
            ArmOp::F32Store { sd, addr } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_ldst(0xED800A00, sd, addr)?))
            }

            ArmOp::F32ConvertI32S { sd, rm } => self.encode_thumb_f32_convert_i32(sd, rm, true),
            ArmOp::F32ConvertI32U { sd, rm } => self.encode_thumb_f32_convert_i32(sd, rm, false),
            ArmOp::F32ConvertI64S { .. } | ArmOp::F32ConvertI64U { .. } => {
                Err(synth_core::Error::synthesis(
                    "F32 i64 conversion not supported (requires register pairs on 32-bit ARM)",
                ))
            }
            ArmOp::F32ReinterpretI32 { sd, rm } => {
                Ok(vfp_to_thumb_bytes(encode_vmov_core_sreg(true, sd, rm)?))
            }
            ArmOp::I32ReinterpretF32 { rd, sm } => {
                Ok(vfp_to_thumb_bytes(encode_vmov_core_sreg(false, sm, rd)?))
            }
            ArmOp::I32TruncF32S { rd, sm } => self.encode_thumb_i32_trunc_f32(rd, sm, true),
            ArmOp::I32TruncF32U { rd, sm } => self.encode_thumb_i32_trunc_f32(rd, sm, false),

            // === F64 VFP double-precision Thumb-2 encodings ===
            // VFP instruction words are identical to ARM32; emit as two LE halfwords.
            ArmOp::F64Add { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE300B00, dd, dn, dm,
            )?)),
            ArmOp::F64Sub { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE300B40, dd, dn, dm,
            )?)),
            ArmOp::F64Mul { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE200B00, dd, dn, dm,
            )?)),
            ArmOp::F64Div { dd, dn, dm } => Ok(vfp_to_thumb_bytes(encode_vfp_3reg_f64(
                0xEE800B00, dd, dn, dm,
            )?)),
            ArmOp::F64Abs { dd, dm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg_f64(0xEEB00BC0, dd, dm)?))
            }
            ArmOp::F64Neg { dd, dm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg_f64(0xEEB10B40, dd, dm)?))
            }
            ArmOp::F64Sqrt { dd, dm } => {
                Ok(vfp_to_thumb_bytes(encode_vfp_2reg_f64(0xEEB10BC0, dd, dm)?))
            }

            // f64 pseudo-ops
            // FPSCR RMode: 00=nearest, 01=+inf(ceil), 10=-inf(floor), 11=zero(trunc)
            ArmOp::F64Ceil { dd, dm } => self.encode_thumb_f64_rounding(dd, dm, 0b01),
            ArmOp::F64Floor { dd, dm } => self.encode_thumb_f64_rounding(dd, dm, 0b10),
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
            )?)),
            ArmOp::F64Store { dd, addr } => Ok(vfp_to_thumb_bytes(encode_vfp_ldst_f64(
                0xED800B00, dd, addr,
            )?)),

            ArmOp::F64ConvertI32S { dd, rm } => self.encode_thumb_f64_convert_i32(dd, rm, true),
            ArmOp::F64ConvertI32U { dd, rm } => self.encode_thumb_f64_convert_i32(dd, rm, false),
            ArmOp::F64ConvertI64S { .. } | ArmOp::F64ConvertI64U { .. } => {
                Err(synth_core::Error::synthesis(
                    "F64 i64 conversion not supported (requires register pairs on 32-bit ARM)",
                ))
            }
            ArmOp::F64PromoteF32 { dd, sm } => self.encode_thumb_f64_promote_f32(dd, sm),
            ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi } => Ok(vfp_to_thumb_bytes(
                encode_vmov_core_dreg(true, dd, rmlo, rmhi)?,
            )),
            ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm } => Ok(vfp_to_thumb_bytes(
                encode_vmov_core_dreg(false, dm, rdlo, rdhi)?,
            )),
            ArmOp::I64TruncF64S { .. } | ArmOp::I64TruncF64U { .. } => {
                Err(synth_core::Error::synthesis(
                    "i64 truncation from F64 not supported (requires i64 register pairs on 32-bit ARM)",
                ))
            }
            ArmOp::I32TruncF64S { rd, dm } => self.encode_thumb_i32_trunc_f64(rd, dm, true),
            ArmOp::I32TruncF64U { rd, dm } => self.encode_thumb_i32_trunc_f64(rd, dm, false),

            // ===== i64 operations: encode as multi-instruction Thumb-2 sequences =====

            // I64Add: ADDS rdlo, rnlo, rmlo; ADC.W rdhi, rnhi, rmhi
            ArmOp::I64Add {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let mut bytes = Vec::new();
                // ADDS rdlo, rnlo, rmlo (16-bit)
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Adds {
                    rd: *rdlo,
                    rn: *rnlo,
                    op2: Operand2::Reg(*rmlo),
                })?);
                // ADC.W rdhi, rnhi, rmhi (32-bit)
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Adc {
                    rd: *rdhi,
                    rn: *rnhi,
                    op2: Operand2::Reg(*rmhi),
                })?);
                Ok(bytes)
            }

            // I64Sub: SUBS rdlo, rnlo, rmlo; SBC.W rdhi, rnhi, rmhi
            ArmOp::I64Sub {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let mut bytes = Vec::new();
                // SUBS rdlo, rnlo, rmlo (16-bit)
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Subs {
                    rd: *rdlo,
                    rn: *rnlo,
                    op2: Operand2::Reg(*rmlo),
                })?);
                // SBC.W rdhi, rnhi, rmhi (32-bit)
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Sbc {
                    rd: *rdhi,
                    rn: *rnhi,
                    op2: Operand2::Reg(*rmhi),
                })?);
                Ok(bytes)
            }

            // I64And: AND rdlo, rnlo, rmlo; AND rdhi, rnhi, rmhi
            ArmOp::I64And {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let mut bytes = Vec::new();
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::And {
                    rd: *rdlo,
                    rn: *rnlo,
                    op2: Operand2::Reg(*rmlo),
                })?);
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::And {
                    rd: *rdhi,
                    rn: *rnhi,
                    op2: Operand2::Reg(*rmhi),
                })?);
                Ok(bytes)
            }

            // I64Or: ORR rdlo, rnlo, rmlo; ORR rdhi, rnhi, rmhi
            ArmOp::I64Or {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let mut bytes = Vec::new();
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Orr {
                    rd: *rdlo,
                    rn: *rnlo,
                    op2: Operand2::Reg(*rmlo),
                })?);
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Orr {
                    rd: *rdhi,
                    rn: *rnhi,
                    op2: Operand2::Reg(*rmhi),
                })?);
                Ok(bytes)
            }

            // I64Xor: EOR rdlo, rnlo, rmlo; EOR rdhi, rnhi, rmhi
            ArmOp::I64Xor {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let mut bytes = Vec::new();
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Eor {
                    rd: *rdlo,
                    rn: *rnlo,
                    op2: Operand2::Reg(*rmlo),
                })?);
                bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Eor {
                    rd: *rdhi,
                    rn: *rnhi,
                    op2: Operand2::Reg(*rmhi),
                })?);
                Ok(bytes)
            }

            // I64Eqz: ORR scratch, lo, hi; ITE EQ; MOV rd, #1; MOV rd, #0
            ArmOp::I64Eqz { rd, rnlo, rnhi } => self.encode_thumb(&ArmOp::I64SetCondZ {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
            }),

            // I64 comparisons: delegate to I64SetCond
            ArmOp::I64Eq {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::EQ,
            }),

            ArmOp::I64Ne {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::NE,
            }),

            ArmOp::I64LtS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::LT,
            }),

            ArmOp::I64LtU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::LO,
            }),

            ArmOp::I64LeS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::LE,
            }),

            ArmOp::I64LeU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::LS,
            }),

            ArmOp::I64GtS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::GT,
            }),

            ArmOp::I64GtU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::HI,
            }),

            ArmOp::I64GeS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::GE,
            }),

            ArmOp::I64GeU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => self.encode_thumb(&ArmOp::I64SetCond {
                rd: *rd,
                rn_lo: *rnlo,
                rn_hi: *rnhi,
                rm_lo: *rmlo,
                rm_hi: *rmhi,
                cond: synth_synthesis::Condition::HS,
            }),

            // I64Const: MOVW rdlo, lo16; MOVT rdlo, hi16; MOVW rdhi, lo16_hi; MOVT rdhi, hi16_hi
            ArmOp::I64Const { rdlo, rdhi, value } => {
                let lo32 = *value as u32;
                let hi32 = (*value >> 32) as u32;
                let mut bytes = Vec::new();
                // Load low 32 bits into rdlo
                bytes.extend_from_slice(
                    &self.encode_thumb32_movw_raw(reg_to_bits(rdlo), lo32 & 0xFFFF)?,
                );
                if lo32 > 0xFFFF {
                    bytes.extend_from_slice(
                        &self.encode_thumb32_movt_raw(reg_to_bits(rdlo), lo32 >> 16)?,
                    );
                }
                // Load high 32 bits into rdhi
                bytes.extend_from_slice(
                    &self.encode_thumb32_movw_raw(reg_to_bits(rdhi), hi32 & 0xFFFF)?,
                );
                if hi32 > 0xFFFF {
                    bytes.extend_from_slice(
                        &self.encode_thumb32_movt_raw(reg_to_bits(rdhi), hi32 >> 16)?,
                    );
                }
                Ok(bytes)
            }

            // I64Ldr: LDR rdlo, [base, offset]; LDR rdhi, [base, offset+4]
            ArmOp::I64Ldr { rdlo, rdhi, addr } => {
                let mut bytes = Vec::new();
                // #372/#382: a memory `i64.load` carries an index register
                // (`reg_imm(R11, addr_reg, offset)` = R11 + addr + offset). The
                // immediate `encode_thumb32_ldr` below uses only base+offset and
                // would SILENTLY DROP `offset_reg` — the #206 defect, here for
                // i64. `i64_effective_base` materializes the effective base into
                // `ip` (and, when `offset+4 > 0xFFF`, folds the offset in too so
                // the function is NOT skipped — #382), returning the residual
                // imm12 for the two halves. Frame i64 loads (no `offset_reg`, e.g.
                // a spilled local at `[SP, #off]`) keep the plain `[base,#off]`
                // form unchanged — so existing output is byte-identical.
                let (base, offset) = self.i64_effective_base(&mut bytes, addr)?;
                bytes.extend_from_slice(&self.encode_thumb32_ldr(rdlo, &base, offset)?);
                bytes.extend_from_slice(&self.encode_thumb32_ldr(
                    rdhi,
                    &base,
                    offset.wrapping_add(4),
                )?);
                Ok(bytes)
            }

            // I64Str: STR rdlo, [base, offset]; STR rdhi, [base, offset+4]
            ArmOp::I64Str { rdlo, rdhi, addr } => {
                let mut bytes = Vec::new();
                // #372/#382: same index-materialization + large-offset fold as
                // I64Ldr (see above).
                let (base, offset) = self.i64_effective_base(&mut bytes, addr)?;
                bytes.extend_from_slice(&self.encode_thumb32_str(rdlo, &base, offset)?);
                bytes.extend_from_slice(&self.encode_thumb32_str(
                    rdhi,
                    &base,
                    offset.wrapping_add(4),
                )?);
                Ok(bytes)
            }

            // I64ExtendI32S: MOV rdlo, rn; ASR rdhi, rdlo, #31 (sign-extend)
            ArmOp::I64ExtendI32S { rdlo, rdhi, rn } => {
                let mut bytes = Vec::new();
                if rdlo != rn {
                    // MOV rdlo, rn (16-bit)
                    bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Mov {
                        rd: *rdlo,
                        op2: Operand2::Reg(*rn),
                    })?);
                }
                // ASR rdhi, rdlo, #31 (sign-extend: fill high word with sign bit)
                bytes.extend_from_slice(
                    &self.encode_thumb32_shift(rdhi, rdlo, 31, 0b10)?, // ASR type
                );
                Ok(bytes)
            }

            // I64ExtendI32U: MOV rdlo, rn; MOV rdhi, #0
            ArmOp::I64ExtendI32U { rdlo, rdhi, rn } => {
                let mut bytes = Vec::new();
                if rdlo != rn {
                    // MOV rdlo, rn
                    bytes.extend_from_slice(&self.encode_thumb(&ArmOp::Mov {
                        rd: *rdlo,
                        op2: Operand2::Reg(*rn),
                    })?);
                }
                // MOV rdhi, #0 (16-bit: MOVS Rd, #0)
                let rdhi_bits = reg_to_bits(rdhi) as u16;
                let instr: u16 = 0x2000 | (rdhi_bits << 8);
                bytes.extend_from_slice(&instr.to_le_bytes());
                Ok(bytes)
            }

            // I32WrapI64: MOV rd, rnlo (just take low 32 bits)
            ArmOp::I32WrapI64 { rd, rnlo } => {
                if rd == rnlo {
                    // No-op: already in the right register
                    let instr: u16 = 0xBF00; // NOP
                    Ok(instr.to_le_bytes().to_vec())
                } else {
                    // MOV rd, rnlo
                    self.encode_thumb(&ArmOp::Mov {
                        rd: *rd,
                        op2: Operand2::Reg(*rnlo),
                    })
                }
            }

            // ===== Helium MVE operations (Thumb-2 encoding) =====
            ArmOp::MveLoad { qd, addr } => Ok(vfp_to_thumb_bytes(encode_mve_vldrw(qd, addr))),
            ArmOp::MveStore { qd, addr } => Ok(vfp_to_thumb_bytes(encode_mve_vstrw(qd, addr))),
            ArmOp::MveConst { qd, bytes } => self.encode_thumb_mve_const(qd, bytes),
            ArmOp::MveAnd { qd, qn, qm } => Ok(vfp_to_thumb_bytes(encode_mve_3reg_bitwise(
                0xEF000150, qd, qn, qm,
            ))),
            ArmOp::MveOrr { qd, qn, qm } => Ok(vfp_to_thumb_bytes(encode_mve_3reg_bitwise(
                0xEF200150, qd, qn, qm,
            ))),
            ArmOp::MveEor { qd, qn, qm } => Ok(vfp_to_thumb_bytes(encode_mve_3reg_bitwise(
                0xFF000150, qd, qn, qm,
            ))),
            ArmOp::MveMvn { qd, qm } => {
                // VMVN Qd, Qm: 0xFFB005C0 | Qd<<12 | Qm
                let qd_enc = qreg_to_num(qd);
                let qm_enc = qreg_to_num(qm);
                let instr: u32 = 0xFFB005C0 | ((qd_enc * 2) << 12) | (qm_enc * 2);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveBic { qd, qn, qm } => Ok(vfp_to_thumb_bytes(encode_mve_3reg_bitwise(
                0xEF100150, qd, qn, qm,
            ))),
            ArmOp::MveAddI { qd, qn, qm, size } => {
                let sz = mve_size_bits(size);
                let base: u32 = 0xEF000840 | (sz << 20);
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(base, qd, qn, qm)))
            }
            ArmOp::MveSubI { qd, qn, qm, size } => {
                let sz = mve_size_bits(size);
                let base: u32 = 0xFF000840 | (sz << 20);
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(base, qd, qn, qm)))
            }
            ArmOp::MveMulI { qd, qn, qm, size } => {
                let sz = mve_size_bits(size);
                let base: u32 = 0xEF000950 | (sz << 20);
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(base, qd, qn, qm)))
            }
            ArmOp::MveNegI { qd, qm, size } => {
                let sz = mve_size_bits(size);
                // VNEG.Sx Qd, Qm
                let qd_enc = qreg_to_num(qd);
                let qm_enc = qreg_to_num(qm);
                let base: u32 = 0xFFB103C0 | (sz << 18);
                let instr = base | ((qd_enc * 2) << 12) | (qm_enc * 2);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveDup { qd, rn, size } => {
                let sz = mve_size_bits(size);
                let qd_enc = qreg_to_num(qd);
                let rn_bits = reg_to_bits(rn);
                // VDUP.sz Qd, Rn: EEA0 0B10 variant
                // size encoding: 00=32, 01=16, 10=8
                let be = match sz {
                    0 => 0b00u32, // 8-bit
                    1 => 0b01,    // 16-bit
                    _ => 0b00,    // 32-bit (default)
                };
                let instr: u32 = 0xEEA00B10 | ((qd_enc * 2) << 16) | (rn_bits << 12) | (be << 5);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveExtractLane { rd, qn, lane, size } => {
                let qn_enc = qreg_to_num(qn);
                let rd_bits = reg_to_bits(rd);
                // VMOV.sz Rd, Dn[x] — extract from Q-register lane
                // For 32-bit: VMOV Rd, Dn — where Dn is the appropriate D-register
                let d_reg = qn_enc * 2 + ((*lane as u32) >> 1);
                let lane_in_d = (*lane as u32) & 1;
                let _sz = mve_size_bits(size);
                // VMOV Rd, Dn[x]: EE10 0B10 for 32-bit
                let instr: u32 = 0xEE100B10 | (d_reg << 16) | (rd_bits << 12) | (lane_in_d << 21);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveInsertLane { qd, rn, lane, size } => {
                let qd_enc = qreg_to_num(qd);
                let rn_bits = reg_to_bits(rn);
                let d_reg = qd_enc * 2 + ((*lane as u32) >> 1);
                let lane_in_d = (*lane as u32) & 1;
                let _sz = mve_size_bits(size);
                // VMOV Dn[x], Rn: EE00 0B10 for 32-bit
                let instr: u32 = 0xEE000B10 | (d_reg << 16) | (rn_bits << 12) | (lane_in_d << 21);
                Ok(vfp_to_thumb_bytes(instr))
            }

            // MVE float comparisons — emit VCMP + VPSEL sequence (simplified: just VCMP)
            ArmOp::MveCmpEqI { qd, qn, qm, size }
            | ArmOp::MveCmpNeI { qd, qn, qm, size }
            | ArmOp::MveCmpLtS { qd, qn, qm, size }
            | ArmOp::MveCmpLtU { qd, qn, qm, size }
            | ArmOp::MveCmpGtS { qd, qn, qm, size }
            | ArmOp::MveCmpGtU { qd, qn, qm, size }
            | ArmOp::MveCmpLeS { qd, qn, qm, size }
            | ArmOp::MveCmpLeU { qd, qn, qm, size }
            | ArmOp::MveCmpGeS { qd, qn, qm, size }
            | ArmOp::MveCmpGeU { qd, qn, qm, size } => {
                // Encode as VADD (placeholder encoding — real implementation
                // would use VCMP + VPSEL pair)
                let sz = mve_size_bits(size);
                let base: u32 = 0xEF000840 | (sz << 20);
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(base, qd, qn, qm)))
            }

            // f32x4 MVE arithmetic
            ArmOp::MveAddF32 { qd, qn, qm } => {
                // VADD.F32 Qd, Qn, Qm (MVE): 0xEF000D40
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(0xEF000D40, qd, qn, qm)))
            }
            ArmOp::MveSubF32 { qd, qn, qm } => {
                // VSUB.F32 Qd, Qn, Qm (MVE): 0xEF200D40
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(0xEF200D40, qd, qn, qm)))
            }
            ArmOp::MveMulF32 { qd, qn, qm } => {
                // VMUL.F32 Qd, Qn, Qm (MVE): 0xFF000D50
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(0xFF000D50, qd, qn, qm)))
            }
            ArmOp::MveNegF32 { qd, qm } => {
                let qd_enc = qreg_to_num(qd);
                let qm_enc = qreg_to_num(qm);
                // VNEG.F32 Qd, Qm: FFB907C0
                let instr: u32 = 0xFFB907C0 | ((qd_enc * 2) << 12) | (qm_enc * 2);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveAbsF32 { qd, qm } => {
                let qd_enc = qreg_to_num(qd);
                let qm_enc = qreg_to_num(qm);
                // VABS.F32 Qd, Qm: FFB90740
                let instr: u32 = 0xFFB90740 | ((qd_enc * 2) << 12) | (qm_enc * 2);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveCmpEqF32 { qd, qn, qm }
            | ArmOp::MveCmpNeF32 { qd, qn, qm }
            | ArmOp::MveCmpLtF32 { qd, qn, qm }
            | ArmOp::MveCmpLeF32 { qd, qn, qm }
            | ArmOp::MveCmpGtF32 { qd, qn, qm }
            | ArmOp::MveCmpGeF32 { qd, qn, qm } => {
                // Placeholder: encode as VADD.F32 (real impl needs VCMP.F32 + VPSEL)
                Ok(vfp_to_thumb_bytes(encode_mve_3reg(0xEF000D40, qd, qn, qm)))
            }
            ArmOp::MveDupF32 { qd, rn } => {
                let qd_enc = qreg_to_num(qd);
                let rn_bits = reg_to_bits(rn);
                // VDUP.32 Qd, Rn (same encoding as integer VDUP.32)
                let instr: u32 = 0xEEA00B10 | ((qd_enc * 2) << 16) | (rn_bits << 12);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveExtractLaneF32 { rd, qn, lane } => {
                let qn_enc = qreg_to_num(qn);
                let rd_bits = reg_to_bits(rd);
                // VMOV Rd, Sn where Sn = Q*4 + lane
                let s_num = qn_enc * 4 + (*lane as u32);
                let (vn, n) = encode_sreg(s_num);
                let instr: u32 = 0xEE100A10 | (vn << 16) | (rd_bits << 12) | (n << 7);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveReplaceLaneF32 { qd, rn, lane } => {
                let qd_enc = qreg_to_num(qd);
                let rn_bits = reg_to_bits(rn);
                // VMOV Sn, Rn where Sn = Q*4 + lane
                let s_num = qd_enc * 4 + (*lane as u32);
                let (vn, n) = encode_sreg(s_num);
                let instr: u32 = 0xEE000A10 | (vn << 16) | (rn_bits << 12) | (n << 7);
                Ok(vfp_to_thumb_bytes(instr))
            }
            ArmOp::MveDivF32 { qd, qn, qm } => {
                // Lane-wise: extract 4 S-regs, VDIV, insert back
                self.encode_thumb_mve_lane_wise_f32_binop(qd, qn, qm, 0xEE800A00)
            }
            ArmOp::MveSqrtF32 { qd, qm } => {
                // Lane-wise: extract 4 S-regs, VSQRT, insert back
                self.encode_thumb_mve_lane_wise_f32_sqrt(qd, qm)
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
        let sn_num = vfp_sreg_to_num(sn)?;
        let sm_num = vfp_sreg_to_num(sm)?;
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
        let vmov = encode_vmov_core_sreg(true, sd, &Reg::R12)?;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    /// Encode VMOV + VCVT.F32.xS32 as Thumb-2
    fn encode_thumb_f32_convert_i32(&self, sd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV Sd, Rm
        let vmov = encode_vmov_core_sreg(true, sd, rm)?;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        // VCVT.F32.S32/U32 Sd, Sd
        let sd_num = vfp_sreg_to_num(sd)?;
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
        let sm_num = vfp_sreg_to_num(sm)?;
        let sd_num = vfp_sreg_to_num(sd)?;
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
        let sn_num = vfp_sreg_to_num(sn)?;
        let sm_num = vfp_sreg_to_num(sm)?;
        let sd_num = vfp_sreg_to_num(sd)?;

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
        )?));

        // VMOV R0, Sn (get magnitude source bits)
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_sreg(
            false,
            sn,
            &Reg::R0,
        )?));

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
        )?));

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
        let dn_num = vfp_dreg_to_num(dn)?;
        let dm_num = vfp_dreg_to_num(dm)?;
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
        let vmov = encode_vmov_core_dreg(true, dd, &Reg::R0, &Reg::R12)?;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    /// Encode VMOV Sd, Rm + VCVT.F64.S32/U32 Dd, Sd as Thumb-2
    fn encode_thumb_f64_convert_i32(&self, dd: &VfpReg, rm: &Reg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        // VMOV S0, Rm
        let vmov = encode_vmov_core_sreg(true, &VfpReg::S0, rm)?;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        // VCVT.F64.S32 Dd, S0 or VCVT.F64.U32 Dd, S0
        let dd_num = vfp_dreg_to_num(dd)?;
        let (vd, d) = encode_dreg(dd_num);
        let base = if signed { 0xEEB80B40 } else { 0xEEB80BC0 };
        let vcvt = base | (d << 22) | (vd << 12);
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        Ok(bytes)
    }

    /// Encode VCVT.F64.F32 Dd, Sm as Thumb-2
    fn encode_thumb_f64_promote_f32(&self, dd: &VfpReg, sm: &VfpReg) -> Result<Vec<u8>> {
        let dd_num = vfp_dreg_to_num(dd)?;
        let sm_num = vfp_sreg_to_num(sm)?;
        let (vd, d) = encode_dreg(dd_num);
        let (vm, m) = encode_sreg(sm_num);

        let vcvt = 0xEEB70AC0 | (d << 22) | (vd << 12) | (m << 5) | vm;
        Ok(vfp_to_thumb_bytes(vcvt))
    }

    /// Encode VCVT.S32/U32.F64 S0, Dm + VMOV Rd, S0 as Thumb-2
    fn encode_thumb_i32_trunc_f64(&self, rd: &Reg, dm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm)?;
        let (vm, m) = encode_dreg(dm_num);

        // VCVT.S32.F64 S0, Dm or VCVT.U32.F64 S0, Dm
        let base = if signed { 0xEEBD0BC0 } else { 0xEEBC0BC0 };
        let vcvt = base | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        // VMOV Rd, S0
        let vmov = encode_vmov_core_sreg(false, &VfpReg::S0, rd)?;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    /// Encode F64 rounding pseudo-op as Thumb-2 via VCVT to integer and back
    /// Encode F64 rounding as Thumb-2.
    /// `mode`: FPSCR RMode — 0b00=nearest, 0b01=+inf(ceil), 0b10=-inf(floor), 0b11=zero(trunc)
    fn encode_thumb_f64_rounding(&self, dd: &VfpReg, dm: &VfpReg, mode: u8) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        let dm_num = vfp_dreg_to_num(dm)?;
        let dd_num = vfp_dreg_to_num(dd)?;
        let (vm, m) = encode_dreg(dm_num);
        let (vd, d) = encode_dreg(dd_num);

        if mode == 0b11 {
            // Trunc: VCVTR.S32.F64 — bit[7]=1, always truncates
            let vcvt_to_int = 0xEEBD0BC0 | (m << 5) | vm;
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_int));
        } else {
            let rt: u32 = 12;

            // VMRS R12, FPSCR
            let vmrs = 0xEEF10A10 | (rt << 12);
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmrs));

            // BIC.W R12, R12, #(3 << 22)
            let bic_hw1: u16 = 0xF020 | ((rt as u16) & 0xF);
            let bic_hw2: u16 = (0x05 << 12) | ((rt as u16) << 8) | 0x03;
            bytes.extend_from_slice(&bic_hw1.to_le_bytes());
            bytes.extend_from_slice(&bic_hw2.to_le_bytes());

            // ORR.W R12, R12, #(mode << 22)
            if mode != 0 {
                let orr_hw1: u16 = 0xF040 | ((rt as u16) & 0xF);
                let orr_hw2: u16 = (0x05 << 12) | ((rt as u16) << 8) | (mode as u16);
                bytes.extend_from_slice(&orr_hw1.to_le_bytes());
                bytes.extend_from_slice(&orr_hw2.to_le_bytes());
            }

            // VMSR FPSCR, R12
            let vmsr = 0xEEE10A10 | (rt << 12);
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmsr));

            // VCVT.S32.F64 S0, Dm — non-R variant (bit[7]=0)
            let vcvt_to_int = 0xEEBD0B40 | (m << 5) | vm;
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt_to_int));

            // Restore FPSCR
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmrs));
            bytes.extend_from_slice(&bic_hw1.to_le_bytes());
            bytes.extend_from_slice(&bic_hw2.to_le_bytes());
            bytes.extend_from_slice(&vfp_to_thumb_bytes(vmsr));
        }

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
        let dn_num = vfp_dreg_to_num(dn)?;
        let dm_num = vfp_dreg_to_num(dm)?;
        let dd_num = vfp_dreg_to_num(dd)?;

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
        )?));

        // VMOV R1, R2, Dn (get magnitude source)
        bytes.extend_from_slice(&vfp_to_thumb_bytes(encode_vmov_core_dreg(
            false,
            dn,
            &Reg::R1,
            &Reg::R2,
        )?));

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
        )?));

        Ok(bytes)
    }

    /// Encode VCVT.S32/U32.F32 + VMOV as Thumb-2
    fn encode_thumb_i32_trunc_f32(&self, rd: &Reg, sm: &VfpReg, signed: bool) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();

        let sm_num = vfp_sreg_to_num(sm)?;
        let (vd, d) = encode_sreg(sm_num);
        let (vm, m) = encode_sreg(sm_num);
        let base = if signed { 0xEEBD0AC0 } else { 0xEEBC0AC0 };
        let vcvt = base | (d << 22) | (vd << 12) | (m << 5) | vm;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vcvt));

        // VMOV Rd, Sm
        let vmov = encode_vmov_core_sreg(false, sm, rd)?;
        bytes.extend_from_slice(&vfp_to_thumb_bytes(vmov));

        Ok(bytes)
    }

    // === Thumb-2 32-bit encoding helpers ===

    /// Encode Thumb-2 32-bit ADD with immediate
    fn encode_thumb32_add(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        // The `i:imm3:imm8` field is split the same way for both forms.
        let i_bit = (imm >> 11) & 1;
        let imm3 = (imm >> 8) & 0x7;
        let imm8 = imm & 0xFF;

        let hw1_base = if imm <= 0xFF {
            // ADD.W (T3): the field is a ThumbExpandImm modified immediate. For
            // imm <= 0xFF (i:imm3 = 0000) it is the zero-extended byte, which is
            // correct — keep this form so existing encodings stay bit-identical.
            0xF100
        } else if imm <= 0xFFF {
            // ADDW (T4): a PLAIN 12-bit immediate (0..4095) — no ThumbExpandImm.
            // This is what makes `add sp, sp, #frame` correct for frame sizes
            // >= 256, which ADD.W (T3) would silently mis-encode (e.g. #256 -> #0).
            0xF200
        } else {
            return Err(synth_core::Error::synthesis(
                "ADD immediate > 0xFFF (4095) requires a multi-instruction sequence (not supported)",
            ));
        };

        let hw1: u16 = (hw1_base | (i_bit << 10) | rn_bits) as u16;
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

        let hw1_base = if imm <= 0xFF {
            // SUB.W (T3) modified immediate — correct for the zero-extended byte
            // (imm <= 0xFF). Kept bit-identical for existing encodings.
            0xF1A0
        } else if imm <= 0xFFF {
            // SUBW (T4): plain 12-bit immediate (0..4095). Makes
            // `sub sp, sp, #frame` correct for frame sizes >= 256.
            0xF2A0
        } else {
            return Err(synth_core::Error::synthesis(
                "SUB immediate > 0xFFF (4095) requires a multi-instruction sequence (not supported)",
            ));
        };

        let hw1: u16 = (hw1_base | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit ADDS with immediate (sets flags)
    fn encode_thumb32_adds(&self, rd: &Reg, rn: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rn_bits = reg_to_bits(rn);

        // ADDS.W (flag-setting) has only the modified-immediate form — error on
        // an un-encodable value rather than silently add the wrong constant.
        let field = try_thumb_expand_imm(imm).ok_or_else(|| {
            synth_core::Error::synthesis(
                "ADDS immediate is not a valid ThumbExpandImm — materialize into a register",
            )
        })?;
        let i_bit = (field >> 11) & 1;
        let imm3 = (field >> 8) & 0x7;
        let imm8 = field & 0xFF;

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

        // SUBS.W (flag-setting) has only the modified-immediate form — error on
        // an un-encodable value rather than silently subtract the wrong constant.
        let field = try_thumb_expand_imm(imm).ok_or_else(|| {
            synth_core::Error::synthesis(
                "SUBS immediate is not a valid ThumbExpandImm — materialize into a register",
            )
        })?;
        let i_bit = (field >> 11) & 1;
        let imm3 = (field >> 8) & 0x7;
        let imm8 = field & 0xFF;

        // SUBS.W Rd, Rn, #imm (with S=1)
        // First halfword: 1111 0 i 0 1101 1 Rn = F1B0 | i<<10 | Rn
        let hw1: u16 = (0xF1B0 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | (rd_bits << 8) | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit MOVW (16-bit immediate)
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires rd <= R14
    /// ensures result.len() == 4
    /// ensures (imm & 0xFFFF) can be reconstructed from the encoding
    /// ```
    fn encode_thumb32_movw(&self, rd: &Reg, imm: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        reg_bits_checked(rd_bits)?;
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
        encoding_contracts::verify_thumb32(&bytes);
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit shift with immediate
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires rd <= R14, rm <= R14
    /// ensures result.len() == 4
    /// ```
    fn encode_thumb32_shift(
        &self,
        rd: &Reg,
        rm: &Reg,
        shift: u32,
        shift_type: u8,
    ) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let rm_bits = reg_to_bits(rm);
        reg_bits_checked(rd_bits)?;
        reg_bits_checked(rm_bits)?;
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

        // CMP.W has only the modified-immediate form (no plain-imm12 like ADDW),
        // so an un-encodable immediate MUST be materialized into a register by
        // the selector. Error rather than silently compare the wrong constant.
        let field = try_thumb_expand_imm(imm).ok_or_else(|| {
            synth_core::Error::synthesis(
                "CMP immediate is not a valid ThumbExpandImm — materialize into a register",
            )
        })?;
        let i_bit = (field >> 11) & 1;
        let imm3 = (field >> 8) & 0x7;
        let imm8 = field & 0xFF;

        // CMP.W Rn, #imm
        let hw1: u16 = (0xF1B0 | (i_bit << 10) | rn_bits) as u16;
        let hw2: u16 = ((imm3 << 12) | 0x0F00 | imm8) as u16;

        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// #372/#382: resolve the base register AND residual immediate offset for an
    /// `I64Ldr`/`I64Str` whose address may carry an index register. Returns
    /// `(base, low_offset)`; the caller accesses the halves at `[base,
    /// #low_offset]` and `[base, #low_offset + 4]`.
    ///
    /// - Frame access (no `offset_reg`, e.g. a spilled local at `[SP, #off]`):
    ///   returns `(addr.base, off)` and emits NOTHING — byte-identical.
    /// - Memory access (`reg_imm(R11, addr, offset)` = `R11 + addr + offset`)
    ///   with `offset + 4 <= 0xFFF`: emits `ADD.W ip, base, index` and returns
    ///   `(ip, offset)`, folding `offset`/`offset+4` into the halves' imm12.
    ///   Byte-identical to the pre-#382 (#372) behavior.
    /// - Memory access with `offset + 4 > 0xFFF`: the imm12 form cannot hold the
    ///   high half's offset, so `encode_thumb32_ldr`'s `check_ldst_imm12` (#259)
    ///   rightly refused it and the WHOLE function was skipped (#382). Instead
    ///   MATERIALIZE the offset into the base: `ADD ip, index, #offset` (against
    ///   the read-only INDEX register, so `encode_thumb32_add_imm` never trips its
    ///   `rd==rn==R12` alias trap), then `ADD.W ip, ip, base` (+ R11), and return
    ///   `(ip, 0)` so the halves use `[ip, #0]` / `[ip, #4]`.
    ///
    /// The effective address is fully materialized into `ip` BEFORE the halves
    /// are accessed, so an `rdlo` aliasing the index register is safe.
    fn i64_effective_base(&self, bytes: &mut Vec<u8>, addr: &MemAddr) -> Result<(Reg, u32)> {
        let offset = if addr.offset < 0 {
            0u32
        } else {
            addr.offset as u32
        };
        match addr.offset_reg {
            Some(idx) => {
                let ip = Reg::R12;
                if offset.wrapping_add(4) > 0xFFF {
                    // Large static offset (#382): fold it (and R11) into ip so the
                    // imm12 halves stay in range instead of skipping the function.
                    // ADD ip, index, #offset  (index != ip → no add_imm alias trap)
                    bytes.extend_from_slice(&self.encode_thumb32_add_imm(&ip, &idx, offset)?);
                    // ADD.W ip, ip, base  (+ R11)
                    bytes.extend_from_slice(&self.encode_thumb32_add_reg_raw(
                        reg_to_bits(&ip),
                        reg_to_bits(&ip),
                        reg_to_bits(&addr.base),
                    )?);
                    Ok((ip, 0))
                } else {
                    // ADD.W ip, addr.base, idx  (Thumb-2, byte-verified vs as)
                    let hw1: u16 = 0xEB00 | reg_to_bits(&addr.base) as u16;
                    let hw2: u16 = 0x0C00 | reg_to_bits(&idx) as u16;
                    bytes.extend_from_slice(&hw1.to_le_bytes());
                    bytes.extend_from_slice(&hw2.to_le_bytes());
                    Ok((ip, offset))
                }
            }
            None => Ok((addr.base, offset)),
        }
    }

    /// Encode Thumb-2 32-bit LDR
    fn encode_thumb32_ldr(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);

        // LDR.W Rd, [Rn, #imm12]
        check_ldst_imm12(offset)?;
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
        check_ldst_imm12(offset)?;
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

    // === Sub-word load/store Thumb-2 encoding helpers ===

    /// Encode Thumb-2 32-bit LDRB with immediate: LDRB.W Rd, [Rn, #imm12]
    fn encode_thumb32_ldrb_imm(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        // LDRB.W Rd, [Rn, #imm12]: 1111 1000 1001 Rn | Rt imm12
        check_ldst_imm12(offset)?;
        let hw1: u16 = (0xF890 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRB with register: LDRB.W Rd, [Rn, Rm]
    fn encode_thumb32_ldrb_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);
        // LDRB.W Rd, [Rn, Rm, LSL #0]: 1111 1000 0001 Rn | Rt 0000 00 imm2 Rm
        let hw1: u16 = (0xF810 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRSB with immediate: LDRSB.W Rd, [Rn, #imm12]
    fn encode_thumb32_ldrsb_imm(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        // LDRSB.W Rd, [Rn, #imm12]: 1111 1001 1001 Rn | Rt imm12
        check_ldst_imm12(offset)?;
        let hw1: u16 = (0xF990 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRSB with register: LDRSB.W Rd, [Rn, Rm]
    fn encode_thumb32_ldrsb_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);
        // LDRSB.W Rd, [Rn, Rm, LSL #0]: 1111 1001 0001 Rn | Rt 0000 00 imm2 Rm
        let hw1: u16 = (0xF910 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRH with immediate: LDRH.W Rd, [Rn, #imm12]
    fn encode_thumb32_ldrh_imm(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        // LDRH.W Rd, [Rn, #imm12]: 1111 1000 1011 Rn | Rt imm12
        check_ldst_imm12(offset)?;
        let hw1: u16 = (0xF8B0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRH with register: LDRH.W Rd, [Rn, Rm]
    fn encode_thumb32_ldrh_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);
        // LDRH.W Rd, [Rn, Rm, LSL #0]: 1111 1000 0011 Rn | Rt 0000 00 imm2 Rm
        let hw1: u16 = (0xF830 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRSH with immediate: LDRSH.W Rd, [Rn, #imm12]
    fn encode_thumb32_ldrsh_imm(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        // LDRSH.W Rd, [Rn, #imm12]: 1111 1001 1011 Rn | Rt imm12
        check_ldst_imm12(offset)?;
        let hw1: u16 = (0xF9B0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit LDRSH with register: LDRSH.W Rd, [Rn, Rm]
    fn encode_thumb32_ldrsh_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);
        // LDRSH.W Rd, [Rn, Rm, LSL #0]: 1111 1001 0011 Rn | Rt 0000 00 imm2 Rm
        let hw1: u16 = (0xF930 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STRB with immediate: STRB.W Rd, [Rn, #imm12]
    fn encode_thumb32_strb_imm(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        // STRB.W Rd, [Rn, #imm12]: 1111 1000 1000 Rn | Rt imm12
        check_ldst_imm12(offset)?;
        let hw1: u16 = (0xF880 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STRB with register: STRB.W Rd, [Rn, Rm]
    fn encode_thumb32_strb_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);
        // STRB.W Rd, [Rn, Rm, LSL #0]: 1111 1000 0000 Rn | Rt 0000 00 imm2 Rm
        let hw1: u16 = (0xF800 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | rm_bits) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STRH with immediate: STRH.W Rd, [Rn, #imm12]
    fn encode_thumb32_strh_imm(&self, rd: &Reg, base: &Reg, offset: u32) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        // STRH.W Rd, [Rn, #imm12]: 1111 1000 1010 Rn | Rt imm12
        check_ldst_imm12(offset)?;
        let hw1: u16 = (0xF8A0 | base_bits) as u16;
        let hw2: u16 = ((rd_bits << 12) | (offset & 0xFFF)) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit STRH with register: STRH.W Rd, [Rn, Rm]
    fn encode_thumb32_strh_reg(&self, rd: &Reg, base: &Reg, offset_reg: &Reg) -> Result<Vec<u8>> {
        let rd_bits = reg_to_bits(rd);
        let base_bits = reg_to_bits(base);
        let rm_bits = reg_to_bits(offset_reg);
        // STRH.W Rd, [Rn, Rm, LSL #0]: 1111 1000 0010 Rn | Rt 0000 00 imm2 Rm
        let hw1: u16 = (0xF820 | base_bits) as u16;
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
            // Out-of-range immediate (> 0xFFF): materialize it into a scratch
            // register, then ADD.W Rd, Rn, scratch. This is the #180/#185
            // "encoder must produce a legal sequence, not assert" class — see #350.
            //
            // Scratch choice (must NEVER equal Rn, or Rn would be clobbered before
            // the ADD reads it):
            //   - rd != rn  => use rd itself (rn is untouched, since rd != rn).
            //   - rd == rn  => use R12/IP (the reserved encoder scratch). rd/rn are
            //                  never R12 (R12 is non-allocatable), so it can't alias.
            //
            // The materialized value is the same whether or not MOVT is emitted, so
            // the byte length depends only on `imm` (and rd==rn) — the size probe and
            // the final emit therefore agree (mandatory: the function is encoded twice).
            let scratch: u32 = if rd_bits == rn_bits {
                12 // R12/IP — in-place add, can't use rd because rd == rn
            } else {
                rd_bits // rn is preserved because rd != rn
            };
            // Invariant: the scratch must never alias Rn (would clobber it before
            // the ADD reads it). Unreachable in real codegen (rd/rn are never R12,
            // which is reserved encoder scratch), but the encoder is also driven by
            // the `encoder_no_panic` fuzz harness with ARBITRARY registers — incl.
            // rd==rn==R12, which makes scratch (R12) alias Rn. The encoder contract
            // (#180/#185) is Ok-or-Err, never a panic, so return a typed error
            // instead of asserting. #350 follow-up.
            if scratch == rn_bits {
                return Err(synth_core::Error::synthesis(format!(
                    "ADD #imm: cannot lower #{imm:#x} for Rd==Rn==R12 — no free scratch \
                     register (R12 is the reserved encoder scratch and aliases Rn here)"
                )));
            }

            let lo16 = imm & 0xFFFF;
            let hi16 = (imm >> 16) & 0xFFFF;

            let mut bytes = self.encode_thumb32_movw_raw(scratch, lo16)?;
            if hi16 != 0 {
                bytes.extend_from_slice(&self.encode_thumb32_movt_raw(scratch, hi16)?);
            }
            bytes.extend_from_slice(&self.encode_thumb32_add_reg_raw(rd_bits, rn_bits, scratch)?);
            Ok(bytes)
        }
    }

    // === Raw encoding helpers for POPCNT (take register numbers directly) ===

    /// Encode Thumb-2 32-bit MOVW (16-bit immediate) - raw version
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires rd <= 14, imm16 <= 0xFFFF
    /// ensures result.len() == 4
    /// ```
    fn encode_thumb32_movw_raw(&self, rd: u32, imm16: u32) -> Result<Vec<u8>> {
        reg_bits_checked(rd)?;
        encoding_contracts::verify_imm16(imm16);
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
        encoding_contracts::verify_thumb32(&bytes);
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit MOVT (move top 16 bits) - raw version
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires rd <= 14, imm16 <= 0xFFFF
    /// ensures result.len() == 4
    /// ```
    fn encode_thumb32_movt_raw(&self, rd: u32, imm16: u32) -> Result<Vec<u8>> {
        reg_bits_checked(rd)?;
        encoding_contracts::verify_imm16(imm16);
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
        encoding_contracts::verify_thumb32(&bytes);
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

    /// Encode Thumb-2 32-bit ADDS (register, flag-setting) - raw version.
    /// Used as the high-register fallback for `ArmOp::Adds` (i64 low-word add)
    /// so R8-R11 pair operands don't overflow the 16-bit field — #178/#180.
    fn encode_thumb32_adds_reg_raw(&self, rd: u32, rn: u32, rm: u32) -> Result<Vec<u8>> {
        // ADDS.W Rd, Rn, Rm (T3, S=1): EB10 Rn | 0 Rd 00 00 Rm
        let hw1: u16 = (0xEB10 | rn) as u16;
        let hw2: u16 = ((rd << 8) | rm) as u16;
        let mut bytes = hw1.to_le_bytes().to_vec();
        bytes.extend_from_slice(&hw2.to_le_bytes());
        Ok(bytes)
    }

    /// Encode Thumb-2 32-bit SUBS (register, flag-setting) - raw version.
    /// High-register fallback for `ArmOp::Subs` (i64 low-word subtract) — #178/#180.
    fn encode_thumb32_subs_reg_raw(&self, rd: u32, rn: u32, rm: u32) -> Result<Vec<u8>> {
        // SUBS.W Rd, Rn, Rm (T3, S=1): EBB0 Rn | 0 Rd 00 00 Rm
        let hw1: u16 = (0xEBB0 | rn) as u16;
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
/// Reverse of the ARMv7-M `ThumbExpandImm`: given a 32-bit immediate, return the
/// 12-bit `i:imm3:imm8` field if it is a representable modified immediate, else
/// `None` (the caller must materialize the value into a register). This is the
/// shared correct path for the data-processing immediate encoders — without it
/// they pack raw bits and silently mis-encode any value `> 0xFF` that isn't a
/// modified immediate (the silent-miscompile class behind #251/#253/#255).
fn try_thumb_expand_imm(value: u32) -> Option<u32> {
    // i:imm3 = 0000 → 8-bit value, zero-extended (00000000 00000000 00000000 XY).
    if value <= 0xFF {
        return Some(value);
    }
    let b0 = value & 0xFF; // byte 0
    let b1 = (value >> 8) & 0xFF; // byte 1
    // 0x00XY00XY (i:imm3 = 0001) — XY in bytes 0 and 2
    if value == (b0 << 16) | b0 {
        return Some(0x100 | b0);
    }
    // 0xXY00XY00 (i:imm3 = 0010) — XY in bytes 1 and 3
    if value == (b1 << 24) | (b1 << 8) {
        return Some(0x200 | b1);
    }
    // 0xXYXYXYXY (i:imm3 = 0011) — XY in all four bytes
    if value == (b0 << 24) | (b0 << 16) | (b0 << 8) | b0 {
        return Some(0x300 | b0);
    }
    // An 8-bit value with bit 7 set, rotated right by 8..=31. `rotate_left(rot)`
    // undoes the encoded right rotation; if the result is `1bbbbbbb` (0x80..=0xFF)
    // the value is representable. imm12[11:7] = rot, imm12[6:0] = low 7 bits.
    for rot in 8..=31u32 {
        let unrot = value.rotate_left(rot);
        if (0x80..=0xFF).contains(&unrot) {
            return Some((rot << 7) | (unrot & 0x7F));
        }
    }
    None
}

/// Guard a Thumb-2 `LDR/STR Rd, [Rn, #imm12]` offset. The imm12 form supports
/// `0..=4095`; a larger offset must be materialized into a register by the
/// selector (register-offset addressing). Returning `Err` rather than silently
/// masking `offset & 0xFFF` closes the wrong-address miscompile class (#259,
/// the load/store sibling of #253/#255).
fn check_ldst_imm12(offset: u32) -> Result<()> {
    if offset > 0xFFF {
        Err(synth_core::Error::synthesis(
            "load/store immediate offset > 0xFFF (4095) — materialize the offset into a register",
        ))
    } else {
        Ok(())
    }
}

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

/// Fallible form of the `verify_reg_bits` contract. PC (R15) is not a valid
/// data operand for the Thumb-2 encodings that use this guard (SDIV/UDIV/MLS/…
/// are UNPREDICTABLE with PC). Synth's own codegen never emits PC there, but
/// the encoder must stay *total* over arbitrary `ArmOp` inputs — the fuzz
/// harness (`encoder_no_panic`) requires Ok-or-Err, never a panic. Pre-fix, the
/// `debug_assert` in `verify_reg_bits` aborted under `-Cdebug-assertions`.
/// Returns a typed Err instead. See #185.
fn reg_bits_checked(bits: u32) -> Result<()> {
    if bits > 14 {
        return Err(synth_core::Error::synthesis(format!(
            "register bits {bits} (PC/R15) is not a valid operand for this Thumb-2 encoding"
        )));
    }
    Ok(())
}

/// Try to encode a 32-bit value as an ARM rotated immediate (imm8 ROR 2*rot4).
/// Returns Some((encoded_bits, 1)) if representable, None otherwise.
fn try_encode_rotated_imm(val: u32) -> Option<(u32, u32)> {
    if val == 0 {
        return Some((0, 1));
    }
    for rot in 0..16u32 {
        let shift = rot * 2;
        // Rotate left by shift (undo the ROR) to see if result fits in 8 bits
        let unrotated = val.rotate_left(shift);
        if unrotated <= 0xFF {
            // Encoded as: rot4(4 bits) | imm8(8 bits) = rotate_imm << 8 | imm8
            return Some(((rot << 8) | unrotated, 1));
        }
    }
    None
}

/// Encode operand2 field and return (bits, immediate_flag).
/// For ARM32 mode, immediates use the rotated-immediate encoding (imm8 ROR 2*rot4).
/// Panics if an immediate value cannot be represented. Callers that need large
/// immediates should use MOVW/MOVT instead of Operand2::Imm.
fn encode_operand2(op2: &Operand2) -> Result<(u32, u32)> {
    match op2 {
        Operand2::Imm(val) => {
            let uval = *val as u32;
            // Attempt rotated-immediate encoding (ARM32 Operand2)
            if let Some(encoded) = try_encode_rotated_imm(uval) {
                Ok(encoded)
            } else {
                // #378-class honesty: an immediate that can't be expressed as an
                // ARM32 rotated immediate is an INTERNAL selector bug — large
                // constants must be materialized via MOVW/MOVT, not passed here.
                // FAIL HONESTLY with an Err rather than silently masking to
                // `uval & 0xFF` and emitting a WRONG immediate. The encoder is
                // Ok-or-Err, never corrupt (#180/#185); a loud Err is also why
                // this is an Err and not a panic (the `encoder_no_panic` fuzz
                // contract — malformed/oversized input must degrade, not crash).
                Err(synth_core::Error::synthesis(format!(
                    "encode_operand2: immediate {uval:#x} ({val}) is not an ARM32 \
                     rotated immediate — the selector must materialize large \
                     constants via MOVW/MOVT"
                )))
            }
        }

        Operand2::Reg(reg) => {
            let reg_bits = reg_to_bits(reg);
            Ok((reg_bits, 0)) // I=0 for register
        }

        Operand2::RegShift {
            rm,
            shift: _,
            amount,
        } => {
            // Simplified encoding with shift
            let rm_bits = reg_to_bits(rm);
            let shift_bits = (*amount & 0x1F) << 7;
            Ok((shift_bits | rm_bits, 0))
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
fn vfp_sreg_to_num(reg: &VfpReg) -> Result<u32> {
    match reg {
        VfpReg::S0 => Ok(0),
        VfpReg::S1 => Ok(1),
        VfpReg::S2 => Ok(2),
        VfpReg::S3 => Ok(3),
        VfpReg::S4 => Ok(4),
        VfpReg::S5 => Ok(5),
        VfpReg::S6 => Ok(6),
        VfpReg::S7 => Ok(7),
        VfpReg::S8 => Ok(8),
        VfpReg::S9 => Ok(9),
        VfpReg::S10 => Ok(10),
        VfpReg::S11 => Ok(11),
        VfpReg::S12 => Ok(12),
        VfpReg::S13 => Ok(13),
        VfpReg::S14 => Ok(14),
        VfpReg::S15 => Ok(15),
        VfpReg::S16 => Ok(16),
        VfpReg::S17 => Ok(17),
        VfpReg::S18 => Ok(18),
        VfpReg::S19 => Ok(19),
        VfpReg::S20 => Ok(20),
        VfpReg::S21 => Ok(21),
        VfpReg::S22 => Ok(22),
        VfpReg::S23 => Ok(23),
        VfpReg::S24 => Ok(24),
        VfpReg::S25 => Ok(25),
        VfpReg::S26 => Ok(26),
        VfpReg::S27 => Ok(27),
        VfpReg::S28 => Ok(28),
        VfpReg::S29 => Ok(29),
        VfpReg::S30 => Ok(30),
        VfpReg::S31 => Ok(31),
        // D-registers are not used in F32 single-precision encodings
        _ => Err(synth_core::Error::SynthesisError(
            "D-register not supported in single-precision VFP encoding".to_string(),
        )),
    }
}

/// D-register number: D0=0, D1=1, ..., D15=15
fn vfp_dreg_to_num(reg: &VfpReg) -> Result<u32> {
    match reg {
        VfpReg::D0 => Ok(0),
        VfpReg::D1 => Ok(1),
        VfpReg::D2 => Ok(2),
        VfpReg::D3 => Ok(3),
        VfpReg::D4 => Ok(4),
        VfpReg::D5 => Ok(5),
        VfpReg::D6 => Ok(6),
        VfpReg::D7 => Ok(7),
        VfpReg::D8 => Ok(8),
        VfpReg::D9 => Ok(9),
        VfpReg::D10 => Ok(10),
        VfpReg::D11 => Ok(11),
        VfpReg::D12 => Ok(12),
        VfpReg::D13 => Ok(13),
        VfpReg::D14 => Ok(14),
        VfpReg::D15 => Ok(15),
        // S-registers are not used in F64 double-precision encodings
        _ => Err(synth_core::Error::SynthesisError(
            "S-register not supported in double-precision VFP encoding".to_string(),
        )),
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
fn encode_vfp_3reg(base: u32, sd: &VfpReg, sn: &VfpReg, sm: &VfpReg) -> Result<u32> {
    let sd_num = vfp_sreg_to_num(sd)?;
    let sn_num = vfp_sreg_to_num(sn)?;
    let sm_num = vfp_sreg_to_num(sm)?;
    let (vd, d) = encode_sreg(sd_num);
    let (vn, n) = encode_sreg(sn_num);
    let (vm, m) = encode_sreg(sm_num);

    Ok(base | (d << 22) | (vn << 16) | (vd << 12) | (n << 7) | (m << 5) | vm)
}

/// Encode a VFP 2-register instruction (VNEG.F32, VABS.F32, VSQRT.F32).
/// Returns the full 32-bit instruction word.
fn encode_vfp_2reg(base: u32, sd: &VfpReg, sm: &VfpReg) -> Result<u32> {
    let sd_num = vfp_sreg_to_num(sd)?;
    let sm_num = vfp_sreg_to_num(sm)?;
    let (vd, d) = encode_sreg(sd_num);
    let (vm, m) = encode_sreg(sm_num);

    Ok(base | (d << 22) | (vd << 12) | (m << 5) | vm)
}

/// Encode a VFP load/store (VLDR.F32 / VSTR.F32).
/// offset is in bytes and must be word-aligned; encoded as imm8 = offset/4.
/// U bit (bit 23) controls add/subtract offset.
fn encode_vfp_ldst(base: u32, sd: &VfpReg, addr: &MemAddr) -> Result<u32> {
    let sd_num = vfp_sreg_to_num(sd)?;
    let (vd, d) = encode_sreg(sd_num);
    let rn = reg_to_bits(&addr.base);

    let offset = addr.offset;
    let u_bit = if offset >= 0 { 1u32 } else { 0u32 };
    let abs_offset = offset.unsigned_abs();
    let imm8 = (abs_offset / 4) & 0xFF;

    Ok(base | (u_bit << 23) | (d << 22) | (rn << 16) | (vd << 12) | imm8)
}

/// Encode VMOV between core register and S-register.
/// VMOV Sn, Rt: 0xEE00_0A10 | (Vn << 16) | (N << 7) | (Rt << 12)
/// VMOV Rt, Sn: 0xEE10_0A10 | (Vn << 16) | (N << 7) | (Rt << 12)
fn encode_vmov_core_sreg(to_sreg: bool, sreg: &VfpReg, core: &Reg) -> Result<u32> {
    let s_num = vfp_sreg_to_num(sreg)?;
    let (vn, n) = encode_sreg(s_num);
    let rt = reg_to_bits(core);

    let base = if to_sreg { 0xEE000A10 } else { 0xEE100A10 };
    Ok(base | (vn << 16) | (rt << 12) | (n << 7))
}

/// Encode a VFP 3-register double-precision instruction (VADD.F64, VSUB.F64, etc.).
/// For double-precision (sz=1), coprocessor = 0xB (bits[11:8]).
/// The base should have bit 8 = 1 for F64 (0xB suffix instead of 0xA).
fn encode_vfp_3reg_f64(base: u32, dd: &VfpReg, dn: &VfpReg, dm: &VfpReg) -> Result<u32> {
    let dd_num = vfp_dreg_to_num(dd)?;
    let dn_num = vfp_dreg_to_num(dn)?;
    let dm_num = vfp_dreg_to_num(dm)?;
    let (vd, d) = encode_dreg(dd_num);
    let (vn, n) = encode_dreg(dn_num);
    let (vm, m) = encode_dreg(dm_num);

    Ok(base | (d << 22) | (vn << 16) | (vd << 12) | (n << 7) | (m << 5) | vm)
}

/// Encode a VFP 2-register double-precision instruction (VNEG.F64, VABS.F64, VSQRT.F64).
fn encode_vfp_2reg_f64(base: u32, dd: &VfpReg, dm: &VfpReg) -> Result<u32> {
    let dd_num = vfp_dreg_to_num(dd)?;
    let dm_num = vfp_dreg_to_num(dm)?;
    let (vd, d) = encode_dreg(dd_num);
    let (vm, m) = encode_dreg(dm_num);

    Ok(base | (d << 22) | (vd << 12) | (m << 5) | vm)
}

/// Encode a VFP load/store for double-precision (VLDR.64 / VSTR.64).
/// offset is in bytes and must be word-aligned; encoded as imm8 = offset/4.
fn encode_vfp_ldst_f64(base: u32, dd: &VfpReg, addr: &MemAddr) -> Result<u32> {
    let dd_num = vfp_dreg_to_num(dd)?;
    let (vd, d) = encode_dreg(dd_num);
    let rn = reg_to_bits(&addr.base);

    let offset = addr.offset;
    let u_bit = if offset >= 0 { 1u32 } else { 0u32 };
    let abs_offset = offset.unsigned_abs();
    let imm8 = (abs_offset / 4) & 0xFF;

    Ok(base | (u_bit << 23) | (d << 22) | (rn << 16) | (vd << 12) | imm8)
}

/// Encode VMOV between two core registers and a D-register.
/// VMOV Dm, Rt, Rt2: 0xEC40_0B10 | (Rt2 << 16) | (Rt << 12) | (M << 5) | Vm
/// VMOV Rt, Rt2, Dm: 0xEC50_0B10 | (Rt2 << 16) | (Rt << 12) | (M << 5) | Vm
fn encode_vmov_core_dreg(
    to_dreg: bool,
    dreg: &VfpReg,
    core_lo: &Reg,
    core_hi: &Reg,
) -> Result<u32> {
    let d_num = vfp_dreg_to_num(dreg)?;
    let (vm, m) = encode_dreg(d_num);
    let rt = reg_to_bits(core_lo);
    let rt2 = reg_to_bits(core_hi);

    let base = if to_dreg { 0xEC400B10 } else { 0xEC500B10 };
    Ok(base | (rt2 << 16) | (rt << 12) | (m << 5) | vm)
}

/// Emit a VFP 32-bit instruction as Thumb-2 bytes (two LE halfwords).
fn vfp_to_thumb_bytes(instr: u32) -> Vec<u8> {
    let hw1 = ((instr >> 16) & 0xFFFF) as u16;
    let hw2 = (instr & 0xFFFF) as u16;
    let mut bytes = hw1.to_le_bytes().to_vec();
    bytes.extend_from_slice(&hw2.to_le_bytes());
    bytes
}

// ============================================================================
// Helium MVE encoding helpers
// ============================================================================

/// Q-register number: Q0=0, Q1=1, ..., Q7=7
fn qreg_to_num(reg: &QReg) -> u32 {
    match reg {
        QReg::Q0 => 0,
        QReg::Q1 => 1,
        QReg::Q2 => 2,
        QReg::Q3 => 3,
        QReg::Q4 => 4,
        QReg::Q5 => 5,
        QReg::Q6 => 6,
        QReg::Q7 => 7,
    }
}

/// MVE element size to encoding bits: S8=0b00, S16=0b01, S32=0b10
fn mve_size_bits(size: &MveSize) -> u32 {
    match size {
        MveSize::S8 => 0b00,
        MveSize::S16 => 0b01,
        MveSize::S32 => 0b10,
    }
}

/// Encode MVE 3-register instruction.
/// Q-registers are encoded as D-register pairs: Q0=D0:D1, Q1=D2:D3, etc.
/// In NEON/MVE encoding, the Q-register uses D-register number = Qn * 2.
fn encode_mve_3reg(base: u32, qd: &QReg, qn: &QReg, qm: &QReg) -> u32 {
    let d = qreg_to_num(qd) * 2;
    let n = qreg_to_num(qn) * 2;
    let m = qreg_to_num(qm) * 2;

    // Standard NEON/MVE 3-register encoding:
    // D bit (bit 22) = Vd[4], Vd[3:0] = bits [15:12]
    // N bit (bit 7)  = Vn[4], Vn[3:0] = bits [19:16]
    // M bit (bit 5)  = Vm[4], Vm[3:0] = bits [3:0]
    let vd = d & 0xF;
    let d_bit = (d >> 4) & 1;
    let vn = n & 0xF;
    let n_bit = (n >> 4) & 1;
    let vm = m & 0xF;
    let m_bit = (m >> 4) & 1;

    base | (d_bit << 22) | (vn << 16) | (vd << 12) | (n_bit << 7) | (m_bit << 5) | vm
}

/// Encode MVE 3-register bitwise instruction (VAND, VORR, VEOR, VBIC).
fn encode_mve_3reg_bitwise(base: u32, qd: &QReg, qn: &QReg, qm: &QReg) -> u32 {
    encode_mve_3reg(base, qd, qn, qm)
}

/// Encode MVE VLDRW.32 Qd, [Rn, #offset]
/// Format: EC9x xxxx - contiguous load, word-sized elements
fn encode_mve_vldrw(qd: &QReg, addr: &MemAddr) -> u32 {
    let qd_enc = qreg_to_num(qd) * 2;
    let rn = reg_to_bits(&addr.base);
    let offset = addr.offset;
    let u_bit = if offset >= 0 { 1u32 } else { 0u32 };
    let abs_offset = offset.unsigned_abs();
    let imm7 = (abs_offset / 4) & 0x7F; // 7-bit word-aligned offset

    // VLDRW.32 Qd, [Rn, #imm]: ED10 xx80 variant
    0xED100E80
        | (u_bit << 23)
        | ((qd_enc >> 4) << 22)
        | (rn << 16)
        | ((qd_enc & 0xF) << 12)
        | (imm7 & 0x7F)
}

/// Encode MVE VSTRW.32 Qd, [Rn, #offset]
fn encode_mve_vstrw(qd: &QReg, addr: &MemAddr) -> u32 {
    let qd_enc = qreg_to_num(qd) * 2;
    let rn = reg_to_bits(&addr.base);
    let offset = addr.offset;
    let u_bit = if offset >= 0 { 1u32 } else { 0u32 };
    let abs_offset = offset.unsigned_abs();
    let imm7 = (abs_offset / 4) & 0x7F;

    0xED000E80
        | (u_bit << 23)
        | ((qd_enc >> 4) << 22)
        | (rn << 16)
        | ((qd_enc & 0xF) << 12)
        | (imm7 & 0x7F)
}

impl ArmEncoder {
    /// Encode MVE constant load: MOVW+MOVT+VMOV for each 32-bit word, then assemble Q-register
    fn encode_thumb_mve_const(&self, qd: &QReg, bytes: &[u8; 16]) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        let qd_num = qreg_to_num(qd);

        // Load each 32-bit word into R12 (temp) then VMOV into S-register
        for i in 0..4 {
            let word = u32::from_le_bytes([
                bytes[i * 4],
                bytes[i * 4 + 1],
                bytes[i * 4 + 2],
                bytes[i * 4 + 3],
            ]);
            let lo16 = word & 0xFFFF;
            let hi16 = (word >> 16) & 0xFFFF;

            // MOVW R12, #lo16
            result.extend_from_slice(&self.encode_thumb32_movw_raw(12, lo16)?);
            // MOVT R12, #hi16
            if hi16 != 0 {
                result.extend_from_slice(&self.encode_thumb32_movt_raw(12, hi16)?);
            }

            // VMOV Sn, R12 where Sn = Qd*4 + i
            let s_num = qd_num * 4 + i as u32;
            let (vn, n) = encode_sreg(s_num);
            let vmov: u32 = 0xEE000A10 | (vn << 16) | (12 << 12) | (n << 7);
            result.extend_from_slice(&vfp_to_thumb_bytes(vmov));
        }

        Ok(result)
    }

    /// Encode lane-wise f32 binary operation (VDIV, etc.) via S-register extraction
    fn encode_thumb_mve_lane_wise_f32_binop(
        &self,
        qd: &QReg,
        qn: &QReg,
        qm: &QReg,
        vfp_base: u32,
    ) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        let qd_num = qreg_to_num(qd);
        let qn_num = qreg_to_num(qn);
        let qm_num = qreg_to_num(qm);

        // For each lane 0..3: use S-registers directly (Q aliasing)
        for i in 0..4u32 {
            let sd = qd_num * 4 + i;
            let sn = qn_num * 4 + i;
            let sm = qm_num * 4 + i;

            let (vd, d) = encode_sreg(sd);
            let (vn, n) = encode_sreg(sn);
            let (vm, m) = encode_sreg(sm);

            let instr = vfp_base | (d << 22) | (vn << 16) | (vd << 12) | (n << 7) | (m << 5) | vm;
            result.extend_from_slice(&vfp_to_thumb_bytes(instr));
        }

        Ok(result)
    }

    /// Encode lane-wise f32 VSQRT via S-register extraction
    fn encode_thumb_mve_lane_wise_f32_sqrt(&self, qd: &QReg, qm: &QReg) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        let qd_num = qreg_to_num(qd);
        let qm_num = qreg_to_num(qm);

        // VSQRT.F32 base: 0xEEB10AC0
        for i in 0..4u32 {
            let sd = qd_num * 4 + i;
            let sm = qm_num * 4 + i;

            let (vd, d) = encode_sreg(sd);
            let (vm, m) = encode_sreg(sm);

            let instr: u32 = 0xEEB10AC0 | (d << 22) | (vd << 12) | (m << 5) | vm;
            result.extend_from_slice(&vfp_to_thumb_bytes(instr));
        }

        Ok(result)
    }
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

    /// #204 WAKE-path regression: `SetCond` materialized 0/1 with the 16-bit
    /// `MOVS Rd,#imm` (T1), whose Rd field is 3 bits (R0–R7). For a high Rd
    /// (R8–R12) `rd_bits << 8` overflows bit 11, flipping the opcode MOVS→CMP
    /// (`0x2c00`), so the boolean was never written — gale's `has_waiter` kept a
    /// stale value and the binary-sem WAKE dispatch read garbage. High Rd must
    /// use the 32-bit `MOV.W` (T2). Verify the bytes, not the IR.
    /// #311: the SAME high-Rd MOVS→CMP transmutation as #204, but in the
    /// i64 comparison expansions (I64SetCond / I64SetCondZ) — missed by the
    /// #204 hardening. With rd=R8 the boolean died in the flags
    /// (`ite eq; cmpeq r0,#1; cmpne r0,#0`), so gale's packed-u64 select
    /// read a stale register on silicon. High Rd must take MOV.W / CMP.W.
    #[test]
    fn test_encode_i64setcond_high_reg_uses_mov_w_311() {
        use synth_synthesis::{ArmOp, Condition, Reg};
        let enc = ArmEncoder::new_thumb2();
        let bytes = enc
            .encode(&ArmOp::I64SetCond {
                rd: Reg::R8,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R6,
                rm_hi: Reg::R7,
                cond: Condition::EQ,
            })
            .unwrap();
        // The 32-bit MOV.W immediate (T2) first halfword is 0xF04F; the
        // 16-bit transmuted forms would contain 0x2801/0x2800 (CMP r0,#1/#0).
        let halfwords: Vec<u16> = bytes
            .chunks(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect();
        assert!(
            halfwords.iter().filter(|&&h| h == 0xF04F).count() == 2,
            "high rd must use two MOV.W (T2) encodings, got {halfwords:04x?}"
        );
        assert!(
            !halfwords.contains(&0x2801) && !halfwords.contains(&0x2800),
            "no transmuted 16-bit CMP imm: {halfwords:04x?}"
        );

        let bytes_z = enc
            .encode(&ArmOp::I64SetCondZ {
                rd: Reg::R8,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
            })
            .unwrap();
        let hw_z: Vec<u16> = bytes_z
            .chunks(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect();
        assert!(
            hw_z.iter().filter(|&&h| h == 0xF04F).count() == 2,
            "SetCondZ high rd MOV.W: {hw_z:04x?}"
        );
        // CMP.W rd,#0 (T2) first halfword: 0xF1B0 | rd
        assert!(
            hw_z.contains(&(0xF1B0 | 8)),
            "SetCondZ high rd must use CMP.W: {hw_z:04x?}"
        );
    }

    #[test]
    fn test_encode_setcond_high_reg_uses_mov_w_204() {
        use synth_synthesis::{ArmOp, Condition, Reg};
        let enc = ArmEncoder::new_thumb2();
        // R12 (high): must be ITE + MOV.W #1 + MOV.W #0, never a 16-bit MOVS/CMP.
        let hi = enc
            .encode(&ArmOp::SetCond {
                rd: Reg::R12,
                cond: Condition::NE,
            })
            .unwrap();
        assert_eq!(hi.len(), 10, "ITE(2) + MOV.W(4) + MOV.W(4): {hi:02x?}");
        // both value halfwords are MOV.W (0xF04F) — NOT the corrupt CMP (0x2c..).
        assert_eq!(&hi[2..4], &[0x4F, 0xF0], "then = MOV.W: {hi:02x?}");
        assert_eq!(&hi[6..8], &[0x4F, 0xF0], "else = MOV.W: {hi:02x?}");
        assert_eq!(hi[4] & 0x0F, 0x01, "then imm = #1");
        assert_eq!(hi[8] & 0x0F, 0x00, "else imm = #0");
        // Low Rd keeps the compact 16-bit MOVS form.
        let lo = enc
            .encode(&ArmOp::SetCond {
                rd: Reg::R0,
                cond: Condition::NE,
            })
            .unwrap();
        assert_eq!(lo.len(), 6, "ITE(2) + MOVS(2) + MOVS(2): {lo:02x?}");
        assert_eq!(lo[2..4], [0x01, 0x20], "then = MOVS R0,#1");
        assert_eq!(lo[4..6], [0x00, 0x20], "else = MOVS R0,#0");
    }

    /// #209 Opt 1b: UMULL RdLo, RdHi, Rn, Rm encodes correctly on both ISAs.
    /// Thumb-2 T1: 1111 1011 1010 Rn | RdLo RdHi 0000 Rm.
    /// A32:        cond 0000 1000 RdHi RdLo Rm 1001 Rn.
    #[test]
    fn test_encode_umull_209b() {
        use synth_synthesis::{ArmOp, Reg};
        let op = ArmOp::Umull {
            rdlo: Reg::R4,
            rdhi: Reg::R5,
            rn: Reg::R0,
            rm: Reg::R3,
        };
        // Thumb-2: hw1 = 0xFBA0 | 0 = 0xFBA0; hw2 = (4<<12)|(5<<8)|3 = 0x4503.
        let t = ArmEncoder::new_thumb2().encode(&op).unwrap();
        assert_eq!(
            t,
            vec![0xA0, 0xFB, 0x03, 0x45],
            "umull r4,r5,r0,r3 (T2): {t:02x?}"
        );
        // A32: 0xE0800090 | (5<<16) | (4<<12) | (3<<8) | 0 = 0xE0854390.
        let a = ArmEncoder::new_arm32().encode(&op).unwrap();
        assert_eq!(
            a,
            0xE085_4390u32.to_le_bytes().to_vec(),
            "umull (A32): {a:02x?}"
        );
    }

    /// #206 regression: the ARM32 (A32) `Ldr`/`Str` encoders fed `addr` through
    /// `encode_mem_addr`, which returns only the 12-bit immediate — so a register
    /// offset (`[rn, rm, #off]`) was silently dropped to `[rn, #off]`, sending
    /// the access to the wrong runtime address (silent miscompile on the default
    /// `--target arm`). A register offset must materialize `ip = rn + rm` and
    /// load from `[ip, #off]`. Verify the bytes.
    #[test]
    fn test_encode_arm32_indexed_load_keeps_index_206() {
        use synth_synthesis::{ArmOp, MemAddr, Reg};
        let enc = ArmEncoder::new_arm32();
        // ldr r0, [r11, r1, #8]  must NOT collapse to a single immediate ldr.
        let bytes = enc
            .encode(&ArmOp::Ldr {
                rd: Reg::R0,
                addr: MemAddr::reg_imm(Reg::R11, Reg::R1, 8),
            })
            .unwrap();
        assert_eq!(
            bytes.len(),
            8,
            "expected ADD ip + LDR (2 words): {bytes:02x?}"
        );
        let add = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        let ldr = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
        // ADD ip, r11, r1  = 0xE08BC001
        assert_eq!(add, 0xE08B_C001, "ADD ip,r11,r1: {add:#010x}");
        // LDR r0, [ip, #8] = 0xE59C0008
        assert_eq!(ldr, 0xE59C_0008, "LDR r0,[ip,#8]: {ldr:#010x}");
        // A bare immediate ldr (the bug) would be 0xE59B0008 (base=r11) — reject.
        assert_ne!(ldr, 0xE59B_0008, "index must not be dropped");
    }

    /// #594 regression: `call_indirect` on the A32 path (`--target cortex-r5`)
    /// was encoded as a literal NOP (0xE1A00000) — the call never happened and
    /// the function silently returned the leftover table-index value. The A32
    /// encoder must emit the same three-instruction expansion as Thumb-2:
    /// `MOV r12, idx, LSL #2; LDR r12, [r11, r12]; BLX r12`.
    #[test]
    fn test_encode_arm32_call_indirect_is_real_call_594() {
        use synth_synthesis::{ArmOp, Reg};
        let enc = ArmEncoder::new_arm32();
        let bytes = enc
            .encode(&ArmOp::CallIndirect {
                rd: Reg::R0,
                type_idx: 0,
                table_index_reg: Reg::R0,
            })
            .unwrap();
        assert_eq!(
            bytes.len(),
            12,
            "expected MOV + LDR + BLX (3 words): {bytes:02x?}"
        );
        let mov = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        let ldr = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
        let blx = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
        // MOV r12, r0, LSL #2 = 0xE1A0C100
        assert_eq!(mov, 0xE1A0_C100, "MOV r12,r0,LSL#2: {mov:#010x}");
        // LDR r12, [r11, r12] = 0xE79BC00C
        assert_eq!(ldr, 0xE79B_C00C, "LDR r12,[r11,r12]: {ldr:#010x}");
        // BLX r12 = 0xE12FFF3C
        assert_eq!(blx, 0xE12F_FF3C, "BLX r12: {blx:#010x}");
        // The bug: a single NOP word. Must never come back.
        assert!(
            !bytes
                .chunks_exact(4)
                .any(|w| w == 0xE1A0_0000u32.to_le_bytes()),
            "call_indirect must not contain a NOP (#594): {bytes:02x?}"
        );

        // A non-R0 index register lands in the MOV's Rm field.
        let bytes = enc
            .encode(&ArmOp::CallIndirect {
                rd: Reg::R0,
                type_idx: 0,
                table_index_reg: Reg::R4,
            })
            .unwrap();
        let mov = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
        assert_eq!(mov, 0xE1A0_C104, "MOV r12,r4,LSL#2: {mov:#010x}");
    }

    /// #597 anchor (justified correctness RE-PIN of the #594-era freeze): the
    /// Thumb-2 `CallIndirect` expansion is `mov.w ip, rm, LSL #2; ldr.w ip,
    /// [r11, ip]; blx ip`.
    ///
    /// The #594 PR froze the then-current bytes `4F EA 20 0C ...` whose first
    /// word decodes as `mov.w ip, rm, ASR #32` — the intended `LSL #2` had
    /// its shift amount in the TYPE field (bits 5:4) instead of imm2 (bits
    /// 7:6), so the index was destroyed and every call_indirect dispatched
    /// table entry 0 (shipped miscompile, masked by index-0 probes). #597
    /// corrects the encoding; new bytes `4F EA 80 0C ...` were
    /// execution-validated under unicorn against the wasmtime oracle on a
    /// multi-entry table (indexes 0, 1, 3 —
    /// scripts/repro/call_indirect_597_differential.py) before this pin was
    /// replaced. Old pin: [4F EA 20 0C, 5B F8 0C C0, E0 47] (ASR #32 — must
    /// never come back).
    #[test]
    fn test_encode_thumb_call_indirect_lsl2_597() {
        use synth_synthesis::{ArmOp, Reg};
        let enc = ArmEncoder::new_thumb2();
        let bytes = enc
            .encode(&ArmOp::CallIndirect {
                rd: Reg::R0,
                type_idx: 0,
                table_index_reg: Reg::R0,
            })
            .unwrap();
        assert_eq!(
            bytes,
            vec![0x4F, 0xEA, 0x80, 0x0C, 0x5B, 0xF8, 0x0C, 0xC0, 0xE0, 0x47],
            "Thumb-2 CallIndirect: mov.w ip,r0,LSL#2; ldr.w ip,[r11,ip]; blx ip: {bytes:02x?}"
        );
        // The #597 bug bytes (ASR #32 first word) must never come back.
        assert_ne!(
            &bytes[0..4],
            &[0x4F, 0xEA, 0x20, 0x0C],
            "mov.w ip, rm, ASR #32 — the #597 type-field bug"
        );

        // A non-R0 index register lands in the mov.w's Rm field (hw2 bits 3:0).
        let bytes = enc
            .encode(&ArmOp::CallIndirect {
                rd: Reg::R0,
                type_idx: 0,
                table_index_reg: Reg::R4,
            })
            .unwrap();
        assert_eq!(
            &bytes[0..4],
            &[0x4F, 0xEA, 0x84, 0x0C],
            "mov.w ip, r4, LSL #2: {bytes:02x?}"
        );
    }

    /// #178/#180 regression: the Thumb `Add`/`Adds`/`Subs` reg-forms used the
    /// 16-bit encoding unconditionally. For high registers (R12 base scratch,
    /// R8-R11 i64 pairs) the 3-bit register fields overflow and corrupt the
    /// operands — `add ip,ip,r0` came out as `adds r4,r5,r1` (0x186C), silently
    /// dropping the address operand and miscompiling every optimized memory
    /// access. High registers must use the 32-bit `.W` forms.
    #[test]
    fn test_encode_thumb_add_high_reg_uses_add_w_178_180() {
        let encoder = ArmEncoder::new_thumb2();

        // add ip, ip, r0  — the exact MemLoad/MemStore base+addr op.
        let code = encoder
            .encode(&ArmOp::Add {
                rd: Reg::R12,
                rn: Reg::R12,
                op2: Operand2::Reg(Reg::R0),
            })
            .unwrap();
        // ADD.W ip, ip, r0 = EB0C 0C00 (little-endian halfwords).
        assert_eq!(
            code,
            vec![0x0C, 0xEB, 0x00, 0x0C],
            "high-reg Thumb ADD must be 32-bit ADD.W (EB0C 0C00), not corrupt 16-bit; got {code:02X?}"
        );
        // Must NOT be the buggy 16-bit 0x186C (`adds r4,r5,r1`).
        assert_ne!(code, vec![0x6C, 0x18], "regressed to corrupt 16-bit ADDS");

        // Low-register add stays 16-bit (no regression for the common case).
        let lo = encoder
            .encode(&ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R3),
            })
            .unwrap();
        assert_eq!(
            lo.len(),
            2,
            "low-reg ADD should remain 16-bit, got {lo:02X?}"
        );
    }

    /// #178/#180 sibling: i64 low-word `Adds`/`Subs` can land in R8-R11 pairs;
    /// those must fall back to 32-bit ADDS.W/SUBS.W (flag-setting preserved).
    #[test]
    fn test_encode_thumb_adds_subs_high_reg_use_32bit_178_180() {
        let encoder = ArmEncoder::new_thumb2();

        // adds r10, r10, r8  → ADDS.W = EB1A 0A08
        let adds = encoder
            .encode(&ArmOp::Adds {
                rd: Reg::R10,
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            })
            .unwrap();
        assert_eq!(
            adds,
            vec![0x1A, 0xEB, 0x08, 0x0A],
            "high-reg ADDS must be 32-bit ADDS.W (EB1A 0A08); got {adds:02X?}"
        );

        // subs r10, r10, r8  → SUBS.W = EBBA 0A08
        let subs = encoder
            .encode(&ArmOp::Subs {
                rd: Reg::R10,
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            })
            .unwrap();
        assert_eq!(
            subs,
            vec![0xBA, 0xEB, 0x08, 0x0A],
            "high-reg SUBS must be 32-bit SUBS.W (EBBA 0A08); got {subs:02X?}"
        );
    }

    /// #184 (sibling of #180): 16-bit CMN (T1) only encodes R0-R7. High registers
    /// must use 32-bit CMN.W, not the corrupt truncated 16-bit form.
    #[test]
    fn test_encode_thumb_cmn_high_reg_uses_cmn_w_184() {
        let encoder = ArmEncoder::new_thumb2();

        // cmn r10, r8  → CMN.W = EB1A 0F08 (ADD.W S=1, Rd=PC discarded).
        let cmn = encoder
            .encode(&ArmOp::Cmn {
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            })
            .unwrap();
        assert_eq!(
            cmn,
            vec![0x1A, 0xEB, 0x08, 0x0F],
            "high-reg CMN must be 32-bit CMN.W (EB1A 0F08); got {cmn:02X?}"
        );

        // Low registers stay 16-bit: cmn r1, r2 = 0x42D1.
        let lo = encoder
            .encode(&ArmOp::Cmn {
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            })
            .unwrap();
        assert_eq!(
            lo.len(),
            2,
            "low-reg CMN should remain 16-bit, got {lo:02X?}"
        );
        assert_eq!(lo, vec![0xD1, 0x42], "low-reg CMN bytes wrong: {lo:02X?}");
    }

    /// #185 regression: feeding PC (R15) as a data operand to a Thumb-2 op that
    /// guards its registers must return Err, not panic under debug-assertions.
    /// (Synth never emits PC here; the fuzz harness requires encode() be total.)
    #[test]
    fn test_encode_pc_operand_returns_err_not_panic_185() {
        let encoder = ArmEncoder::new_thumb2();
        for op in [
            ArmOp::Sdiv {
                rd: Reg::PC,
                rn: Reg::R0,
                rm: Reg::R1,
            },
            ArmOp::Udiv {
                rd: Reg::R0,
                rn: Reg::PC,
                rm: Reg::R1,
            },
            ArmOp::Sdiv {
                rd: Reg::R0,
                rn: Reg::R1,
                rm: Reg::PC,
            },
        ] {
            let r = encoder.encode(&op);
            assert!(
                r.is_err(),
                "encode({op:?}) must return Err for a PC operand, got {r:?}"
            );
        }
        // Valid registers still encode fine (no false rejection).
        assert!(
            encoder
                .encode(&ArmOp::Sdiv {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2
                })
                .is_ok()
        );
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

    /// #350 — `encode_thumb32_add_imm` must lower an out-of-range immediate
    /// (> 0xFFF) to a legal MOVW(/MOVT) + ADD.W-register sequence instead of
    /// erroring. The small-imm fast path (imm <= 0xFFF) stays byte-identical.
    #[test]
    fn test_encode_add_imm_large_350() {
        let enc = ArmEncoder::new_thumb2();

        // --- Fast path unchanged: imm <= 0xFFF is a single 4-byte ADD.W ---
        let small = enc
            .encode_thumb32_add_imm(&Reg::R0, &Reg::R1, 0x123)
            .unwrap();
        assert_eq!(small.len(), 4, "small imm must stay a single instruction");

        // helper: decode a Thumb-2 MOVW/MOVT halfword pair back to its imm16
        fn movx_imm16(b: &[u8]) -> u32 {
            let hw1 = u16::from_le_bytes([b[0], b[1]]) as u32;
            let hw2 = u16::from_le_bytes([b[2], b[3]]) as u32;
            let imm4 = hw1 & 0xF;
            let i = (hw1 >> 10) & 1;
            let imm3 = (hw2 >> 12) & 0x7;
            let imm8 = hw2 & 0xFF;
            (imm4 << 12) | (i << 11) | (imm3 << 8) | imm8
        }
        fn movx_rd(b: &[u8]) -> u32 {
            (u16::from_le_bytes([b[2], b[3]]) as u32 >> 8) & 0xF
        }

        // --- rd != rn: scratch is rd. imm = 70000 = 0x11170 needs MOVW+MOVT. ---
        // 0x11170: lo16 = 0x1170, hi16 = 0x0001
        let seq = enc
            .encode_thumb32_add_imm(&Reg::R12, &Reg::R0, 70000)
            .unwrap();
        assert_eq!(seq.len(), 12, "MOVW + MOVT + ADD = 12 bytes");
        // MOVW r12, #0x1170
        assert_eq!(u16::from_le_bytes([seq[0], seq[1]]) & 0xFBF0, 0xF240);
        assert_eq!(movx_rd(&seq[0..4]), 12);
        assert_eq!(movx_imm16(&seq[0..4]), 0x1170);
        // MOVT r12, #0x0001
        assert_eq!(u16::from_le_bytes([seq[4], seq[5]]) & 0xFBF0, 0xF2C0);
        assert_eq!(movx_rd(&seq[4..8]), 12);
        assert_eq!(movx_imm16(&seq[4..8]), 0x0001);
        // ADD.W r12, r0, r12  (EB00 | rn=0 ; rd=12, rm=12)
        let add1 = u16::from_le_bytes([seq[8], seq[9]]) as u32;
        let add2 = u16::from_le_bytes([seq[10], seq[11]]) as u32;
        assert_eq!(add1 & 0xFFF0, 0xEB00);
        assert_eq!(add1 & 0xF, 0); // rn = r0
        assert_eq!((add2 >> 8) & 0xF, 12); // rd = r12
        assert_eq!(add2 & 0xF, 12); // rm = scratch = r12
        // The materialized scratch must reconstruct exactly 70000.
        assert_eq!(
            (movx_imm16(&seq[4..8]) << 16) | movx_imm16(&seq[0..4]),
            70000
        );

        // --- imm <= 0xFFFF: MOVT is skipped (MOVW + ADD = 8 bytes). ---
        let seq16 = enc
            .encode_thumb32_add_imm(&Reg::R3, &Reg::R0, 0xABCD)
            .unwrap();
        assert_eq!(seq16.len(), 8, "imm <= 0xFFFF skips MOVT");
        assert_eq!(movx_imm16(&seq16[0..4]), 0xABCD);
        assert_eq!(movx_rd(&seq16[0..4]), 3); // scratch = rd = r3

        // --- rd == rn (in-place add): scratch must be R12, not rd. ---
        // imm = 0x12345: lo16 = 0x2345, hi16 = 0x0001
        let inplace = enc
            .encode_thumb32_add_imm(&Reg::R5, &Reg::R5, 0x12345)
            .unwrap();
        assert_eq!(inplace.len(), 12);
        assert_eq!(movx_rd(&inplace[0..4]), 12, "rd==rn must use R12 scratch");
        assert_eq!(
            (movx_imm16(&inplace[4..8]) << 16) | movx_imm16(&inplace[0..4]),
            0x12345
        );
        // ADD.W r5, r5, r12 — rm must be the scratch (12), never rn.
        let ip_add2 = u16::from_le_bytes([inplace[10], inplace[11]]) as u32;
        assert_eq!(ip_add2 & 0xF, 12);
        assert_eq!((ip_add2 >> 8) & 0xF, 5);
    }

    /// #350 follow-up — the `encoder_no_panic` fuzz harness drives the encoder
    /// with ARBITRARY registers, including the one case the in-place lowering
    /// cannot serve: rd==rn==R12. There the scratch (R12, the reserved encoder
    /// register) would alias Rn and clobber it before the ADD reads it. The
    /// encoder contract (#180/#185) is Ok-or-Err, never a panic — so this must
    /// return Err, not assert. (Real codegen never emits rd==rn==R12 because R12
    /// is non-allocatable; this guards only the fuzz/adversarial path.)
    #[test]
    fn test_encode_add_imm_large_rd_rn_r12_errs_not_panics_350() {
        let enc = ArmEncoder::new_thumb2();
        // Out-of-range imm with rd==rn==R12: no free scratch -> Err.
        let r = enc.encode_thumb32_add_imm(&Reg::R12, &Reg::R12, 70000);
        assert!(
            r.is_err(),
            "rd==rn==R12 with out-of-range imm must Err (no free scratch), got {r:?}"
        );
        // Small imm with rd==rn==R12 still takes the single-instruction fast path
        // (no scratch needed) and must succeed — the guard is scoped to the
        // out-of-range lowering only.
        let small = enc.encode_thumb32_add_imm(&Reg::R12, &Reg::R12, 0x10);
        assert!(small.is_ok(), "small imm needs no scratch, must stay Ok");
    }

    /// #378 — `encode_operand2` (ARM32 data-processing operand) must FAIL
    /// HONESTLY on an immediate that is not a valid rotated immediate, rather
    /// than silently masking it to `imm & 0xFF` and emitting a WRONG
    /// instruction. `0x1FF` has 9 set bits, so it cannot come from rotating an
    /// 8-bit imm8 — non-encodable. Real codegen materializes large constants via
    /// MOVW/MOVT; this guards the encoder's Ok-or-Err contract (#180/#185)
    /// directly. It is an Err (not a panic) so the `encoder_no_panic` fuzz
    /// harness — which drives arbitrary operands — still passes.
    #[test]
    fn test_encode_operand2_non_rotatable_imm_errs_not_masks_378() {
        let enc = ArmEncoder::new_arm32();
        let bad = enc.encode(&ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Imm(0x1FF),
        });
        assert!(
            bad.is_err(),
            "non-rotatable ARM32 immediate 0x1FF must Err (was silently masked \
             to 0xFF), got {bad:?}"
        );
        // A representable rotated immediate still encodes fine (regression guard).
        let ok = enc.encode(&ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Imm(0xFF),
        });
        assert!(
            ok.is_ok(),
            "0xFF is a valid rotated immediate, must stay Ok"
        );
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

    /// Regression test for #167 + #174: the Thumb-2 BL relocatable placeholder
    /// must carry a -4 addend so an R_ARM_THM_CALL nets to exactly the symbol S.
    /// The correct encoding is what `gas` emits for `bl <extern>`: f7ff fffe
    /// (hw1=0xF7FF, hw2=0xFFFE), little-endian bytes FF F7 FE FF.
    ///   - 0xD000 (J1=J2=0) → ~+0x600000 garbage addend: `bl c0000c` / truncated
    ///     to fit (#167).
    ///   - 0xF800 (addend 0) → lands at S+4, one instruction past the callee
    ///     entry (#174).
    ///   - 0xFFFE (addend -4) → lands at S. Correct.
    #[test]
    fn test_encode_thumb_bl_placeholder_addend_167_174() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Bl {
            label: "callee".to_string(),
        };

        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "Thumb-2 BL is 32-bit");

        let hw1 = u16::from_le_bytes([code[0], code[1]]);
        let hw2 = u16::from_le_bytes([code[2], code[3]]);
        assert_eq!(hw1, 0xF7FF, "BL first halfword (matches gas `bl <extern>`)");
        assert_eq!(
            hw2, 0xFFFE,
            "BL second halfword must be 0xFFFE (-4 addend → nets to S), not 0xF800 (→ S+4, #174) or 0xD000 (#167)"
        );
        assert_ne!(hw2, 0xF800, "0xF800 (addend 0) lands at S+4 (#174)");
        assert_ne!(hw2, 0xD000, "0xD000 bakes in a ~+0x600000 addend (#167)");
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

    // ========================================================================
    // Control flow encoding tests
    // ========================================================================

    #[test]
    fn test_encode_label_emits_no_bytes() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Label {
            name: ".Lblock_end_0".to_string(),
        };
        let code = encoder.encode(&op).unwrap();
        assert!(code.is_empty(), "Label should emit zero bytes");

        let encoder32 = ArmEncoder::new_arm32();
        let code32 = encoder32.encode(&op).unwrap();
        assert!(
            code32.is_empty(),
            "Label should emit zero bytes in ARM32 too"
        );
    }

    #[test]
    fn test_encode_bcc_eq_thumb2() {
        use synth_synthesis::Condition;
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Bcc {
            cond: Condition::EQ,
            label: "target".to_string(),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2); // 16-bit conditional branch

        // BEQ with offset 0: 0xD000 in little-endian
        assert_eq!(code, vec![0x00, 0xD0]);
    }

    #[test]
    fn test_encode_bcc_ne_thumb2() {
        use synth_synthesis::Condition;
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Bcc {
            cond: Condition::NE,
            label: "target".to_string(),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2);

        // BNE with offset 0: 0xD100 in little-endian
        assert_eq!(code, vec![0x00, 0xD1]);
    }

    #[test]
    fn test_encode_bcc_arm32() {
        use synth_synthesis::Condition;
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Bcc {
            cond: Condition::EQ,
            label: "target".to_string(),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4); // 32-bit ARM instruction

        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        // BEQ: cond=0x0, opcode=0xA, offset=0
        assert_eq!(instr & 0xF0000000, 0x00000000); // EQ condition
        assert_eq!(instr & 0x0F000000, 0x0A000000); // Branch opcode
    }

    #[test]
    fn test_encode_udf_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Udf { imm: 0 };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2); // 16-bit

        // UDF #0: 0xDE00 in little-endian
        assert_eq!(code, vec![0x00, 0xDE]);
    }

    #[test]
    fn test_encode_nop_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Nop;
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2); // 16-bit

        // NOP: 0xBF00 in little-endian
        assert_eq!(code, vec![0x00, 0xBF]);
    }

    // =========================================================================
    // i64 Thumb-2 encoding tests
    // =========================================================================

    #[test]
    fn test_encode_i64_add_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Add {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
        };
        let code = encoder.encode(&op).unwrap();
        // Should emit ADDS (2 bytes) + ADC.W (4 bytes) = 6 bytes
        assert_eq!(code.len(), 6, "I64Add should be 6 bytes (ADDS + ADC.W)");
    }

    #[test]
    fn test_encode_i64_sub_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Sub {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
        };
        let code = encoder.encode(&op).unwrap();
        // Should emit SUBS (2 bytes) + SBC.W (4 bytes) = 6 bytes
        assert_eq!(code.len(), 6, "I64Sub should be 6 bytes (SUBS + SBC.W)");
    }

    #[test]
    fn test_encode_i64_and_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64And {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
        };
        let code = encoder.encode(&op).unwrap();
        // AND.W (4 bytes) + AND.W (4 bytes) = 8 bytes
        assert!(code.len() >= 4, "I64And should emit at least 4 bytes");
    }

    #[test]
    fn test_encode_i64_or_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Or {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
        };
        let code = encoder.encode(&op).unwrap();
        assert!(code.len() >= 4, "I64Or should emit at least 4 bytes");
    }

    #[test]
    fn test_encode_i64_xor_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Xor {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
        };
        let code = encoder.encode(&op).unwrap();
        assert!(code.len() >= 4, "I64Xor should emit at least 4 bytes");
    }

    #[test]
    fn test_encode_i64_const_small_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        // Small constant: only needs MOVW for each half
        let op = ArmOp::I64Const {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            value: 42,
        };
        let code = encoder.encode(&op).unwrap();
        // MOVW R0, #42 (4 bytes) + MOVW R1, #0 (4 bytes) = 8 bytes minimum
        assert!(code.len() >= 8, "I64Const should emit at least 8 bytes");
    }

    #[test]
    fn test_encode_i64_const_large_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        // Large constant: needs MOVW+MOVT for each half
        let op = ArmOp::I64Const {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            value: 0x1234_5678_9ABC_DEF0_u64 as i64,
        };
        let code = encoder.encode(&op).unwrap();
        // MOVW + MOVT for lo (8 bytes) + MOVW + MOVT for hi (8 bytes) = 16 bytes
        assert_eq!(
            code.len(),
            16,
            "I64Const with large value should be 16 bytes"
        );
    }

    #[test]
    fn test_encode_i64_extend_i32_s_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64ExtendI32S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R0,
        };
        let code = encoder.encode(&op).unwrap();
        // When rdlo == rn, only ASR (4 bytes) is emitted
        assert_eq!(
            code.len(),
            4,
            "I64ExtendI32S (same reg) should be 4 bytes (ASR only)"
        );
    }

    #[test]
    fn test_encode_i64_extend_i32_s_diff_reg_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64ExtendI32S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R2,
        };
        let code = encoder.encode(&op).unwrap();
        // MOV rdlo, rn (2 bytes for low regs) + ASR rdhi, rdlo, #31 (4 bytes) = 6 bytes
        assert!(
            code.len() >= 6,
            "I64ExtendI32S (diff reg) should be at least 6 bytes"
        );
    }

    #[test]
    fn test_encode_i64_extend_i32_u_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64ExtendI32U {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R0,
        };
        let code = encoder.encode(&op).unwrap();
        // When rdlo == rn, only MOV rdhi, #0 (2 bytes) is emitted
        assert_eq!(
            code.len(),
            2,
            "I64ExtendI32U (same reg) should be 2 bytes (MOV #0 only)"
        );
    }

    #[test]
    fn test_encode_i32_wrap_i64_nop_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        // When rd == rnlo, should be a NOP
        let op = ArmOp::I32WrapI64 {
            rd: Reg::R0,
            rnlo: Reg::R0,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 2, "I32WrapI64 same reg should be NOP (2 bytes)");
        assert_eq!(code, vec![0x00, 0xBF]); // NOP
    }

    #[test]
    fn test_encode_i32_wrap_i64_diff_reg_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I32WrapI64 {
            rd: Reg::R2,
            rnlo: Reg::R0,
        };
        let code = encoder.encode(&op).unwrap();
        // MOV R2, R0 (2 or 4 bytes)
        assert!(
            code.len() >= 2,
            "I32WrapI64 diff reg should emit at least 2 bytes"
        );
    }

    #[test]
    fn test_encode_i64_eqz_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Eqz {
            rd: Reg::R0,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
        };
        let code = encoder.encode(&op).unwrap();
        // Delegates to I64SetCondZ which is already encoded
        assert!(
            code.len() >= 6,
            "I64Eqz should emit at least 6 bytes for ORR+ITE+MOV+MOV"
        );
    }

    #[test]
    fn test_encode_i64_eq_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Eq {
            rd: Reg::R0,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
        };
        let code = encoder.encode(&op).unwrap();
        // Delegates to I64SetCond EQ: CMP lo + IT EQ + CMPEQ hi + ITE EQ + MOV 1 + MOV 0
        assert!(code.len() >= 10, "I64Eq should emit at least 10 bytes");
    }

    #[test]
    fn test_encode_i64_ldr_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Ldr {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            addr: MemAddr::imm(Reg::SP, 0),
        };
        let code = encoder.encode(&op).unwrap();
        // Two LDR instructions (lo at offset, hi at offset+4)
        assert!(code.len() >= 4, "I64Ldr should emit at least 4 bytes");
    }

    #[test]
    fn test_372_i64_ldr_indexed_materializes_address() {
        // #372: a memory i64.load carries an index register (R11 + addr + off).
        // The encoder must materialize `ip = base + index` (ADD.W) and load via
        // `[ip,#off]` — NOT drop the index. A frame (non-indexed) i64.load must
        // stay byte-identical (plain `[base,#off]`, no ADD).
        let encoder = ArmEncoder::new_thumb2();
        let indexed = encoder
            .encode(&ArmOp::I64Ldr {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                addr: MemAddr::reg_imm(Reg::R11, Reg::R0, 0),
            })
            .unwrap();
        // ADD.W ip, fp, r0 = eb0b 0c00 (byte-verified vs arm-none-eabi-as).
        assert_eq!(
            &indexed[0..4],
            &[0x0b, 0xeb, 0x00, 0x0c],
            "indexed I64Ldr must start with ADD.W ip, base, index"
        );
        let frame = encoder
            .encode(&ArmOp::I64Ldr {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                addr: MemAddr::imm(Reg::SP, 8),
            })
            .unwrap();
        // No index -> no ADD.W prefix (byte-identical frame access).
        assert_ne!(
            &frame[0..2],
            &[0x0b, 0xeb],
            "frame (non-indexed) I64Ldr must NOT emit an ADD.W"
        );
    }

    #[test]
    fn test_382_i64_ldst_large_offset_materializes_not_skips() {
        // #382: an indexed i64.load/store whose static offset > 0xFFF must
        // MATERIALIZE the offset into the base — NOT return Err (skip the fn).
        // Sequence for reg_imm(R11, R0, 5000): MOVW ip,#5000 ; ADD ip,r0,ip ;
        // ADD ip,ip,fp ; LDR/STR halves at [ip,#0] / [ip,#4]. Byte-verified tail
        // vs arm-none-eabi-as.
        let encoder = ArmEncoder::new_thumb2();
        // 0x1388 > 0xFFF (MemAddr is not Copy, so build it per use).

        let ld = encoder
            .encode(&ArmOp::I64Ldr {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                addr: MemAddr::reg_imm(Reg::R11, Reg::R0, 5000),
            })
            .expect("large-offset i64.load must lower, not skip");
        // MOVW ip,#0x1388 (4) + ADD ip,r0,ip (4) + ADD ip,ip,fp (4) + 2 LDR (8).
        assert_eq!(ld.len(), 20, "expected MOVW + 2×ADD + 2×LDR");
        // Must NOT be the small-offset `ADD.W ip, fp, r0` (0x0b 0xeb) prefix —
        // that path can only reach imm12 offsets.
        assert_ne!(
            &ld[0..2],
            &[0x0b, 0xeb],
            "must materialize the large offset"
        );
        // Effective base built in ip, then halves at [ip,#0] / [ip,#4].
        assert_eq!(
            &ld[4..20],
            &[
                0x00, 0xeb, 0x0c, 0x0c, // ADD.W ip, r0, ip
                0x0c, 0xeb, 0x0b, 0x0c, // ADD.W ip, ip, fp
                0xdc, 0xf8, 0x00, 0x00, // LDR.W r0, [ip, #0]
                0xdc, 0xf8, 0x04, 0x10, // LDR.W r1, [ip, #4]
            ],
            "large-offset i64.load must fold offset into ip and access [ip,#0]/[ip,#4]"
        );

        // Store: same base materialization, STR halves.
        let st = encoder
            .encode(&ArmOp::I64Str {
                rdlo: Reg::R2,
                rdhi: Reg::R3,
                addr: MemAddr::reg_imm(Reg::R11, Reg::R0, 5000),
            })
            .expect("large-offset i64.store must lower, not skip");
        assert_eq!(st.len(), 20);
        assert_eq!(
            &st[4..20],
            &[
                0x00, 0xeb, 0x0c, 0x0c, // ADD.W ip, r0, ip
                0x0c, 0xeb, 0x0b, 0x0c, // ADD.W ip, ip, fp
                0xcc, 0xf8, 0x00, 0x20, // STR.W r2, [ip, #0]
                0xcc, 0xf8, 0x04, 0x30, // STR.W r3, [ip, #4]
            ],
            "large-offset i64.store must fold offset into ip and access [ip,#0]/[ip,#4]"
        );

        // Small-offset (imm12) indexed access stays byte-identical (#372): the
        // effective base is a single `ADD.W ip, fp, r0` and the halves keep the
        // folded immediates — NO extra MOVW/ADD.
        let small = encoder
            .encode(&ArmOp::I64Ldr {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                addr: MemAddr::reg_imm(Reg::R11, Reg::R0, 8),
            })
            .unwrap();
        assert_eq!(
            &small[0..4],
            &[0x0b, 0xeb, 0x00, 0x0c],
            "small-offset indexed i64 must keep the single ADD.W ip, fp, r0"
        );
        assert_eq!(small.len(), 12, "ADD.W + 2×LDR.W (offset folded in imm12)");
    }

    #[test]
    fn test_encode_i64_str_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Str {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            addr: MemAddr::imm(Reg::SP, 0),
        };
        let code = encoder.encode(&op).unwrap();
        // Two STR instructions (lo at offset, hi at offset+4)
        assert!(code.len() >= 4, "I64Str should emit at least 4 bytes");
    }

    #[test]
    fn test_encode_i64_all_comparisons_thumb2() {
        let encoder = ArmEncoder::new_thumb2();

        let ops = vec![
            ArmOp::I64Ne {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64LtS {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64LtU {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64LeS {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64LeU {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64GtS {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64GtU {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64GeS {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
            ArmOp::I64GeU {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
                rmlo: Reg::R2,
                rmhi: Reg::R3,
            },
        ];

        for op in &ops {
            let code = encoder.encode(op).unwrap();
            assert!(
                code.len() >= 8,
                "i64 comparison {:?} should emit at least 8 bytes, got {}",
                op,
                code.len()
            );
        }
    }

    #[test]
    fn test_encode_i64_const_zero_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Const {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            value: 0,
        };
        let code = encoder.encode(&op).unwrap();
        // MOVW R0, #0 (4 bytes) + MOVW R1, #0 (4 bytes) = 8 bytes
        assert_eq!(code.len(), 8, "I64Const(0) should be 8 bytes");
    }

    #[test]
    fn test_encode_i64_const_negative_one_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::I64Const {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            value: -1, // 0xFFFF_FFFF_FFFF_FFFF
        };
        let code = encoder.encode(&op).unwrap();
        // MOVW + MOVT for lo (8 bytes) + MOVW + MOVT for hi (8 bytes) = 16 bytes
        assert_eq!(code.len(), 16, "I64Const(-1) should be 16 bytes");
    }

    // =========================================================================
    // Sub-word load/store encoding tests
    // =========================================================================

    #[test]
    fn test_encode_ldrb_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Ldrb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 4),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 LDRB should be 4 bytes");
        // LDRB R0, [R1, #4] = 0xE5D10004
        let encoded = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(encoded, 0xE5D10004, "Should encode LDRB R0, [R1, #4]");
    }

    #[test]
    fn test_encode_strb_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Strb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 STRB should be 4 bytes");
        // STRB R0, [R1, #0] = 0xE5C10000
        let encoded = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(encoded, 0xE5C10000, "Should encode STRB R0, [R1, #0]");
    }

    #[test]
    fn test_encode_ldrh_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Ldrh {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 2),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 LDRH should be 4 bytes");
    }

    #[test]
    fn test_encode_strh_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Strh {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 STRH should be 4 bytes");
    }

    #[test]
    fn test_encode_ldrsb_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Ldrsb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 LDRSB should be 4 bytes");
    }

    #[test]
    fn test_encode_ldrsh_arm32() {
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::Ldrsh {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 LDRSH should be 4 bytes");
    }

    #[test]
    fn test_encode_ldrb_thumb2_16bit() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Ldrb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 4),
        };
        let code = encoder.encode(&op).unwrap();
        // Low registers + small offset -> 16-bit encoding
        assert_eq!(
            code.len(),
            2,
            "Thumb-2 LDRB with small offset should be 16-bit"
        );
    }

    #[test]
    fn test_encode_ldrb_thumb2_32bit() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Ldrb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 100), // offset > 31 needs 32-bit
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            4,
            "Thumb-2 LDRB with large offset should be 32-bit"
        );
    }

    #[test]
    fn test_encode_strb_thumb2_16bit() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Strb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 10),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            2,
            "Thumb-2 STRB with small offset should be 16-bit"
        );
    }

    #[test]
    fn test_encode_ldrh_thumb2_16bit() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Ldrh {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 4), // offset aligned to 2, <= 62
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            2,
            "Thumb-2 LDRH with small aligned offset should be 16-bit"
        );
    }

    #[test]
    fn test_encode_strh_thumb2_16bit() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Strh {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 4),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            2,
            "Thumb-2 STRH with small aligned offset should be 16-bit"
        );
    }

    #[test]
    fn test_encode_ldrsb_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Ldrsb {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&op).unwrap();
        // LDRSB has no 16-bit immediate form, always 32-bit
        assert_eq!(code.len(), 4, "Thumb-2 LDRSB should be 32-bit");
    }

    #[test]
    fn test_encode_ldrsh_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::Ldrsh {
            rd: Reg::R0,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "Thumb-2 LDRSH should be 32-bit");
    }

    #[test]
    fn test_encode_memory_size_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MemorySize { rd: Reg::R0 };
        let code = encoder.encode(&op).unwrap();
        // R0 and R10 are not both low registers, so this needs careful handling
        assert!(!code.is_empty(), "MemorySize should produce code");
    }

    #[test]
    fn test_encode_memory_grow_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MemoryGrow {
            rd: Reg::R0,
            rn: Reg::R0,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MemoryGrow (MVN) should be 32-bit Thumb-2");
    }

    #[test]
    fn test_encode_subword_reg_offset_thumb2() {
        let encoder = ArmEncoder::new_thumb2();

        // LDRB with register offset
        let op = ArmOp::Ldrb {
            rd: Reg::R0,
            addr: MemAddr::reg(Reg::R1, Reg::R2),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            4,
            "Thumb-2 LDRB with reg offset should be 32-bit"
        );

        // STRB with register offset
        let op = ArmOp::Strb {
            rd: Reg::R0,
            addr: MemAddr::reg(Reg::R1, Reg::R2),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            4,
            "Thumb-2 STRB with reg offset should be 32-bit"
        );

        // LDRH with register offset
        let op = ArmOp::Ldrh {
            rd: Reg::R0,
            addr: MemAddr::reg(Reg::R1, Reg::R2),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            4,
            "Thumb-2 LDRH with reg offset should be 32-bit"
        );

        // STRH with register offset
        let op = ArmOp::Strh {
            rd: Reg::R0,
            addr: MemAddr::reg(Reg::R1, Reg::R2),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            4,
            "Thumb-2 STRH with reg offset should be 32-bit"
        );
    }

    #[test]
    fn test_encode_subword_reg_imm_offset_thumb2() {
        let encoder = ArmEncoder::new_thumb2();

        // LDRB with both register and immediate offset
        let op = ArmOp::Ldrb {
            rd: Reg::R0,
            addr: MemAddr::reg_imm(Reg::R1, Reg::R2, 4),
        };
        let code = encoder.encode(&op).unwrap();
        // ADD R12, R2, #4 (4 bytes) + LDRB R0, [R1, R12] (4 bytes) = 8 bytes
        assert_eq!(
            code.len(),
            8,
            "Thumb-2 LDRB with reg+imm offset should be 8 bytes"
        );
    }

    // ========================================================================
    // Helium MVE encoding tests
    // ========================================================================

    #[test]
    fn test_encode_mve_addi32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveAddI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code.len(),
            4,
            "MVE VADD.I32 should be 4 bytes (Thumb-2 32-bit)"
        );
    }

    #[test]
    fn test_encode_mve_subi16_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveSubI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S16,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VSUB.I16 should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_muli8_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveMulI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S8,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VMUL.I8 should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_bitwise_thumb2() {
        let encoder = ArmEncoder::new_thumb2();

        let ops = vec![
            ArmOp::MveAnd {
                qd: QReg::Q0,
                qn: QReg::Q1,
                qm: QReg::Q2,
            },
            ArmOp::MveOrr {
                qd: QReg::Q0,
                qn: QReg::Q1,
                qm: QReg::Q2,
            },
            ArmOp::MveEor {
                qd: QReg::Q0,
                qn: QReg::Q1,
                qm: QReg::Q2,
            },
            ArmOp::MveBic {
                qd: QReg::Q0,
                qn: QReg::Q1,
                qm: QReg::Q2,
            },
        ];
        for op in ops {
            let code = encoder.encode(&op).unwrap();
            assert_eq!(code.len(), 4, "MVE bitwise op should be 4 bytes");
        }
    }

    #[test]
    fn test_encode_mve_mvn_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveMvn {
            qd: QReg::Q0,
            qm: QReg::Q1,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VMVN should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_load_store_thumb2() {
        let encoder = ArmEncoder::new_thumb2();

        let load = ArmOp::MveLoad {
            qd: QReg::Q0,
            addr: MemAddr::imm(Reg::R0, 16),
        };
        let code = encoder.encode(&load).unwrap();
        assert_eq!(code.len(), 4, "MVE VLDRW.32 should be 4 bytes");

        let store = ArmOp::MveStore {
            qd: QReg::Q1,
            addr: MemAddr::imm(Reg::R1, 0),
        };
        let code = encoder.encode(&store).unwrap();
        assert_eq!(code.len(), 4, "MVE VSTRW.32 should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_const_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveConst {
            qd: QReg::Q0,
            bytes: [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0],
        };
        let code = encoder.encode(&op).unwrap();
        // Should be 4 words of (MOVW R12 + VMOV Sn) = 4 * (4+4) = 32 bytes min
        // Some words with hi16=0 skip MOVT, so length varies
        assert!(
            code.len() >= 24,
            "MVE const should produce multiple instructions"
        );
    }

    #[test]
    fn test_encode_mve_dup_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveDup {
            qd: QReg::Q0,
            rn: Reg::R0,
            size: MveSize::S32,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VDUP.32 should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_extract_lane_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveExtractLane {
            rd: Reg::R0,
            qn: QReg::Q1,
            lane: 2,
            size: MveSize::S32,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE extract lane should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_insert_lane_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveInsertLane {
            qd: QReg::Q0,
            rn: Reg::R1,
            lane: 3,
            size: MveSize::S32,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE insert lane should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_addf32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveAddF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VADD.F32 should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_divf32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveDivF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        };
        let code = encoder.encode(&op).unwrap();
        // Lane-wise: 4 x VDIV.F32 = 4 x 4 = 16 bytes
        assert_eq!(
            code.len(),
            16,
            "MVE VDIV.F32 (lane-wise) should be 16 bytes"
        );
    }

    #[test]
    fn test_encode_mve_sqrtf32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveSqrtF32 {
            qd: QReg::Q0,
            qm: QReg::Q1,
        };
        let code = encoder.encode(&op).unwrap();
        // Lane-wise: 4 x VSQRT.F32 = 4 x 4 = 16 bytes
        assert_eq!(
            code.len(),
            16,
            "MVE VSQRT.F32 (lane-wise) should be 16 bytes"
        );
    }

    #[test]
    fn test_encode_mve_negf32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveNegF32 {
            qd: QReg::Q0,
            qm: QReg::Q1,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VNEG.F32 should be 4 bytes");
    }

    #[test]
    fn test_encode_mve_absf32_thumb2() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::MveAbsF32 {
            qd: QReg::Q0,
            qm: QReg::Q1,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "MVE VABS.F32 should be 4 bytes");
    }

    /// VCR-RA-001 / immediate-folding precondition: pins the Thumb-2 `AND`
    /// immediate encoding for the byte range and documents its bound.
    ///
    /// The `And { Operand2::Imm }` encoder packs the low 12 bits straight into
    /// the `i:imm3:imm8` field WITHOUT applying ThumbExpandImm (the modified-
    /// immediate expansion). For `imm <= 0xFF` (e.g. gale's int8 clamps
    /// `#0x7e` / `#0x7f`) that is correct — `i:imm3 = 0000` means "imm8
    /// zero-extended". So `and r2, r0, #0x7e` encodes to the canonical
    /// `00 f0 7e 02`. For `imm >= 0x100` the field would need a true
    /// ThumbExpandImm pattern (rotation / replication), which is NOT
    /// implemented here — so **immediate folding must gate on `imm <= 0xFF`**
    /// until the encoder is hardened to ThumbExpandImm/Ok-or-Err (the
    /// "encoder must be Ok-or-Err, never silently wrong" principle, #180/#185).
    /// This bound covers the measured `flat_flight` waste (#209).
    #[test]
    fn and_immediate_encodes_correctly_in_byte_range_documents_fold_bound() {
        let encoder = ArmEncoder::new_thumb2();
        let op = ArmOp::And {
            rd: Reg::R2,
            rn: Reg::R0,
            op2: Operand2::Imm(0x7e),
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(
            code,
            vec![0x00, 0xf0, 0x7e, 0x02],
            "and r2, r0, #0x7e must encode to the canonical AND.W T1 (imm8=0x7e)"
        );
    }

    /// #255: the shared ThumbExpandImm reverse-encoder underpinning the
    /// data-processing immediate fix. Encodable modified immediates round-trip to
    /// the expected `i:imm3:imm8` field; a genuinely non-modified value is `None`
    /// (caller must materialize into a register). Note `1000 = 0xFA ror 30` *is*
    /// representable (field 0xF7A) — the old encoder mis-encoded it (raw 0x3E8);
    /// this encodes it correctly.
    #[test]
    fn try_thumb_expand_imm_encodes_modified_immediates() {
        assert_eq!(try_thumb_expand_imm(0x7e), Some(0x07e)); // zero-extended byte
        assert_eq!(try_thumb_expand_imm(0xff), Some(0x0ff));
        assert_eq!(try_thumb_expand_imm(0x0001_0001), Some(0x101)); // 0x00XY00XY
        assert_eq!(try_thumb_expand_imm(0xff00_ff00), Some(0x2ff)); // 0xXY00XY00
        assert_eq!(try_thumb_expand_imm(0xffff_ffff), Some(0x3ff)); // 0xXYXYXYXY
        assert_eq!(try_thumb_expand_imm(0x100), Some(0xf80)); // 0x80 ror 31
        assert_eq!(try_thumb_expand_imm(0x8000_0000), Some(0x400)); // 0x80 ror 8
        assert_eq!(try_thumb_expand_imm(1000), Some(0xf7a)); // 0xFA ror 30
        // Genuinely unrepresentable (bits too far apart for an 8-bit window).
        assert_eq!(try_thumb_expand_imm(0x101), None);
        assert_eq!(try_thumb_expand_imm(0x12345), None);
    }

    /// #255: CMP/ADDS/SUBS encode any valid modified immediate correctly, and
    /// ERROR (not silently mis-encode) on a genuinely unrepresentable one,
    /// forcing the selector to materialize into a register — closing the
    /// silent-miscompile class of #251/#253.
    #[test]
    fn cmp_adds_subs_immediate_error_on_non_modified_imm() {
        let encoder = ArmEncoder::new_thumb2();
        // cmp r0, #0xff → valid → Ok; cmp r0, #1000 → valid (0xFA ror 30) → Ok.
        assert!(encoder.encode_thumb32_cmp_imm(&Reg::R0, 0xff).is_ok());
        assert!(encoder.encode_thumb32_cmp_imm(&Reg::R0, 1000).is_ok());
        // cmp r0, #0x101 → NOT a modified immediate → Err (materialize-reg).
        assert!(
            encoder.encode_thumb32_cmp_imm(&Reg::R0, 0x101).is_err(),
            "cmp #0x101 must error, not compare the wrong constant"
        );
        assert!(
            encoder
                .encode_thumb32_adds(&Reg::R0, &Reg::R0, 0x101)
                .is_err()
        );
        assert!(
            encoder
                .encode_thumb32_subs(&Reg::R0, &Reg::R0, 0x101)
                .is_err()
        );
        // ...but a valid modified immediate still encodes.
        assert!(
            encoder
                .encode_thumb32_adds(&Reg::R0, &Reg::R0, 0x80)
                .is_ok()
        );
    }

    /// #257: MLA (multiply-accumulate) encodes as MLS without the bit-4 op flag.
    /// `mla r2, r3, r4, r8` (rd=r2, rn=r3, rm=r4, ra=r8) → Thumb-2 `03 fb 04 82`.
    #[test]
    fn mla_thumb2_encodes_correctly() {
        let encoder = ArmEncoder::new_thumb2();
        let code = encoder
            .encode(&ArmOp::Mla {
                rd: Reg::R2,
                rn: Reg::R3,
                rm: Reg::R4,
                ra: Reg::R8,
            })
            .unwrap();
        // hw1 = 0xFB03, hw2 = (8<<12)|(2<<8)|4 = 0x8204
        assert_eq!(code, vec![0x03, 0xfb, 0x04, 0x82]);
    }

    /// #259: LDR/STR (and sub-word) immediate-offset encoders truncated
    /// `offset & 0xFFF`, silently targeting the wrong address for offset >= 4096.
    /// They now error (the selector must use register-offset addressing) — the
    /// load/store sibling of the #253/#255 class. Offsets <= 4095 still encode.
    #[test]
    fn ldst_imm12_offset_errors_when_out_of_range() {
        let encoder = ArmEncoder::new_thumb2();
        // offset 0xFFF (4095): valid → Ok; ldr r0, [r1, #4095].
        assert!(
            encoder
                .encode_thumb32_ldr(&Reg::R0, &Reg::R1, 0xFFF)
                .is_ok()
        );
        // offset 0x1000 (4096): out of imm12 range → Err (not & 0xFFF → #0).
        assert!(
            encoder
                .encode_thumb32_ldr(&Reg::R0, &Reg::R1, 0x1000)
                .is_err(),
            "ldr offset 4096 must error, not wrap to 0"
        );
        assert!(
            encoder
                .encode_thumb32_str(&Reg::R0, &Reg::R1, 0x1000)
                .is_err()
        );
        assert!(
            encoder
                .encode_thumb32_ldrb_imm(&Reg::R0, &Reg::R1, 5000)
                .is_err()
        );
        assert!(
            encoder
                .encode_thumb32_strh_imm(&Reg::R0, &Reg::R1, 5000)
                .is_err()
        );
    }

    /// Latent miscompile fix: ADD/SUB with a >0xFF immediate (e.g.
    /// `add sp, sp, #frame` for a >=256-byte frame) used ADD.W (T3), whose
    /// `i:imm3:imm8` is a ThumbExpandImm modified immediate — so `#256` silently
    /// encoded as `#0` (stack corruption). Use ADDW/SUBW (T4), a PLAIN 12-bit
    /// immediate, for 0x100..=0xFFF; keep T3 for <=0xFF (bit-identical); error
    /// beyond 4095.
    #[test]
    fn add_sub_large_immediate_use_addw_subw_not_misencoded() {
        let encoder = ArmEncoder::new_thumb2();
        // add sp, sp, #256  →  ADDW (T4) SP, SP, #256  =  0d f2 00 1d
        assert_eq!(
            encoder
                .encode(&ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(256),
                })
                .unwrap(),
            vec![0x0d, 0xf2, 0x00, 0x1d],
            "add sp,sp,#256 must be ADDW (plain imm12), not a mis-encoded ADD.W"
        );
        // sub sp, sp, #256  →  SUBW (T4) SP, SP, #256  =  ad f2 00 1d
        assert_eq!(
            encoder
                .encode(&ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(256),
                })
                .unwrap(),
            vec![0xad, 0xf2, 0x00, 0x1d],
        );
        // > 4095 has no single-instruction encoding → error, not silent wrong.
        assert!(
            encoder
                .encode(&ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(5000),
                })
                .is_err(),
            "add #5000 must error (no single ADDW), not mis-encode"
        );
    }

    /// Closes the data-proc immediate class: AND and CMN now go through
    /// `try_thumb_expand_imm` like ORR/EOR/CMP — correct for any modified
    /// immediate, `Err` (not raw-pack / NOP) on an un-encodable one. The byte
    /// range stays bit-identical (`and r2,r0,#0x7e` is unchanged).
    #[test]
    fn and_cmn_immediate_thumb_expand_else_error() {
        let encoder = ArmEncoder::new_thumb2();
        // byte range unchanged (bit-identical with the pre-retrofit encoding)
        assert_eq!(
            encoder
                .encode(&ArmOp::And {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Imm(0x7e),
                })
                .unwrap(),
            vec![0x00, 0xf0, 0x7e, 0x02],
        );
        // a valid replicated modified immediate now encodes (was silently wrong)
        assert!(
            encoder
                .encode(&ArmOp::And {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Imm(0xff00ff00u32 as i32),
                })
                .is_ok()
        );
        // a genuinely un-encodable immediate errors (AND was raw-pack; CMN NOP)
        assert!(
            encoder
                .encode(&ArmOp::And {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Imm(0x101),
                })
                .is_err()
        );
        assert!(
            encoder
                .encode(&ArmOp::Cmn {
                    rn: Reg::R0,
                    op2: Operand2::Imm(0x101),
                })
                .is_err(),
            "CMN #0x101 must error, not emit a NOP"
        );
    }

    /// VCR-RA-001: ORR/EOR with a small immediate must encode the real
    /// instruction (not a silent `0xBF00` NOP). Pins the byte range and the
    /// Ok-or-Err bound that makes future Or/Eor immediate folding safe.
    #[test]
    fn orr_eor_immediate_encode_in_byte_range_else_error() {
        let encoder = ArmEncoder::new_thumb2();
        // orr r2, r0, #0x7e  →  ORR.W T1, imm8=0x7e
        assert_eq!(
            encoder
                .encode(&ArmOp::Orr {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Imm(0x7e),
                })
                .unwrap(),
            vec![0x40, 0xf0, 0x7e, 0x02],
        );
        // eor r2, r0, #0x7e  →  EOR.W T1, imm8=0x7e
        assert_eq!(
            encoder
                .encode(&ArmOp::Eor {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Imm(0x7e),
                })
                .unwrap(),
            vec![0x80, 0xf0, 0x7e, 0x02],
        );
        // Out-of-range immediates error rather than silently mis-encode / NOP.
        assert!(
            encoder
                .encode(&ArmOp::Orr {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Imm(0x140),
                })
                .is_err(),
            "ORR #0x140 must error, not emit a NOP"
        );
    }

    #[test]
    fn test_encode_mve_different_qregs() {
        let encoder = ArmEncoder::new_thumb2();

        // Test that different Q-register numbers produce different encodings
        let op1 = ArmOp::MveAddI {
            qd: QReg::Q0,
            qn: QReg::Q0,
            qm: QReg::Q0,
            size: MveSize::S32,
        };
        let op2 = ArmOp::MveAddI {
            qd: QReg::Q3,
            qn: QReg::Q5,
            qm: QReg::Q7,
            size: MveSize::S32,
        };
        let code1 = encoder.encode(&op1).unwrap();
        let code2 = encoder.encode(&op2).unwrap();
        assert_ne!(
            code1, code2,
            "Different Q-registers should produce different encodings"
        );
    }

    #[test]
    fn test_encode_mve_arm32_nop() {
        // MVE instructions on ARM32 encoder should produce NOP (only Thumb-2 supported)
        let encoder = ArmEncoder::new_arm32();
        let op = ArmOp::MveAddI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        };
        let code = encoder.encode(&op).unwrap();
        assert_eq!(code.len(), 4, "ARM32 MVE should be 4 bytes (NOP)");
        // NOP in ARM32 is 0xE1A00000 (MOV R0, R0)
        let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(instr, 0xE1A00000, "ARM32 MVE should encode as NOP");
    }
}
