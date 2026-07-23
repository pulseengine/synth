//! ARM Semantics Encoding to SMT
//!
//! Encodes ARM operation semantics as SMT bitvector formulas.
//! Each ARM operation is translated to a mathematical formula that precisely
//! captures its behavior, including register updates and condition flags.

use crate::term::{BV, Bool};
use std::collections::HashMap;
use synth_synthesis::rules::{ArmOp, Operand2, Reg, VfpReg};

/// ARM processor state representation in SMT
///
/// Z3 0.19 uses thread-local context -- no lifetime parameters needed.
pub struct ArmState {
    /// General purpose registers R0-R15
    pub registers: Vec<BV>,
    /// Condition flags (N, Z, C, V)
    pub flags: ConditionFlags,
    /// VFP (floating-point) registers
    pub vfp_registers: Vec<BV>,
    /// Memory model (simplified for bounded verification)
    pub memory: Vec<BV>,
    /// Local variables (for WASM verification)
    pub locals: Vec<BV>,
    /// Global variables (for WASM verification)
    pub globals: Vec<BV>,
    /// VCR-VER-002 (#166): the accumulated condition under which the executed
    /// sequence TRAPS (reaches a `UDF`). `false` in a fresh state; `encode_op`
    /// sets it unconditionally on a `Udf`, and the branch-taking executor
    /// [`ArmSemantics::encode_sequence_br`] conditions it on the path guard the
    /// `UDF` is reached under — this is the ARM-side trap term the
    /// trap-preservation VC compares against the WASM op's trap condition.
    pub may_trap: Bool,
}

/// ARM condition flags
pub struct ConditionFlags {
    pub n: Bool, // Negative
    pub z: Bool, // Zero
    pub c: Bool, // Carry
    pub v: Bool, // Overflow
}

impl ArmState {
    /// Create a new ARM state with symbolic values
    pub fn new_symbolic() -> Self {
        let registers = (0..16)
            .map(|i| BV::new_const(format!("r{}", i), 32))
            .collect();

        let flags = ConditionFlags {
            n: Bool::new_const("flag_n"),
            z: Bool::new_const("flag_z"),
            c: Bool::new_const("flag_c"),
            v: Bool::new_const("flag_v"),
        };

        let memory = (0..256)
            .map(|i| BV::new_const(format!("mem_{}", i), 32))
            .collect();

        let locals = (0..32)
            .map(|i| BV::new_const(format!("local_{}", i), 32))
            .collect();

        let globals = (0..16)
            .map(|i| BV::new_const(format!("global_{}", i), 32))
            .collect();

        let vfp_registers = (0..48)
            .map(|i| BV::new_const(format!("vfp_{}", i), 32))
            .collect();

        Self {
            registers,
            flags,
            vfp_registers,
            memory,
            locals,
            globals,
            may_trap: Bool::from_bool(false),
        }
    }

    /// Get register value
    pub fn get_reg(&self, reg: &Reg) -> &BV {
        let index = reg_to_index(reg);
        &self.registers[index]
    }

    /// Set register value
    pub fn set_reg(&mut self, reg: &Reg, value: BV) {
        let index = reg_to_index(reg);
        self.registers[index] = value;
    }

    /// Get VFP register value
    pub fn get_vfp_reg(&self, reg: &VfpReg) -> &BV {
        let index = vfp_reg_to_index(reg);
        &self.vfp_registers[index]
    }

    /// Set VFP register value
    pub fn set_vfp_reg(&mut self, reg: &VfpReg, value: BV) {
        let index = vfp_reg_to_index(reg);
        self.vfp_registers[index] = value;
    }
}

/// Convert register enum to index
fn reg_to_index(reg: &Reg) -> usize {
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

/// Convert VFP register enum to index
fn vfp_reg_to_index(reg: &VfpReg) -> usize {
    match reg {
        // Single-precision registers S0-S31 (indices 0-31)
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
        // Double-precision registers D0-D15 (indices 32-47)
        // Note: D0 = S0:S1, D1 = S2:S3, etc.
        // We store the "low" part of each D register
        VfpReg::D0 => 32,
        VfpReg::D1 => 33,
        VfpReg::D2 => 34,
        VfpReg::D3 => 35,
        VfpReg::D4 => 36,
        VfpReg::D5 => 37,
        VfpReg::D6 => 38,
        VfpReg::D7 => 39,
        VfpReg::D8 => 40,
        VfpReg::D9 => 41,
        VfpReg::D10 => 42,
        VfpReg::D11 => 43,
        VfpReg::D12 => 44,
        VfpReg::D13 => 45,
        VfpReg::D14 => 46,
        VfpReg::D15 => 47,
    }
}

/// ARM semantics encoder
///
/// Z3 0.19 uses thread-local context -- no lifetime parameters needed.
pub struct ArmSemantics;

impl Default for ArmSemantics {
    fn default() -> Self {
        Self::new()
    }
}

impl ArmSemantics {
    /// Create a new ARM semantics encoder
    pub fn new() -> Self {
        Self
    }

    /// Encode an ARM operation and return the resulting state
    ///
    /// This models the effect of executing the ARM instruction on the processor state.
    pub fn encode_op(&self, op: &ArmOp, state: &mut ArmState) {
        match op {
            ArmOp::Add { rd, rn, op2 } => {
                let rn_val = state.get_reg(rn).clone();
                let op2_val = self.evaluate_operand2(op2, state);
                let result = rn_val.bvadd(&op2_val);
                state.set_reg(rd, result);
            }

            ArmOp::Sub { rd, rn, op2 } => {
                let rn_val = state.get_reg(rn).clone();
                let op2_val = self.evaluate_operand2(op2, state);
                let result = rn_val.bvsub(&op2_val);
                state.set_reg(rd, result);
            }

            ArmOp::Mul { rd, rn, rm } => {
                let rn_val = state.get_reg(rn).clone();
                let rm_val = state.get_reg(rm).clone();
                let result = rn_val.bvmul(&rm_val);
                state.set_reg(rd, result);
            }

            ArmOp::Umull { rdlo, rdhi, rn, rm } => {
                // {rdhi:rdlo} = zext64(rn) * zext64(rm); rdhi = high 32 bits.
                let rn64 = state.get_reg(rn).zero_ext(32);
                let rm64 = state.get_reg(rm).zero_ext(32);
                let prod = rn64.bvmul(&rm64);
                state.set_reg(rdlo, prod.extract(31, 0));
                state.set_reg(rdhi, prod.extract(63, 32));
            }

            ArmOp::Sdiv { rd, rn, rm } => {
                let rn_val = state.get_reg(rn).clone();
                let rm_val = state.get_reg(rm).clone();
                let result = rn_val.bvsdiv(&rm_val);
                state.set_reg(rd, result);
            }

            ArmOp::Udiv { rd, rn, rm } => {
                let rn_val = state.get_reg(rn).clone();
                let rm_val = state.get_reg(rm).clone();
                let result = rn_val.bvudiv(&rm_val);
                state.set_reg(rd, result);
            }

            ArmOp::Mls { rd, rn, rm, ra } => {
                // MLS (Multiply and Subtract): Rd = Ra - Rn * Rm
                // Used for remainder operations: a % b = a - (a/b) * b
                let rn_val = state.get_reg(rn).clone();
                let rm_val = state.get_reg(rm).clone();
                let ra_val = state.get_reg(ra).clone();
                let product = rn_val.bvmul(&rm_val);
                let result = ra_val.bvsub(&product);
                state.set_reg(rd, result);
            }

            ArmOp::And { rd, rn, op2 } => {
                let rn_val = state.get_reg(rn).clone();
                let op2_val = self.evaluate_operand2(op2, state);
                let result = rn_val.bvand(&op2_val);
                state.set_reg(rd, result);
            }

            ArmOp::Orr { rd, rn, op2 } => {
                let rn_val = state.get_reg(rn).clone();
                let op2_val = self.evaluate_operand2(op2, state);
                let result = rn_val.bvor(&op2_val);
                state.set_reg(rd, result);
            }

            ArmOp::Eor { rd, rn, op2 } => {
                let rn_val = state.get_reg(rn).clone();
                let op2_val = self.evaluate_operand2(op2, state);
                let result = rn_val.bvxor(&op2_val);
                state.set_reg(rd, result);
            }

            ArmOp::Lsl { rd, rn, shift } => {
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(*shift as i64, 32);
                let result = rn_val.bvshl(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Lsr { rd, rn, shift } => {
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(*shift as i64, 32);
                let result = rn_val.bvlshr(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Asr { rd, rn, shift } => {
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(*shift as i64, 32);
                let result = rn_val.bvashr(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Ror { rd, rn, shift } => {
                // Rotate right - ARM ROR instruction
                // ROR(x, n) rotates x right by n positions
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(*shift as i64, 32);
                let result = rn_val.bvrotr(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Mov { rd, op2 } => {
                let op2_val = self.evaluate_operand2(op2, state);
                state.set_reg(rd, op2_val);
            }

            ArmOp::Mvn { rd, op2 } => {
                let op2_val = self.evaluate_operand2(op2, state);
                let result = op2_val.bvnot();
                state.set_reg(rd, result);
            }

            ArmOp::Cmp { rn, op2 } => {
                // Compare sets flags but doesn't write to a register
                // CMP performs: Rn - Op2 and updates all condition flags
                let rn_val = state.get_reg(rn).clone();
                let op2_val = self.evaluate_operand2(op2, state);

                // Compute result of subtraction
                let result = rn_val.bvsub(&op2_val);

                // Update all condition flags
                self.update_flags_sub(state, &rn_val, &op2_val, &result);
            }

            ArmOp::Clz { rd, rm } => {
                // Count leading zeros - ARM CLZ instruction
                // Uses binary search algorithm matching WASM i32.clz semantics
                let input = state.get_reg(rm).clone();
                let result = self.encode_clz(&input);
                state.set_reg(rd, result);
            }

            ArmOp::Rbit { rd, rm } => {
                // Reverse bits - ARM RBIT instruction
                // Reverses the bit order in a 32-bit value
                let input = state.get_reg(rm).clone();
                let result = self.encode_rbit(&input);
                state.set_reg(rd, result);
            }

            ArmOp::Popcnt { rd, rm } => {
                // Population count - count number of 1 bits
                // This is a pseudo-instruction for verification
                let input = state.get_reg(rm).clone();
                let result = self.encode_popcnt(&input);
                state.set_reg(rd, result);
            }

            ArmOp::Nop => {
                // No operation - state unchanged
            }

            ArmOp::SetCond { rd, cond } => {
                // SetCond evaluates a condition based on NZCV flags and sets rd to 0 or 1
                // This is a pseudo-instruction for verification purposes
                let cond_result = self.evaluate_condition(cond, &state.flags);
                let result = self.bool_to_bv32(&cond_result);
                state.set_reg(rd, result);
            }

            ArmOp::Select {
                rd,
                rval1,
                rval2,
                rcond,
            } => {
                // Select operation: if rcond != 0, select rval1, else rval2
                // This is a pseudo-instruction for verification purposes
                let val1 = state.get_reg(rval1).clone();
                let val2 = state.get_reg(rval2).clone();
                let cond = state.get_reg(rcond).clone();
                let zero = BV::from_i64(0, 32);
                let cond_bool = cond.eq(&zero).not(); // cond != 0
                let result = cond_bool.ite(&val1, &val2);
                state.set_reg(rd, result);
            }

            // Memory operations simplified for now
            ArmOp::Ldr { rd, addr: _ } => {
                // Load from memory
                // Simplified: return symbolic value
                let result = BV::new_const(format!("load_{:?}", rd), 32);
                state.set_reg(rd, result);
            }

            ArmOp::Str { rd: _, addr: _ } => {
                // Store to memory
                // Simplified: memory updates not fully modeled yet
            }

            // Control flow operations
            ArmOp::B { label: _ } => {
                // Branch - would update PC in full model
                // For bounded verification, we treat this symbolically
            }

            ArmOp::Bl { label: _ } => {
                // Branch with link - would update PC and LR
            }

            ArmOp::Bx { rm: _ } => {
                // Branch and exchange - would update PC
            }

            // Local/Global variable access (pseudo-instructions for verification)
            ArmOp::LocalGet { rd, index } => {
                // Load local variable into register
                let value = state
                    .locals
                    .get(*index as usize)
                    .cloned()
                    .unwrap_or_else(|| BV::new_const(format!("local_{}", index), 32));
                state.set_reg(rd, value);
            }

            ArmOp::LocalSet { rs, index } => {
                // Store register into local variable
                let value = state.get_reg(rs).clone();
                if let Some(local) = state.locals.get_mut(*index as usize) {
                    *local = value;
                }
            }

            ArmOp::LocalTee { rd, rs, index } => {
                // Store register into local variable and also copy to destination
                let value = state.get_reg(rs).clone();
                if let Some(local) = state.locals.get_mut(*index as usize) {
                    *local = value.clone();
                }
                state.set_reg(rd, value);
            }

            ArmOp::GlobalGet { rd, index } => {
                // Load global variable into register
                let value = state
                    .globals
                    .get(*index as usize)
                    .cloned()
                    .unwrap_or_else(|| BV::new_const(format!("global_{}", index), 32));
                state.set_reg(rd, value);
            }

            ArmOp::GlobalSet { rs, index } => {
                // Store register into global variable
                let value = state.get_reg(rs).clone();
                if let Some(global) = state.globals.get_mut(*index as usize) {
                    *global = value;
                }
            }

            ArmOp::BrTable {
                rd,
                index_reg,
                targets,
                default,
            } => {
                // Multi-way branch based on index
                // For verification, we model the control flow symbolically
                let _index = state.get_reg(index_reg).clone();
                let result = BV::new_const(format!("br_table_{}_{}", targets.len(), default), 32);
                state.set_reg(rd, result);
            }

            ArmOp::Call { rd, func_idx } => {
                // Function call - model result symbolically
                let result = BV::new_const(format!("call_{}", func_idx), 32);
                state.set_reg(rd, result);
            }

            ArmOp::CallIndirect {
                rd,
                type_idx,
                table_index_reg,
                // #642: the bounds guard is a control-flow effect (trap), not
                // modeled by the symbolic call result. #650: the table base
                // offset only changes WHICH pointer is loaded, not the
                // symbolic result shape. #664: the null check is likewise a
                // trap (control-flow effect) on the loaded pointer.
                table_size: _,
                table_byte_offset: _,
                null_check: _,
                // #676: the runtime type check is likewise a trap
                // (control-flow effect) on the sidecar-loaded class id.
                type_check: _,
            } => {
                // Indirect function call through table
                let _table_index = state.get_reg(table_index_reg).clone();
                let result = BV::new_const(format!("call_indirect_{}", type_idx), 32);
                state.set_reg(rd, result);
            }

            // ================================================================
            // i64 Operations (Phase 2) - Simplified implementation
            // ================================================================
            // These use register pairs on ARM32 but simplified to single
            // registers for initial implementation
            ArmOp::I64Const { rdlo, rdhi, value } => {
                // Load 64-bit constant into register pair
                let low32 = (*value as u32) as i64;
                let high32 = *value >> 32;
                state.set_reg(rdlo, BV::from_i64(low32, 32));
                state.set_reg(rdhi, BV::from_i64(high32, 32));
            }

            ArmOp::I64Add {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // 64-bit addition with register pairs and carry propagation
                // ARM: ADDS rdlo, rnlo, rmlo  ; Add low parts, set carry
                //      ADC  rdhi, rnhi, rmhi  ; Add high parts with carry

                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                // Low part: simple addition
                let result_low = n_low.bvadd(&m_low);
                state.set_reg(rdlo, result_low.clone());

                // Detect carry: overflow occurred if result < either operand
                // For unsigned: carry = (result_low < n_low)
                let carry = result_low.bvult(&n_low);
                let carry_bv = carry.ite(BV::from_i64(1, 32), BV::from_i64(0, 32));

                // High part: add with carry
                let high_sum = n_high.bvadd(&m_high);
                let result_high = high_sum.bvadd(&carry_bv);
                state.set_reg(rdhi, result_high);
            }

            ArmOp::I64Eqz { rd, rnlo, rnhi } => {
                // Check if 64-bit value is zero
                // True if both low and high parts are zero
                let zero = BV::from_i64(0, 32);
                let low_zero = state.get_reg(rnlo).eq(&zero);
                let high_zero = state.get_reg(rnhi).eq(&zero);
                let both_zero = Bool::and(&[&low_zero, &high_zero]);
                let result = self.bool_to_bv32(&both_zero);
                state.set_reg(rd, result);
            }

            ArmOp::I32WrapI64 { rd, rnlo } => {
                // Wrap 64-bit to 32-bit (take low 32 bits)
                let low_val = state.get_reg(rnlo).clone();
                state.set_reg(rd, low_val);
            }

            ArmOp::I64ExtendI32S { rdlo, rdhi, rn } => {
                // Sign-extend 32-bit to 64-bit
                let value = state.get_reg(rn).clone();
                state.set_reg(rdlo, value.clone());

                // High part is sign extension (all 0s or all 1s based on sign bit)
                let sign_bit = value.extract(31, 31); // Extract bit 31
                let all_ones = BV::from_i64(-1, 32);
                let zero = BV::from_i64(0, 32);
                // If sign bit is 1, high = 0xFFFFFFFF, else high = 0
                let high_val = sign_bit.eq(BV::from_i64(1, 1)).ite(&all_ones, &zero);
                state.set_reg(rdhi, high_val);
            }

            ArmOp::I64ExtendI32U { rdlo, rdhi, rn } => {
                // Zero-extend 32-bit to 64-bit
                let value = state.get_reg(rn).clone();
                state.set_reg(rdlo, value);
                // High part is always zero for unsigned extend
                state.set_reg(rdhi, BV::from_i64(0, 32));
            }

            ArmOp::I64Sub {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // 64-bit subtraction with register pairs and borrow propagation
                // ARM: SUBS rdlo, rnlo, rmlo  ; Subtract low parts, set borrow
                //      SBC  rdhi, rnhi, rmhi  ; Subtract high parts with borrow

                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                // Low part: simple subtraction
                let result_low = n_low.bvsub(&m_low);
                state.set_reg(rdlo, result_low.clone());

                // Detect borrow: borrow occurred if n_low < m_low (unsigned)
                let borrow = n_low.bvult(&m_low);
                let borrow_bv = borrow.ite(BV::from_i64(1, 32), BV::from_i64(0, 32));

                // High part: subtract with borrow
                let high_diff = n_high.bvsub(&m_high);
                let result_high = high_diff.bvsub(&borrow_bv);
                state.set_reg(rdhi, result_high);
            }

            ArmOp::I64Mul {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                // 64-bit multiplication: (a_hi:a_lo) * (b_hi:b_lo) → (result_hi:result_lo)
                // Algorithm for 64x64→64 bit multiplication:
                // result = (a_hi * b_lo * 2^32) + (a_lo * b_hi * 2^32) + (a_lo * b_lo)
                // Only the low 64 bits are kept

                let a_lo = state.get_reg(rn_lo).clone();
                let a_hi = state.get_reg(rn_hi).clone();
                let b_lo = state.get_reg(rm_lo).clone();
                let b_hi = state.get_reg(rm_hi).clone();

                // Low part: a_lo * b_lo (32x32→64, we need both parts)
                // For SMT, we can use bvmul which gives 32-bit result (truncated)
                let lo_lo = a_lo.bvmul(&b_lo);
                state.set_reg(rd_lo, lo_lo.clone());

                // For the high part, we need to handle overflow from a_lo * b_lo
                // and add the cross products: a_hi * b_lo + a_lo * b_hi
                //
                // Simplified approach: use symbolic representation for now
                // TODO: Implement full 64-bit multiplication with proper overflow handling
                // This requires 64-bit bitvector intermediate computations

                // Cross products (take low 32 bits of each)
                let hi_lo = a_hi.bvmul(&b_lo); // a_hi * b_lo (low 32 bits)
                let lo_hi = a_lo.bvmul(&b_hi); // a_lo * b_hi (low 32 bits)

                // High part approximation (missing carry from a_lo * b_lo)
                // result_hi ≈ hi_lo + lo_hi
                let hi_sum = hi_lo.bvadd(&lo_hi);
                state.set_reg(rd_hi, hi_sum);

                // Note: This is a simplified implementation. A complete implementation
                // would need to:
                // 1. Extract high 32 bits of (a_lo * b_lo)
                // 2. Add that to the cross products
                // 3. Handle carries properly
            }

            // ========================================================================
            // i64 Division and Remainder
            // ========================================================================
            // Note: Full 64-bit division on ARM32 requires library calls or
            // very complex multi-instruction sequences. For verification, we model
            // the results symbolically.
            ArmOp::I64DivS { rdlo, rdhi, .. } => {
                // Signed 64-bit division
                // Real implementation would require __aeabi_ldivmod or equivalent
                // For verification, return symbolic values
                state.set_reg(rdlo, BV::new_const("i64_divs_lo", 32));
                state.set_reg(rdhi, BV::new_const("i64_divs_hi", 32));
            }

            ArmOp::I64DivU { rdlo, rdhi, .. } => {
                // Unsigned 64-bit division
                // Real implementation would require __aeabi_uldivmod or equivalent
                // For verification, return symbolic values
                state.set_reg(rdlo, BV::new_const("i64_divu_lo", 32));
                state.set_reg(rdhi, BV::new_const("i64_divu_hi", 32));
            }

            ArmOp::I64RemS { rdlo, rdhi, .. } => {
                // Signed 64-bit remainder (modulo)
                // Real implementation would require __aeabi_ldivmod or equivalent
                // For verification, return symbolic values
                state.set_reg(rdlo, BV::new_const("i64_rems_lo", 32));
                state.set_reg(rdhi, BV::new_const("i64_rems_hi", 32));
            }

            ArmOp::I64RemU { rdlo, rdhi, .. } => {
                // Unsigned 64-bit remainder (modulo)
                // Real implementation would require __aeabi_uldivmod or equivalent
                // For verification, return symbolic values
                state.set_reg(rdlo, BV::new_const("i64_remu_lo", 32));
                state.set_reg(rdhi, BV::new_const("i64_remu_hi", 32));
            }

            ArmOp::I64And {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                state.set_reg(rdlo, n_low.bvand(&m_low));

                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();
                state.set_reg(rdhi, n_high.bvand(&m_high));
            }

            ArmOp::I64Or {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                state.set_reg(rdlo, n_low.bvor(&m_low));

                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();
                state.set_reg(rdhi, n_high.bvor(&m_high));
            }

            ArmOp::I64Xor {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                state.set_reg(rdlo, n_low.bvxor(&m_low));

                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();
                state.set_reg(rdhi, n_high.bvxor(&m_high));
            }

            ArmOp::I64Eq {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let low_eq = n_low.eq(&m_low);
                let high_eq = n_high.eq(&m_high);
                let both_eq = Bool::and(&[&low_eq, &high_eq]);
                let result = self.bool_to_bv32(&both_eq);
                state.set_reg(rd, result);
            }

            ArmOp::I64LtS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Signed less than: n < m
                // Compare high parts first (signed), tiebreak with low parts (unsigned)
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                // High parts comparison (signed)
                let high_lt = n_high.bvslt(&m_high);
                let high_eq = n_high.eq(&m_high);

                // Low parts comparison (unsigned)
                let low_lt = n_low.bvult(&m_low);

                // Result: high_lt OR (high_eq AND low_lt)
                let eq_and_low = Bool::and(&[&high_eq, &low_lt]);
                let result_bool = Bool::or(&[&high_lt, &eq_and_low]);
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64LtU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Unsigned less than: n < m
                // Compare high parts first (unsigned), tiebreak with low parts (unsigned)
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                // High parts comparison (unsigned)
                let high_lt = n_high.bvult(&m_high);
                let high_eq = n_high.eq(&m_high);

                // Low parts comparison (unsigned)
                let low_lt = n_low.bvult(&m_low);

                // Result: high_lt OR (high_eq AND low_lt)
                let eq_and_low = Bool::and(&[&high_eq, &low_lt]);
                let result_bool = Bool::or(&[&high_lt, &eq_and_low]);
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64Ne {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Not equal: !(n == m)
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let low_eq = n_low.eq(&m_low);
                let high_eq = n_high.eq(&m_high);
                let both_eq = Bool::and(&[&low_eq, &high_eq]);
                let not_eq = both_eq.not();
                let result = self.bool_to_bv32(&not_eq);
                state.set_reg(rd, result);
            }

            ArmOp::I64LeS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Signed less than or equal: n <= m
                // Equivalent to: n < m OR n == m
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let high_lt = n_high.bvslt(&m_high);
                let high_eq = n_high.eq(&m_high);
                let low_le = n_low.bvule(&m_low); // Low parts unsigned LE

                let eq_and_le = Bool::and(&[&high_eq, &low_le]);
                let result_bool = Bool::or(&[&high_lt, &eq_and_le]);
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64LeU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Unsigned less than or equal: n <= m
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let high_lt = n_high.bvult(&m_high);
                let high_eq = n_high.eq(&m_high);
                let low_le = n_low.bvule(&m_low);

                let eq_and_le = Bool::and(&[&high_eq, &low_le]);
                let result_bool = Bool::or(&[&high_lt, &eq_and_le]);
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64GtS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Signed greater than: n > m
                // Equivalent to: m < n
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let high_gt = n_high.bvsgt(&m_high);
                let high_eq = n_high.eq(&m_high);
                let low_gt = n_low.bvugt(&m_low); // Low parts unsigned GT

                let eq_and_gt = Bool::and(&[&high_eq, &low_gt]);
                let result_bool = Bool::or(&[&high_gt, &eq_and_gt]);
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64GtU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Unsigned greater than: n > m
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let high_gt = n_high.bvugt(&m_high);
                let high_eq = n_high.eq(&m_high);
                let low_gt = n_low.bvugt(&m_low);

                let eq_and_gt = Bool::and(&[&high_eq, &low_gt]);
                let result_bool = Bool::or(&[&high_gt, &eq_and_gt]);
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64GeS {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Signed greater than or equal: n >= m
                // Equivalent to: !(n < m)
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let high_lt = n_high.bvslt(&m_high);
                let high_eq = n_high.eq(&m_high);
                let low_lt = n_low.bvult(&m_low);

                let eq_and_lt = Bool::and(&[&high_eq, &low_lt]);
                let lt_bool = Bool::or(&[&high_lt, &eq_and_lt]);
                let result_bool = lt_bool.not(); // GE is !(LT)
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            ArmOp::I64GeU {
                rd,
                rnlo,
                rnhi,
                rmlo,
                rmhi,
            } => {
                // Unsigned greater than or equal: n >= m
                // Equivalent to: !(n < m)
                let n_low = state.get_reg(rnlo).clone();
                let m_low = state.get_reg(rmlo).clone();
                let n_high = state.get_reg(rnhi).clone();
                let m_high = state.get_reg(rmhi).clone();

                let high_lt = n_high.bvult(&m_high);
                let high_eq = n_high.eq(&m_high);
                let low_lt = n_low.bvult(&m_low);

                let eq_and_lt = Bool::and(&[&high_eq, &low_lt]);
                let lt_bool = Bool::or(&[&high_lt, &eq_and_lt]);
                let result_bool = lt_bool.not(); // GE is !(LT)
                let result = self.bool_to_bv32(&result_bool);
                state.set_reg(rd, result);
            }

            // ================================================================
            // i64 Shift Operations
            // ================================================================
            ArmOp::I64Shl {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi: _,
            } => {
                // 64-bit left shift: (n_hi:n_lo) << shift
                // WASM spec: shift amount is modulo 64
                let n_lo = state.get_reg(rn_lo).clone();
                let n_hi = state.get_reg(rn_hi).clone();
                let shift_amt = state.get_reg(rm_lo).clone();

                // Modulo 64: shift_amt = shift_amt & 63
                let shift_mod = shift_amt.bvand(BV::from_i64(63, 32));

                // If shift < 32: normal shift with bits moving from low to high
                // If shift >= 32: low becomes 0, high gets shifted low part
                let shift_32 = BV::from_i64(32, 32);
                let is_large = shift_mod.bvuge(&shift_32); // shift >= 32

                // Small shift (< 32):
                // result_lo = n_lo << shift
                // result_hi = (n_hi << shift) | (n_lo >> (32 - shift))
                let result_lo_small = n_lo.bvshl(&shift_mod);
                let shift_complement = shift_32.bvsub(&shift_mod);
                let bits_to_high = n_lo.bvlshr(&shift_complement);
                let result_hi_small = n_hi.bvshl(&shift_mod).bvor(&bits_to_high);

                // Large shift (>= 32):
                // result_lo = 0
                // result_hi = n_lo << (shift - 32)
                let zero = BV::from_i64(0, 32);
                let shift_minus_32 = shift_mod.bvsub(&shift_32);
                let result_lo_large = zero.clone();
                let result_hi_large = n_lo.bvshl(&shift_minus_32);

                // Select based on shift size
                let result_lo = is_large.ite(&result_lo_large, &result_lo_small);
                let result_hi = is_large.ite(&result_hi_large, &result_hi_small);

                state.set_reg(rd_lo, result_lo);
                state.set_reg(rd_hi, result_hi);
            }

            ArmOp::I64ShrU {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi: _,
            } => {
                // 64-bit logical (unsigned) right shift
                let n_lo = state.get_reg(rn_lo).clone();
                let n_hi = state.get_reg(rn_hi).clone();
                let shift_amt = state.get_reg(rm_lo).clone();

                let shift_mod = shift_amt.bvand(BV::from_i64(63, 32));
                let shift_32 = BV::from_i64(32, 32);
                let is_large = shift_mod.bvuge(&shift_32);

                // Small shift (< 32):
                // result_hi = n_hi >> shift
                // result_lo = (n_lo >> shift) | (n_hi << (32 - shift))
                let result_hi_small = n_hi.bvlshr(&shift_mod);
                let shift_complement = shift_32.bvsub(&shift_mod);
                let bits_to_low = n_hi.bvshl(&shift_complement);
                let result_lo_small = n_lo.bvlshr(&shift_mod).bvor(&bits_to_low);

                // Large shift (>= 32):
                // result_hi = 0
                // result_lo = n_hi >> (shift - 32)
                let zero = BV::from_i64(0, 32);
                let shift_minus_32 = shift_mod.bvsub(&shift_32);
                let result_hi_large = zero.clone();
                let result_lo_large = n_hi.bvlshr(&shift_minus_32);

                let result_lo = is_large.ite(&result_lo_large, &result_lo_small);
                let result_hi = is_large.ite(&result_hi_large, &result_hi_small);

                state.set_reg(rd_lo, result_lo);
                state.set_reg(rd_hi, result_hi);
            }

            ArmOp::I64ShrS {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi: _,
            } => {
                // 64-bit arithmetic (signed) right shift
                let n_lo = state.get_reg(rn_lo).clone();
                let n_hi = state.get_reg(rn_hi).clone();
                let shift_amt = state.get_reg(rm_lo).clone();

                let shift_mod = shift_amt.bvand(BV::from_i64(63, 32));
                let shift_32 = BV::from_i64(32, 32);
                let is_large = shift_mod.bvuge(&shift_32);

                // Small shift (< 32):
                // result_hi = n_hi >> shift (arithmetic)
                // result_lo = (n_lo >> shift) | (n_hi << (32 - shift))
                let result_hi_small = n_hi.bvashr(&shift_mod);
                let shift_complement = shift_32.bvsub(&shift_mod);
                let bits_to_low = n_hi.bvshl(&shift_complement);
                let result_lo_small = n_lo.bvlshr(&shift_mod).bvor(&bits_to_low);

                // Large shift (>= 32):
                // result_hi = n_hi >> 31 (sign extension: all 0s or all 1s)
                // result_lo = n_hi >> (shift - 32) (arithmetic)
                let shift_31 = BV::from_i64(31, 32);
                let result_hi_large = n_hi.bvashr(&shift_31);
                let shift_minus_32 = shift_mod.bvsub(&shift_32);
                let result_lo_large = n_hi.bvashr(&shift_minus_32);

                let result_lo = is_large.ite(&result_lo_large, &result_lo_small);
                let result_hi = is_large.ite(&result_hi_large, &result_hi_small);

                state.set_reg(rd_lo, result_lo);
                state.set_reg(rd_hi, result_hi);
            }

            // ========================================================================
            // i64 Rotation Operations
            // ========================================================================
            ArmOp::I64Rotl {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                shift,
            } => {
                // 64-bit rotate left: rotl(hi:lo, shift)
                // Result = (value << shift) | (value >> (64 - shift))
                let n_lo = state.get_reg(rnlo).clone();
                let n_hi = state.get_reg(rnhi).clone();
                let shift_amt = state.get_reg(shift).clone();

                // Normalize shift to 0-63 range
                let shift_mod = shift_amt.bvand(BV::from_i64(63, 32));
                let shift_32 = BV::from_i64(32, 32);
                let is_large = shift_mod.bvuge(&shift_32); // shift >= 32

                // For shift < 32:
                // result_lo = (n_lo << shift) | (n_hi >> (32 - shift))
                // result_hi = (n_hi << shift) | (n_lo >> (32 - shift))
                let shift_complement = shift_32.bvsub(&shift_mod);

                let lo_shifted_left = n_lo.bvshl(&shift_mod);
                let hi_bits_to_lo = n_hi.bvlshr(&shift_complement);
                let result_lo_small = lo_shifted_left.bvor(&hi_bits_to_lo);

                let hi_shifted_left = n_hi.bvshl(&shift_mod);
                let lo_bits_to_hi = n_lo.bvlshr(&shift_complement);
                let result_hi_small = hi_shifted_left.bvor(&lo_bits_to_hi);

                // For shift >= 32:
                // Swap and rotate by (shift - 32)
                let shift_minus_32 = shift_mod.bvsub(&shift_32);
                let complement_large = shift_32.bvsub(&shift_minus_32);

                let hi_shifted_left_large = n_hi.bvshl(&shift_minus_32);
                let lo_bits_to_hi_large = n_lo.bvlshr(&complement_large);
                let result_lo_large = hi_shifted_left_large.bvor(&lo_bits_to_hi_large);

                let lo_shifted_left_large = n_lo.bvshl(&shift_minus_32);
                let hi_bits_to_lo_large = n_hi.bvlshr(&complement_large);
                let result_hi_large = lo_shifted_left_large.bvor(&hi_bits_to_lo_large);

                // Select based on shift size
                let result_lo = is_large.ite(&result_lo_large, &result_lo_small);
                let result_hi = is_large.ite(&result_hi_large, &result_hi_small);

                state.set_reg(rdlo, result_lo);
                state.set_reg(rdhi, result_hi);
            }

            ArmOp::I64Rotr {
                rdlo,
                rdhi,
                rnlo,
                rnhi,
                shift,
            } => {
                // 64-bit rotate right: rotr(hi:lo, shift)
                // Result = (value >> shift) | (value << (64 - shift))
                let n_lo = state.get_reg(rnlo).clone();
                let n_hi = state.get_reg(rnhi).clone();
                let shift_amt = state.get_reg(shift).clone();

                // Normalize shift to 0-63 range
                let shift_mod = shift_amt.bvand(BV::from_i64(63, 32));
                let shift_32 = BV::from_i64(32, 32);
                let is_large = shift_mod.bvuge(&shift_32); // shift >= 32

                // For shift < 32:
                // result_lo = (n_lo >> shift) | (n_hi << (32 - shift))
                // result_hi = (n_hi >> shift) | (n_lo << (32 - shift))
                let shift_complement = shift_32.bvsub(&shift_mod);

                let lo_shifted_right = n_lo.bvlshr(&shift_mod);
                let hi_bits_to_lo = n_hi.bvshl(&shift_complement);
                let result_lo_small = lo_shifted_right.bvor(&hi_bits_to_lo);

                let hi_shifted_right = n_hi.bvlshr(&shift_mod);
                let lo_bits_to_hi = n_lo.bvshl(&shift_complement);
                let result_hi_small = hi_shifted_right.bvor(&lo_bits_to_hi);

                // For shift >= 32:
                // Swap and rotate by (shift - 32)
                let shift_minus_32 = shift_mod.bvsub(&shift_32);
                let complement_large = shift_32.bvsub(&shift_minus_32);

                let hi_shifted_right_large = n_hi.bvlshr(&shift_minus_32);
                let lo_bits_to_hi_large = n_lo.bvshl(&complement_large);
                let result_lo_large = hi_shifted_right_large.bvor(&lo_bits_to_hi_large);

                let lo_shifted_right_large = n_lo.bvlshr(&shift_minus_32);
                let hi_bits_to_lo_large = n_hi.bvshl(&complement_large);
                let result_hi_large = lo_shifted_right_large.bvor(&hi_bits_to_lo_large);

                // Select based on shift size
                let result_lo = is_large.ite(&result_lo_large, &result_lo_small);
                let result_hi = is_large.ite(&result_hi_large, &result_hi_small);

                state.set_reg(rdlo, result_lo);
                state.set_reg(rdhi, result_hi);
            }

            ArmOp::I64Clz { rd, rnlo, rnhi } => {
                // Count leading zeros for 64-bit value
                // If high part has zeros, result = clz(high) + clz(low)
                // If high part is zero, result = 32 + clz(low)
                let n_lo = state.get_reg(rnlo).clone();
                let n_hi = state.get_reg(rnhi).clone();

                let hi_clz = self.encode_clz(&n_hi);
                let lo_clz = self.encode_clz(&n_lo);

                // If high == 32 (all zeros), add low clz; else use high clz
                let thirty_two = BV::from_i64(32, 32);
                let hi_is_zero = hi_clz.eq(&thirty_two);
                let result = hi_is_zero.ite(
                    thirty_two.bvadd(&lo_clz), // High is zero: 32 + clz(low)
                    &hi_clz,                   // High has bits: clz(high)
                );
                state.set_reg(rd, result);
            }

            ArmOp::I64Ctz { rd, rnlo, rnhi } => {
                // Count trailing zeros for 64-bit value
                // If low part is zero, result = 32 + ctz(high)
                // Else result = ctz(low)
                let n_lo = state.get_reg(rnlo).clone();
                let n_hi = state.get_reg(rnhi).clone();

                let lo_ctz = self.encode_ctz(&n_lo);
                let hi_ctz = self.encode_ctz(&n_hi);

                // If low == 32 (all zeros), add high ctz; else use low ctz
                let thirty_two = BV::from_i64(32, 32);
                let lo_is_zero = lo_ctz.eq(&thirty_two);
                let result = lo_is_zero.ite(
                    thirty_two.bvadd(&hi_ctz), // Low is zero: 32 + ctz(high)
                    &lo_ctz,                   // Low has bits: ctz(low)
                );
                state.set_reg(rd, result);
            }

            ArmOp::I64Popcnt { rd, rnlo, rnhi } => {
                // Population count for 64-bit value
                // Result = popcnt(low) + popcnt(high)
                let n_lo = state.get_reg(rnlo).clone();
                let n_hi = state.get_reg(rnhi).clone();

                let lo_popcnt = self.encode_popcnt(&n_lo);
                let hi_popcnt = self.encode_popcnt(&n_hi);

                let result = lo_popcnt.bvadd(&hi_popcnt);
                state.set_reg(rd, result);
            }

            // ========================================================================
            // i64 Memory Operations
            // ========================================================================
            ArmOp::I64Ldr { rdlo, rdhi, addr } => {
                // Load 64-bit value from memory
                // Simplified: return symbolic values for both registers
                // Real implementation would load from memory at [addr] and [addr+4]
                let result_lo = BV::new_const(format!("i64load_lo_{:?}", addr), 32);
                let result_hi = BV::new_const(format!("i64load_hi_{:?}", addr), 32);
                state.set_reg(rdlo, result_lo);
                state.set_reg(rdhi, result_hi);
            }

            ArmOp::I64Str {
                rdlo: _,
                rdhi: _,
                addr: _,
            } => {
                // Store 64-bit value to memory
                // Simplified: memory updates not fully modeled yet
                // Real implementation would store rdlo to [addr] and rdhi to [addr+4]
                // No register changes - store operation has no output
            }

            // ========================================================================
            // f32 Operations (Phase 2 - Floating Point)
            // ========================================================================
            // Note: f32 values are represented as 32-bit bitvectors (IEEE 754 format)
            // For verification, we use symbolic bitvector operations
            // A complete implementation would use Z3's FloatingPoint sort

            // f32 Constants
            ArmOp::F32Const { sd, value } => {
                // Load f32 constant (represented as 32-bit bitvector)
                // Convert f32 to its IEEE 754 bit representation
                let bits = value.to_bits() as i64;
                let bv_val = BV::from_i64(bits, 32);
                state.set_vfp_reg(sd, bv_val);
            }

            // f32 Arithmetic (symbolic for verification)
            ArmOp::F32Add { sd, sn, sm } => {
                // f32 addition: sd = sn + sm
                // For verification, return symbolic value
                // Full implementation would use Z3 FloatingPoint operations
                let result = BV::new_const(format!("f32_add_{:?}_{:?}", sn, sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Sub { sd, sn, sm } => {
                // f32 subtraction: sd = sn - sm
                let result = BV::new_const(format!("f32_sub_{:?}_{:?}", sn, sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Mul { sd, sn, sm } => {
                // f32 multiplication: sd = sn * sm
                let result = BV::new_const(format!("f32_mul_{:?}_{:?}", sn, sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Div { sd, sn, sm } => {
                // f32 division: sd = sn / sm
                let result = BV::new_const(format!("f32_div_{:?}_{:?}", sn, sm), 32);
                state.set_vfp_reg(sd, result);
            }

            // f32 Simple Math
            ArmOp::F32Abs { sd, sm } => {
                // f32 absolute value: sd = |sm|
                // Clear the sign bit (bit 31)
                let val = state.get_vfp_reg(sm).clone();
                let mask = BV::from_u64(0x7FFFFFFF, 32); // Clear sign bit
                let result = val.bvand(&mask);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Neg { sd, sm } => {
                // f32 negation: sd = -sm
                // Flip the sign bit (bit 31)
                let val = state.get_vfp_reg(sm).clone();
                let mask = BV::from_u64(0x80000000, 32); // Sign bit
                let result = val.bvxor(&mask);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Sqrt { sd, sm } => {
                // f32 square root: sd = sqrt(sm)
                // Symbolic representation for verification
                let result = BV::new_const(format!("f32_sqrt_{:?}", sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Min { sd, sn, sm } => {
                // f32 minimum: sd = min(sn, sm)
                // IEEE 754 semantics: NaN propagation, -0.0 < +0.0
                // Symbolic representation for verification
                let result = BV::new_const(format!("f32_min_{:?}_{:?}", sn, sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Max { sd, sn, sm } => {
                // f32 maximum: sd = max(sn, sm)
                // IEEE 754 semantics: NaN propagation, +0.0 > -0.0
                // Symbolic representation for verification
                let result = BV::new_const(format!("f32_max_{:?}_{:?}", sn, sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Copysign { sd, sn, sm } => {
                // f32 copysign: sd = |sn| with sign of sm
                // Take magnitude of sn and sign bit from sm
                let val_n = state.get_vfp_reg(sn).clone();
                let val_m = state.get_vfp_reg(sm).clone();

                // Extract magnitude from sn (clear sign bit)
                let mag_mask = BV::from_u64(0x7FFFFFFF, 32);
                let magnitude = val_n.bvand(&mag_mask);

                // Extract sign from sm (bit 31 only)
                let sign_mask = BV::from_u64(0x80000000, 32);
                let sign = val_m.bvand(&sign_mask);

                // Combine: magnitude | sign
                let result = magnitude.bvor(&sign);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Load { sd, addr } => {
                // f32 load: sd = memory[addr]
                // Symbolic memory access for verification
                let result = BV::new_const(format!("f32_load_{:?}", addr), 32);
                state.set_vfp_reg(sd, result);
            }

            // f32 Comparisons (result stored in integer register)
            ArmOp::F32Eq { rd, sn, sm } => {
                // f32 equal: rd = (sn == sm) ? 1 : 0
                // IEEE 754: NaN != NaN, so symbolic comparison needed
                let result = BV::new_const(format!("f32_eq_{:?}_{:?}", sn, sm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F32Ne { rd, sn, sm } => {
                // f32 not equal: rd = (sn != sm) ? 1 : 0
                let result = BV::new_const(format!("f32_ne_{:?}_{:?}", sn, sm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F32Lt { rd, sn, sm } => {
                // f32 less than: rd = (sn < sm) ? 1 : 0
                let result = BV::new_const(format!("f32_lt_{:?}_{:?}", sn, sm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F32Le { rd, sn, sm } => {
                // f32 less than or equal: rd = (sn <= sm) ? 1 : 0
                let result = BV::new_const(format!("f32_le_{:?}_{:?}", sn, sm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F32Gt { rd, sn, sm } => {
                // f32 greater than: rd = (sn > sm) ? 1 : 0
                let result = BV::new_const(format!("f32_gt_{:?}_{:?}", sn, sm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F32Ge { rd, sn, sm } => {
                // f32 greater than or equal: rd = (sn >= sm) ? 1 : 0
                let result = BV::new_const(format!("f32_ge_{:?}_{:?}", sn, sm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F32Store { sd, addr } => {
                // f32 store: memory[addr] = sd
                // Memory write - modeled symbolically for verification
                // In a full implementation, would update memory state
                // For now, this is a no-op as we model memory symbolically
                let _val = state.get_vfp_reg(sd);
                let _addr_str = format!("{:?}", addr);
                // TODO: Add memory state tracking when implementing full memory model
            }

            // f32 Advanced Math Operations
            ArmOp::F32Ceil { sd, sm } => {
                // f32 ceil: sd = ceil(sm) - round toward +infinity
                // Symbolic representation for IEEE 754 rounding
                let result = BV::new_const(format!("f32_ceil_{:?}", sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Floor { sd, sm } => {
                // f32 floor: sd = floor(sm) - round toward -infinity
                // Symbolic representation for IEEE 754 rounding
                let result = BV::new_const(format!("f32_floor_{:?}", sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Trunc { sd, sm } => {
                // f32 trunc: sd = trunc(sm) - round toward zero
                // Symbolic representation for IEEE 754 rounding
                let result = BV::new_const(format!("f32_trunc_{:?}", sm), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32Nearest { sd, sm } => {
                // f32 nearest: sd = nearest(sm) - round to nearest, ties to even
                // Symbolic representation for IEEE 754 rounding
                let result = BV::new_const(format!("f32_nearest_{:?}", sm), 32);
                state.set_vfp_reg(sd, result);
            }

            // f32 Conversions from Integers
            ArmOp::F32ConvertI32S { sd, rm } => {
                // f32 convert from signed i32: sd = (f32)rm
                let int_val = state.get_reg(rm);
                let result = BV::new_const(format!("f32_convert_i32s_{:?}", int_val), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32ConvertI32U { sd, rm } => {
                // f32 convert from unsigned i32: sd = (f32)(unsigned)rm
                let int_val = state.get_reg(rm);
                let result = BV::new_const(format!("f32_convert_i32u_{:?}", int_val), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32ConvertI64S { sd, rmlo, rmhi } => {
                // f32 convert from signed i64: sd = (f32)r64
                let lo = state.get_reg(rmlo);
                let hi = state.get_reg(rmhi);
                let result = BV::new_const(format!("f32_convert_i64s_{:?}_{:?}", lo, hi), 32);
                state.set_vfp_reg(sd, result);
            }

            ArmOp::F32ConvertI64U { sd, rmlo, rmhi } => {
                // f32 convert from unsigned i64: sd = (f32)(unsigned)r64
                let lo = state.get_reg(rmlo);
                let hi = state.get_reg(rmhi);
                let result = BV::new_const(format!("f32_convert_i64u_{:?}_{:?}", lo, hi), 32);
                state.set_vfp_reg(sd, result);
            }

            // f32 Reinterpretations
            ArmOp::F32ReinterpretI32 { sd, rm } => {
                // f32 reinterpret i32: sd = reinterpret_cast<f32>(rm)
                // Bitwise copy without conversion
                let bits = state.get_reg(rm).clone();
                state.set_vfp_reg(sd, bits);
            }

            ArmOp::I32ReinterpretF32 { rd, sm } => {
                // i32 reinterpret f32: rd = reinterpret_cast<i32>(sm)
                // Bitwise copy without conversion
                let bits = state.get_vfp_reg(sm).clone();
                state.set_reg(rd, bits);
            }

            // ===================================================================
            // f64 Operations (Phase 2c - Double-Precision Floating Point)
            // ===================================================================

            // f64 Arithmetic (symbolic for verification)
            ArmOp::F64Add { dd, dn, dm } => {
                // f64 addition: dd = dn + dm
                // For verification, return symbolic value
                // Full implementation would use Z3 FloatingPoint operations
                let result = BV::new_const(format!("f64_add_{:?}_{:?}", dn, dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Sub { dd, dn, dm } => {
                // f64 subtraction: dd = dn - dm
                let result = BV::new_const(format!("f64_sub_{:?}_{:?}", dn, dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Mul { dd, dn, dm } => {
                // f64 multiplication: dd = dn * dm
                let result = BV::new_const(format!("f64_mul_{:?}_{:?}", dn, dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Div { dd, dn, dm } => {
                // f64 division: dd = dn / dm
                let result = BV::new_const(format!("f64_div_{:?}_{:?}", dn, dm), 64);
                state.set_vfp_reg(dd, result);
            }

            // f64 Simple Math
            ArmOp::F64Abs { dd, dm } => {
                // f64 absolute value: dd = |dm|
                // Clear the sign bit (bit 63)
                let val = state.get_vfp_reg(dm).clone();
                let mask = BV::from_u64(0x7FFFFFFFFFFFFFFF, 64); // Clear sign bit
                let result = val.bvand(&mask);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Neg { dd, dm } => {
                // f64 negation: dd = -dm
                // Flip the sign bit (bit 63)
                let val = state.get_vfp_reg(dm).clone();
                let mask = BV::from_u64(0x8000000000000000, 64); // Sign bit
                let result = val.bvxor(&mask);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Sqrt { dd, dm } => {
                // f64 square root: dd = sqrt(dm)
                // Symbolic representation for verification
                let result = BV::new_const(format!("f64_sqrt_{:?}", dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Min { dd, dn, dm } => {
                // f64 minimum: dd = min(dn, dm)
                // IEEE 754 semantics: NaN propagation, -0.0 < +0.0
                // Symbolic representation for verification
                let result = BV::new_const(format!("f64_min_{:?}_{:?}", dn, dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Max { dd, dn, dm } => {
                // f64 maximum: dd = max(dn, dm)
                // IEEE 754 semantics: NaN propagation, +0.0 > -0.0
                // Symbolic representation for verification
                let result = BV::new_const(format!("f64_max_{:?}_{:?}", dn, dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Copysign { dd, dn, dm } => {
                // f64 copysign: dd = |dn| with sign of dm
                // Take magnitude of dn and sign bit from dm
                let val_n = state.get_vfp_reg(dn).clone();
                let val_m = state.get_vfp_reg(dm).clone();

                // Extract magnitude from dn (clear sign bit)
                let mag_mask = BV::from_u64(0x7FFFFFFFFFFFFFFF, 64);
                let magnitude = val_n.bvand(&mag_mask);

                // Extract sign from dm (bit 63 only)
                let sign_mask = BV::from_u64(0x8000000000000000, 64);
                let sign = val_m.bvand(&sign_mask);

                // Combine: magnitude | sign
                let result = magnitude.bvor(&sign);
                state.set_vfp_reg(dd, result);
            }

            // f64 Rounding Operations (symbolic for verification)
            ArmOp::F64Ceil { dd, dm } => {
                // f64 ceil: dd = ceil(dm) - round toward +infinity
                let result = BV::new_const(format!("f64_ceil_{:?}", dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Floor { dd, dm } => {
                // f64 floor: dd = floor(dm) - round toward -infinity
                let result = BV::new_const(format!("f64_floor_{:?}", dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Trunc { dd, dm } => {
                // f64 trunc: dd = trunc(dm) - round toward zero
                let result = BV::new_const(format!("f64_trunc_{:?}", dm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Nearest { dd, dm } => {
                // f64 nearest: dd = round(dm) - round to nearest, ties to even
                let result = BV::new_const(format!("f64_nearest_{:?}", dm), 64);
                state.set_vfp_reg(dd, result);
            }

            // f64 Memory Operations
            ArmOp::F64Load { dd, addr } => {
                // f64 load: dd = memory[addr]
                // Symbolic memory access for verification
                let result = BV::new_const(format!("f64_load_{:?}", addr), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64Store { dd: _, addr: _ } => {
                // f64 store: memory[addr] = dd
                // Store operations don't produce register values
                // No state change for symbolic execution
            }

            ArmOp::F64Const { dd, value } => {
                // f64 constant: dd = value
                let bits = value.to_bits() as i64;
                let result = BV::from_i64(bits, 64);
                state.set_vfp_reg(dd, result);
            }

            // f64 Comparisons (result stored in integer register)
            ArmOp::F64Eq { rd, dn, dm } => {
                // f64 equal: rd = (dn == dm) ? 1 : 0
                // IEEE 754: NaN != NaN, so symbolic comparison needed
                let result = BV::new_const(format!("f64_eq_{:?}_{:?}", dn, dm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F64Ne { rd, dn, dm } => {
                // f64 not equal: rd = (dn != dm) ? 1 : 0
                let result = BV::new_const(format!("f64_ne_{:?}_{:?}", dn, dm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F64Lt { rd, dn, dm } => {
                // f64 less than: rd = (dn < dm) ? 1 : 0
                let result = BV::new_const(format!("f64_lt_{:?}_{:?}", dn, dm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F64Le { rd, dn, dm } => {
                // f64 less than or equal: rd = (dn <= dm) ? 1 : 0
                let result = BV::new_const(format!("f64_le_{:?}_{:?}", dn, dm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F64Gt { rd, dn, dm } => {
                // f64 greater than: rd = (dn > dm) ? 1 : 0
                let result = BV::new_const(format!("f64_gt_{:?}_{:?}", dn, dm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::F64Ge { rd, dn, dm } => {
                // f64 greater than or equal: rd = (dn >= dm) ? 1 : 0
                let result = BV::new_const(format!("f64_ge_{:?}_{:?}", dn, dm), 32);
                state.set_reg(rd, result);
            }

            // f64 Conversions
            ArmOp::F64ConvertI32S { dd, rm } => {
                // f64 convert i32 signed: dd = (f64)rm
                // Symbolic conversion
                let result = BV::new_const(format!("f64_convert_i32s_{:?}", rm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64ConvertI32U { dd, rm } => {
                // f64 convert i32 unsigned: dd = (f64)(unsigned)rm
                // Symbolic conversion
                let result = BV::new_const(format!("f64_convert_i32u_{:?}", rm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64ConvertI64S {
                dd,
                rmlo: _,
                rmhi: _,
            } => {
                // f64 convert i64 signed: dd = (f64)(rmhi:rmlo)
                // Symbolic conversion (complex operation)
                let result = BV::new_const("f64_convert_i64s_result", 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64ConvertI64U {
                dd,
                rmlo: _,
                rmhi: _,
            } => {
                // f64 convert i64 unsigned: dd = (f64)(unsigned)(rmhi:rmlo)
                // Symbolic conversion (complex operation)
                let result = BV::new_const("f64_convert_i64u_result", 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64PromoteF32 { dd, sm } => {
                // f64 promote f32: dd = (f64)sm
                // Promote from 32-bit to 64-bit (symbolic for verification)
                let result = BV::new_const(format!("f64_promote_f32_{:?}", sm), 64);
                state.set_vfp_reg(dd, result);
            }

            ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi } => {
                // f64 reinterpret i64: dd = reinterpret_cast<f64>(rmhi:rmlo)
                // Bitwise copy without conversion - combine two 32-bit registers
                let lo = state.get_reg(rmlo).clone();
                let hi = state.get_reg(rmhi).clone();

                // Extend to 64 bits and combine: (hi << 32) | lo
                let lo_64 = lo.zero_ext(32); // Extend to 64 bits
                let hi_64 = hi.zero_ext(32);
                let shift_32 = BV::from_u64(32, 64);
                let hi_shifted = hi_64.bvshl(&shift_32);
                let result = hi_shifted.bvor(&lo_64);

                state.set_vfp_reg(dd, result);
            }

            ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm } => {
                // i64 reinterpret f64: (rdhi:rdlo) = reinterpret_cast<i64>(dm)
                // Bitwise copy without conversion - split 64-bit into two 32-bit registers
                let bits = state.get_vfp_reg(dm).clone();

                // Extract low 32 bits
                let lo = bits.extract(31, 0);
                state.set_reg(rdlo, lo);

                // Extract high 32 bits
                let hi = bits.extract(63, 32);
                state.set_reg(rdhi, hi);
            }

            ArmOp::I64TruncF64S {
                rdlo: _,
                rdhi: _,
                dm: _,
            } => {
                // i64 trunc f64 signed: (rdhi:rdlo) = (i64)dm
                // Symbolic conversion (complex operation)
                // Would require proper truncation with saturation
            }

            ArmOp::I64TruncF64U {
                rdlo: _,
                rdhi: _,
                dm: _,
            } => {
                // i64 trunc f64 unsigned: (rdhi:rdlo) = (unsigned i64)dm
                // Symbolic conversion (complex operation)
                // Would require proper truncation with saturation
            }

            ArmOp::I32TruncF64S { rd, dm } => {
                // i32 trunc f64 signed: rd = (i32)dm
                // Symbolic conversion
                let result = BV::new_const(format!("i32_trunc_f64s_{:?}", dm), 32);
                state.set_reg(rd, result);
            }

            ArmOp::I32TruncF64U { rd, dm } => {
                // i32 trunc f64 unsigned: rd = (unsigned i32)dm
                // Symbolic conversion
                let result = BV::new_const(format!("i32_trunc_f64u_{:?}", dm), 32);
                state.set_reg(rd, result);
            }

            // VCR-VER-002 (#166): UDF is the WASM trap sink — executing it
            // raises UsageFault. In the straight-line model (no path guards)
            // reaching a UDF means the sequence traps unconditionally; the
            // branch-taking executor [`Self::encode_sequence_br`] instead
            // conditions this on the guard the UDF is reached under.
            ArmOp::Udf { .. } => {
                state.may_trap = Bool::from_bool(true);
            }

            _ => {
                // Unsupported operations - no state change
            }
        }
    }

    /// Evaluate an Operand2 value
    fn evaluate_operand2(&self, op2: &Operand2, state: &ArmState) -> BV {
        match op2 {
            Operand2::Imm(value) => BV::from_i64(*value as i64, 32),
            Operand2::Reg(reg) => state.get_reg(reg).clone(),
            Operand2::RegShift { rm, shift, amount } => {
                let reg_val = state.get_reg(rm).clone();
                let shift_amount = BV::from_i64(*amount as i64, 32);

                match shift {
                    synth_synthesis::ShiftType::LSL => reg_val.bvshl(&shift_amount),
                    synth_synthesis::ShiftType::LSR => reg_val.bvlshr(&shift_amount),
                    synth_synthesis::ShiftType::ASR => reg_val.bvashr(&shift_amount),
                    synth_synthesis::ShiftType::ROR => reg_val.bvrotr(&shift_amount),
                }
            }
        }
    }

    /// Extract the result value from a register after execution
    pub fn extract_result(&self, state: &ArmState, reg: &Reg) -> BV {
        state.get_reg(reg).clone()
    }

    /// Encode ARM CLZ (Count Leading Zeros) instruction
    ///
    /// Implements the same algorithm as WASM i32.clz for equivalence verification.
    /// Uses binary search through bit positions.
    fn encode_clz(&self, input: &BV) -> BV {
        let zero = BV::from_i64(0, 32);

        // Special case: if input is 0, return 32
        let all_zero = input.eq(&zero);
        let result_if_zero = BV::from_i64(32, 32);

        // Binary search approach
        let mut count = BV::from_i64(0, 32);
        let mut remaining = input.clone();

        // Check top 16 bits
        let mask_16 = BV::from_u64(0xFFFF0000, 32);
        let top_16 = remaining.bvand(&mask_16);
        let top_16_zero = top_16.eq(&zero);

        count = top_16_zero.ite(count.bvadd(BV::from_i64(16, 32)), &count);
        remaining = top_16_zero.ite(remaining.bvshl(BV::from_i64(16, 32)), &remaining);

        // Check top 8 bits
        let mask_8 = BV::from_u64(0xFF000000, 32);
        let top_8 = remaining.bvand(&mask_8);
        let top_8_zero = top_8.eq(&zero);

        count = top_8_zero.ite(count.bvadd(BV::from_i64(8, 32)), &count);
        remaining = top_8_zero.ite(remaining.bvshl(BV::from_i64(8, 32)), &remaining);

        // Check top 4 bits
        let mask_4 = BV::from_u64(0xF0000000, 32);
        let top_4 = remaining.bvand(&mask_4);
        let top_4_zero = top_4.eq(&zero);

        count = top_4_zero.ite(count.bvadd(BV::from_i64(4, 32)), &count);
        remaining = top_4_zero.ite(remaining.bvshl(BV::from_i64(4, 32)), &remaining);

        // Check top 2 bits
        let mask_2 = BV::from_u64(0xC0000000, 32);
        let top_2 = remaining.bvand(&mask_2);
        let top_2_zero = top_2.eq(&zero);

        count = top_2_zero.ite(count.bvadd(BV::from_i64(2, 32)), &count);
        remaining = top_2_zero.ite(remaining.bvshl(BV::from_i64(2, 32)), &remaining);

        // Check top bit
        let mask_1 = BV::from_u64(0x80000000, 32);
        let top_1 = remaining.bvand(&mask_1);
        let top_1_zero = top_1.eq(&zero);

        count = top_1_zero.ite(count.bvadd(BV::from_i64(1, 32)), &count);

        // Return 32 if all zeros, otherwise return count
        all_zero.ite(&result_if_zero, &count)
    }

    /// Encode CTZ (Count Trailing Zeros) instruction
    ///
    /// Counts the number of trailing (low-order) zero bits.
    /// Implemented as: ctz(x) = clz(rbit(x))
    /// Returns 32 if input is 0.
    fn encode_ctz(&self, input: &BV) -> BV {
        // CTZ can be implemented by reversing bits and then counting leading zeros
        let reversed = self.encode_rbit(input);
        self.encode_clz(&reversed)
    }

    /// Encode ARM RBIT (Reverse Bits) instruction
    ///
    /// Reverses the bit order in a 32-bit value.
    /// Used in combination with CLZ to implement CTZ.
    fn encode_rbit(&self, input: &BV) -> BV {
        // Reverse bits by swapping progressively smaller chunks
        let mut result = input.clone();

        // Swap 16-bit halves
        let mask_16 = BV::from_u64(0xFFFF0000, 32);
        let top_16 = result.bvand(&mask_16).bvlshr(BV::from_i64(16, 32));
        let bottom_16 = result.bvshl(BV::from_i64(16, 32));
        result = top_16.bvor(&bottom_16);

        // Swap 8-bit chunks
        let mask_8_top = BV::from_u64(0xFF00FF00, 32);
        let mask_8_bottom = BV::from_u64(0x00FF00FF, 32);
        let top_8 = result.bvand(&mask_8_top).bvlshr(BV::from_i64(8, 32));
        let bottom_8 = result.bvand(&mask_8_bottom).bvshl(BV::from_i64(8, 32));
        result = top_8.bvor(&bottom_8);

        // Swap 4-bit chunks
        let mask_4_top = BV::from_u64(0xF0F0F0F0, 32);
        let mask_4_bottom = BV::from_u64(0x0F0F0F0F, 32);
        let top_4 = result.bvand(&mask_4_top).bvlshr(BV::from_i64(4, 32));
        let bottom_4 = result.bvand(&mask_4_bottom).bvshl(BV::from_i64(4, 32));
        result = top_4.bvor(&bottom_4);

        // Swap 2-bit chunks
        let mask_2_top = BV::from_u64(0xCCCCCCCC, 32);
        let mask_2_bottom = BV::from_u64(0x33333333, 32);
        let top_2 = result.bvand(&mask_2_top).bvlshr(BV::from_i64(2, 32));
        let bottom_2 = result.bvand(&mask_2_bottom).bvshl(BV::from_i64(2, 32));
        result = top_2.bvor(&bottom_2);

        // Swap 1-bit chunks (individual bits)
        let mask_1_top = BV::from_u64(0xAAAAAAAA, 32);
        let mask_1_bottom = BV::from_u64(0x55555555, 32);
        let top_1 = result.bvand(&mask_1_top).bvlshr(BV::from_i64(1, 32));
        let bottom_1 = result.bvand(&mask_1_bottom).bvshl(BV::from_i64(1, 32));
        result = top_1.bvor(&bottom_1);

        result
    }

    /// Update condition flags for subtraction (used by CMP, SUB, etc.)
    ///
    /// Computes all four ARM condition flags based on a subtraction:
    /// - N (Negative): Result is negative (bit 31 set)
    /// - Z (Zero): Result is zero
    /// - C (Carry): No borrow occurred (unsigned: a >= b)
    /// - V (Overflow): Signed overflow occurred
    ///
    /// For subtraction result = a - b:
    /// - C = 1 if a >= b (unsigned), 0 if borrow
    /// - V = 1 if signs of a and b differ AND sign of result differs from a
    fn update_flags_sub(&self, state: &mut ArmState, a: &BV, b: &BV, result: &BV) {
        let zero = BV::from_i64(0, 32);

        // N flag: bit 31 of result (negative if set)
        let sign_bit = result.extract(31, 31);
        let one_bit = BV::from_i64(1, 1);
        state.flags.n = sign_bit.eq(&one_bit);

        // Z flag: result == 0
        state.flags.z = result.eq(&zero);

        // C flag: carry/borrow flag for subtraction
        // For SUB: C = 1 if no borrow (i.e., a >= b unsigned)
        // This is equivalent to: a >= b in unsigned arithmetic
        state.flags.c = a.bvuge(b);

        // V flag: signed overflow
        // Overflow occurs when:
        // - Subtracting a positive from a negative gives positive
        // - Subtracting a negative from a positive gives negative
        // Formula: (a[31] != b[31]) && (a[31] != result[31])
        let a_sign = a.extract(31, 31);
        let b_sign = b.extract(31, 31);
        let r_sign = result.extract(31, 31);

        let signs_differ = a_sign.eq(&b_sign).not(); // a and b have different signs
        let result_sign_wrong = a_sign.eq(&r_sign).not(); // result sign differs from a
        state.flags.v = Bool::and(&[&signs_differ, &result_sign_wrong]);
    }

    /// Update condition flags for addition
    ///
    /// Similar to subtraction but with different carry logic:
    /// - C = 1 if unsigned overflow (result < a or result < b)
    /// - V = 1 if signed overflow
    #[allow(dead_code)]
    fn update_flags_add(&self, state: &mut ArmState, a: &BV, b: &BV, result: &BV) {
        let zero = BV::from_i64(0, 32);

        // N flag: bit 31 of result
        let sign_bit = result.extract(31, 31);
        let one_bit = BV::from_i64(1, 1);
        state.flags.n = sign_bit.eq(&one_bit);

        // Z flag: result == 0
        state.flags.z = result.eq(&zero);

        // C flag: unsigned overflow
        // For ADD: C = 1 if carry out (unsigned overflow)
        // This occurs if result < a (wrapping occurred)
        state.flags.c = result.bvult(a);

        // V flag: signed overflow
        // Overflow occurs when:
        // - Adding two positives gives negative
        // - Adding two negatives gives positive
        // Formula: (a[31] == b[31]) && (a[31] != result[31])
        let a_sign = a.extract(31, 31);
        let b_sign = b.extract(31, 31);
        let r_sign = result.extract(31, 31);

        let signs_same = a_sign.eq(&b_sign); // a and b have same sign
        let result_sign_wrong = a_sign.eq(&r_sign).not(); // result sign differs
        state.flags.v = Bool::and(&[&signs_same, &result_sign_wrong]);
    }

    /// Evaluate an ARM condition code based on NZCV flags
    ///
    /// This implements the standard ARM condition code logic:
    /// - EQ: Z == 1
    /// - NE: Z == 0
    /// - LT: N != V (signed less than)
    /// - LE: Z == 1 || N != V (signed less or equal)
    /// - GT: Z == 0 && N == V (signed greater than)
    /// - GE: N == V (signed greater or equal)
    /// - LO: C == 0 (unsigned less than)
    /// - LS: C == 0 || Z == 1 (unsigned less or equal)
    /// - HI: C == 1 && Z == 0 (unsigned greater than)
    /// - HS: C == 1 (unsigned greater or equal)
    fn evaluate_condition(
        &self,
        cond: &synth_synthesis::rules::Condition,
        flags: &ConditionFlags,
    ) -> Bool {
        use synth_synthesis::rules::Condition;

        match cond {
            Condition::EQ => flags.z.clone(),
            Condition::NE => flags.z.not(),
            Condition::LT => {
                // N != V: negative flag differs from overflow flag
                flags.n.eq(&flags.v).not()
            }
            Condition::LE => {
                // Z == 1 || N != V
                let n_ne_v = flags.n.eq(&flags.v).not();
                Bool::or(&[&flags.z, &n_ne_v])
            }
            Condition::GT => {
                // Z == 0 && N == V
                let z_zero = flags.z.not();
                let n_eq_v = flags.n.eq(&flags.v);
                Bool::and(&[&z_zero, &n_eq_v])
            }
            Condition::GE => {
                // N == V
                flags.n.eq(&flags.v)
            }
            Condition::LO => {
                // C == 0 (no carry = less than unsigned)
                flags.c.not()
            }
            Condition::LS => {
                // C == 0 || Z == 1
                let c_zero = flags.c.not();
                Bool::or(&[&flags.z, &c_zero])
            }
            Condition::HI => {
                // C == 1 && Z == 0
                let z_zero = flags.z.not();
                Bool::and(&[&flags.c, &z_zero])
            }
            Condition::HS => {
                // C == 1 (carry = greater or equal unsigned)
                flags.c.clone()
            }
        }
    }

    /// Convert a boolean to a 32-bit bitvector (0 or 1)
    fn bool_to_bv32(&self, cond: &Bool) -> BV {
        let zero = BV::from_i64(0, 32);
        let one = BV::from_i64(1, 32);
        cond.ite(&one, &zero)
    }

    /// Encode ARM POPCNT (population count)
    ///
    /// Uses the Hamming weight algorithm (same as WASM implementation).
    /// This is a pseudo-instruction that would be expanded into actual ARM code.
    fn encode_popcnt(&self, input: &BV) -> BV {
        let mut x = input.clone();

        // Step 1: Count bits in pairs
        let mask1 = BV::from_u64(0x55555555, 32);
        let masked = x.bvand(&mask1);
        let shifted = x.bvlshr(BV::from_i64(1, 32));
        let shifted_masked = shifted.bvand(&mask1);
        x = masked.bvadd(&shifted_masked);

        // Step 2: Count pairs in nibbles
        let mask2 = BV::from_u64(0x33333333, 32);
        let masked = x.bvand(&mask2);
        let shifted = x.bvlshr(BV::from_i64(2, 32));
        let shifted_masked = shifted.bvand(&mask2);
        x = masked.bvadd(&shifted_masked);

        // Step 3: Count nibbles in bytes
        let mask3 = BV::from_u64(0x0F0F0F0F, 32);
        let masked = x.bvand(&mask3);
        let shifted = x.bvlshr(BV::from_i64(4, 32));
        let shifted_masked = shifted.bvand(&mask3);
        x = masked.bvadd(&shifted_masked);

        // Step 4: Sum all bytes
        let multiplier = BV::from_u64(0x01010101, 32);
        x = x.bvmul(&multiplier);
        x = x.bvlshr(BV::from_i64(24, 32));

        x
    }
}

// ===========================================================================
// VCR-VER-002 (#166): branch-taking guarded executor — DERIVES the ARM trap
// condition from the emitted guard/branch/UDF structure
// ===========================================================================

/// Path guard: the condition under which an instruction executes. `Always`
/// keeps the straight-line common case free of `ite` merging.
#[derive(Clone)]
enum Guard {
    Always,
    Cond(Bool),
}

impl Guard {
    fn and_cond(&self, c: &Bool) -> Guard {
        match self {
            Guard::Always => Guard::Cond(c.clone()),
            Guard::Cond(g) => Guard::Cond(Bool::and(&[g, c])),
        }
    }
}

/// Merge an incoming edge guard into the guard map at `at`.
fn merge_guard(incoming: &mut HashMap<usize, Guard>, at: usize, g: Guard) {
    match (incoming.get(&at), g) {
        (Some(Guard::Always), _) => {}
        (_, Guard::Always) => {
            incoming.insert(at, Guard::Always);
        }
        (Some(Guard::Cond(a)), Guard::Cond(b)) => {
            let merged = Bool::or(&[a, &b]);
            incoming.insert(at, Guard::Cond(merged));
        }
        (None, g @ Guard::Cond(_)) => {
            incoming.insert(at, g);
        }
    }
}

/// Boolean if-then-else (the term API only has BV ite).
fn bool_ite(c: &Bool, t: &Bool, e: &Bool) -> Bool {
    Bool::or(&[&Bool::and(&[c, t]), &Bool::and(&[&c.not(), e])])
}

/// IEEE 754 single-precision NaN test over the raw bit pattern:
/// exponent all-ones with a non-zero fraction.
fn f32_is_nan(x: &BV) -> Bool {
    let exp_ones = x.extract(30, 23).eq(BV::from_u64(0xFF, 8));
    let frac_nonzero = x.extract(22, 0).eq(BV::from_u64(0, 23)).not();
    Bool::and(&[&exp_ones, &frac_nonzero])
}

/// Ordered `a < b` over IEEE 754 single-precision BIT PATTERNS, assuming
/// neither operand is NaN (the callers conjoin the NaN exclusion). Uses the
/// sign/magnitude case split; `+0.0 == -0.0` (neither is less).
fn f32_ordered_lt(a: &BV, b: &BV) -> Bool {
    let a_neg = a.extract(31, 31).eq(BV::from_u64(1, 1));
    let b_neg = b.extract(31, 31).eq(BV::from_u64(1, 1));
    let a_mag = a.extract(30, 0);
    let b_mag = b.extract(30, 0);
    let zero31 = BV::from_u64(0, 31);
    let both_zero = Bool::and(&[&a_mag.eq(&zero31), &b_mag.eq(&zero31)]);
    // (neg, neg): larger magnitude is smaller; (neg, pos): a < b unless both
    // are zeros; (pos, neg): never; (pos, pos): magnitude order.
    let neg_neg = b_mag.bvult(&a_mag);
    let neg_pos = both_zero.not();
    let pos_pos = a_mag.bvult(&b_mag);
    bool_ite(
        &a_neg,
        &bool_ite(&b_neg, &neg_neg, &neg_pos),
        &bool_ite(&b_neg, &Bool::from_bool(false), &pos_pos),
    )
}

/// The three ordered VFP comparison results the trunc guards use, as total
/// functions over the operands' bit patterns (result is 0 on any NaN — the
/// unordered case — exactly the ARM `VCMP`+`VMRS`+`IT` materialization the
/// `F32Lt`/`F32Gt`/`F32Ge` pseudo-ops stand for).
fn f32_cmp_result(kind: F32CmpKind, a: &BV, b: &BV) -> Bool {
    let ordered = Bool::and(&[&f32_is_nan(a).not(), &f32_is_nan(b).not()]);
    let rel = match kind {
        F32CmpKind::Lt => f32_ordered_lt(a, b),
        F32CmpKind::Gt => f32_ordered_lt(b, a),
        F32CmpKind::Ge => f32_ordered_lt(a, b).not(),
    };
    Bool::and(&[&ordered, &rel])
}

#[derive(Clone, Copy)]
enum F32CmpKind {
    Lt,
    Gt,
    Ge,
}

/// IEEE 754 double-precision NaN test over the raw bit pattern:
/// exponent all-ones (bits 62..52) with a non-zero fraction (bits 51..0).
/// The 64-bit twin of [`f32_is_nan`], for the #709/#756 f64→i32 trunc guards.
fn f64_is_nan(x: &BV) -> Bool {
    let exp_ones = x.extract(62, 52).eq(BV::from_u64(0x7FF, 11));
    let frac_nonzero = x.extract(51, 0).eq(BV::from_u64(0, 52)).not();
    Bool::and(&[&exp_ones, &frac_nonzero])
}

/// Ordered `a < b` over IEEE 754 double-precision BIT PATTERNS, assuming
/// neither operand is NaN (the callers conjoin the NaN exclusion). The 64-bit
/// twin of [`f32_ordered_lt`]: sign bit 63, magnitude bits 62..0; `+0.0 == -0.0`
/// (neither is less).
fn f64_ordered_lt(a: &BV, b: &BV) -> Bool {
    let a_neg = a.extract(63, 63).eq(BV::from_u64(1, 1));
    let b_neg = b.extract(63, 63).eq(BV::from_u64(1, 1));
    let a_mag = a.extract(62, 0);
    let b_mag = b.extract(62, 0);
    let zero63 = BV::from_u64(0, 63);
    let both_zero = Bool::and(&[&a_mag.eq(&zero63), &b_mag.eq(&zero63)]);
    // (neg, neg): larger magnitude is smaller; (neg, pos): a < b unless both
    // are zeros; (pos, neg): never; (pos, pos): magnitude order.
    let neg_neg = b_mag.bvult(&a_mag);
    let neg_pos = both_zero.not();
    let pos_pos = a_mag.bvult(&b_mag);
    bool_ite(
        &a_neg,
        &bool_ite(&b_neg, &neg_neg, &neg_pos),
        &bool_ite(&b_neg, &Bool::from_bool(false), &pos_pos),
    )
}

/// The three ordered VFP.F64 comparison results the f64 trunc guards use, as
/// total functions over the operands' bit patterns (result is 0 on any NaN —
/// the unordered case — exactly the ARM `VCMP.F64`+`VMRS`+`IT` materialization
/// the `F64Lt`/`F64Gt`/`F64Ge` pseudo-ops stand for). The 64-bit twin of
/// [`f32_cmp_result`].
fn f64_cmp_result(kind: F32CmpKind, a: &BV, b: &BV) -> Bool {
    let ordered = Bool::and(&[&f64_is_nan(a).not(), &f64_is_nan(b).not()]);
    let rel = match kind {
        F32CmpKind::Lt => f64_ordered_lt(a, b),
        F32CmpKind::Gt => f64_ordered_lt(b, a),
        F32CmpKind::Ge => f64_ordered_lt(a, b).not(),
    };
    Bool::and(&[&ordered, &rel])
}

impl ArmSemantics {
    /// Branch-taking guarded symbolic execution of an ARM sequence,
    /// deriving `state.may_trap` from the emitted guard structure
    /// (VCR-VER-002, #166).
    ///
    /// Forward-branch DAG execution over the op list: every instruction
    /// carries the disjunction of the path conditions that reach it
    /// (if-conversion), `BCondOffset` routes guards forward, and a `Udf`
    /// accumulates its path guard into [`ArmState::may_trap`] — and does NOT
    /// fall through (a trap halts execution, so the code after a guarded
    /// `UDF` is reached only via the guard's skip branch). This makes the ARM
    /// trap condition a DERIVED term: a lowering whose guard was dropped,
    /// inverted, or aimed at the wrong register derives a trap condition that
    /// fails the preservation VC — unlike the previous structural
    /// `Udf`-presence proxy, which only saw that *some* trap existed.
    ///
    /// Branch targets are resolved in bytes via the shipped byte-size
    /// estimator (`synth_synthesis::optimizer_bridge::estimate_arm_byte_size`,
    /// the #511 estimator that CI pins against the encoder), matching the
    /// encoder's `target = branch + 4 + 2*offset` halfword rule. A target
    /// that lands mid-instruction, a backward branch (loop), an op outside
    /// the modeled subset, or any label/call control flow is a loud `Err` —
    /// never a silent accept.
    pub fn encode_sequence_br(
        &self,
        arm_ops: &[ArmOp],
        state: &mut ArmState,
    ) -> Result<(), String> {
        use synth_synthesis::optimizer_bridge::estimate_arm_byte_size;

        // Byte offset of each op (the estimator is the pinned encoder mirror).
        let mut offsets = Vec::with_capacity(arm_ops.len());
        let mut off = 0usize;
        for op in arm_ops {
            offsets.push(off);
            off += estimate_arm_byte_size(op);
        }
        let total_len = off;
        let boundaries: std::collections::HashSet<usize> = offsets.iter().copied().collect();

        let mut incoming: HashMap<usize, Guard> = HashMap::new();
        incoming.insert(0, Guard::Always);

        for (i, op) in arm_ops.iter().enumerate() {
            let o = offsets[i];
            // Unreached instruction (e.g. dead code behind an unconditional
            // trap): no incoming edge, skip — it can never execute.
            let Some(g) = incoming.get(&o).cloned() else {
                continue;
            };
            let next = o + estimate_arm_byte_size(op);

            match op {
                ArmOp::BCondOffset { cond, offset } => {
                    if *offset < 0 {
                        return Err(
                            "backward branch (loop) outside the trap-derivation subset — held out"
                                .to_string(),
                        );
                    }
                    // Encoder rule: offset is the halfword displacement,
                    // target = branch_addr + 4 + 2*offset.
                    let target = o + 4 + 2 * (*offset as usize);
                    if target != total_len && !boundaries.contains(&target) {
                        return Err(format!(
                            "BCondOffset target {target} lands mid-instruction \
                             (sequence len {total_len}) — estimator/encoder drift or \
                             malformed guard"
                        ));
                    }
                    let c = self.evaluate_condition(cond, &state.flags);
                    merge_guard(&mut incoming, target, g.and_cond(&c));
                    merge_guard(&mut incoming, next, g.and_cond(&c.not()));
                }

                ArmOp::Udf { .. } => {
                    // The trap fires exactly under this path guard; execution
                    // never continues past it (no fall-through edge).
                    state.may_trap = match &g {
                        Guard::Always => Bool::from_bool(true),
                        Guard::Cond(gb) => Bool::or(&[&state.may_trap, gb]),
                    };
                }

                // Label/relative/indirect control flow has no derivable local
                // trap semantics here — loud decline, never a silent accept.
                ArmOp::B { .. }
                | ArmOp::BOffset { .. }
                | ArmOp::Bcc { .. }
                | ArmOp::Bhs { .. }
                | ArmOp::Blo { .. }
                | ArmOp::Bl { .. }
                | ArmOp::Blx { .. }
                | ArmOp::Bx { .. }
                | ArmOp::Label { .. }
                | ArmOp::Call { .. }
                | ArmOp::CallIndirect { .. }
                | ArmOp::BrTable { .. }
                | ArmOp::Push { .. }
                | ArmOp::Pop { .. } => {
                    return Err(format!(
                        "op {op:?} outside the trap-derivation subset — loud decline"
                    ));
                }

                _ => {
                    match &g {
                        Guard::Always => self.exec_trap_subset_op(op, state)?,
                        Guard::Cond(gb) => {
                            // Guarded (if-converted) execution: snapshot the
                            // register/flag/VFP state, execute, ite-merge
                            // under the guard. Sound because these ops touch
                            // only registers/flags/VFP (the subset check in
                            // exec_trap_subset_op rejects everything else).
                            //
                            // Only components the op actually CHANGED are
                            // merged — `ite(g, x, x) ≡ x`, and wrapping every
                            // untouched register on every guarded step nests
                            // the SDIV/UDIV operands in ite chains, blowing
                            // the div/rem trap VC off a CDCL cliff (observed:
                            // the div_s double-guard query ran 45+ min / 5 GB
                            // with the unconditional merge, sub-second
                            // without).
                            let regs_before = state.registers.clone();
                            let vfp_before = state.vfp_registers.clone();
                            let flags_before = ConditionFlags {
                                n: state.flags.n.clone(),
                                z: state.flags.z.clone(),
                                c: state.flags.c.clone(),
                                v: state.flags.v.clone(),
                            };
                            self.exec_trap_subset_op(op, state)?;
                            for (r, before) in regs_before.iter().enumerate() {
                                if !state.registers[r].same_term(before) {
                                    state.registers[r] = gb.ite(&state.registers[r], before);
                                }
                            }
                            for (r, before) in vfp_before.iter().enumerate() {
                                if !state.vfp_registers[r].same_term(before) {
                                    state.vfp_registers[r] =
                                        gb.ite(&state.vfp_registers[r], before);
                                }
                            }
                            if !state.flags.n.same_term(&flags_before.n) {
                                state.flags.n = bool_ite(gb, &state.flags.n, &flags_before.n);
                            }
                            if !state.flags.z.same_term(&flags_before.z) {
                                state.flags.z = bool_ite(gb, &state.flags.z, &flags_before.z);
                            }
                            if !state.flags.c.same_term(&flags_before.c) {
                                state.flags.c = bool_ite(gb, &state.flags.c, &flags_before.c);
                            }
                            if !state.flags.v.same_term(&flags_before.v) {
                                state.flags.v = bool_ite(gb, &state.flags.v, &flags_before.v);
                            }
                        }
                    }
                    merge_guard(&mut incoming, next, g);
                }
            }
        }

        Ok(())
    }

    /// Whether the sequence's branch structure is VALUE-DEAD: every op inside
    /// a branch-skipped span writes no register/VFP state (`Udf`, `Cmp`,
    /// `Cmn`, nested `BCondOffset` only), and no op anywhere in the sequence
    /// turns flags into a register value (`SetCond`).
    ///
    /// Under this condition the final REGISTER state is path-independent —
    /// every register-writing op executes on every path, in program order —
    /// so the straight-line value pass
    /// [`Self::encode_sequence_value_straightline`] computes exactly the
    /// registers any non-trapping real path produces. The flag writes a taken
    /// branch skips (e.g. the div_s overflow guard's `CMN` behind `BNE +3`)
    /// can only influence which PATH is taken — the trap side, which
    /// [`Self::encode_sequence_br`] derives with full path sensitivity — and
    /// never a register value, because `SetCond` (the only flag→register op
    /// in the modeled subset) is excluded outright.
    ///
    /// This is what lets the div/rem trap VC keep its value clause
    /// STRUCTURALLY aligned with the WASM side (`bvsdiv`/`MLS` terms
    /// identical after canonicalization): an `ite(guard, …)` wrapper on an
    /// SDIV/MLS operand un-shares the 32×32 multiplier/divider circuits and
    /// sends the UNSAT proof off the CDCL cliff term.rs documents (observed:
    /// rem_s value clause 15+ min with the ite, sub-second without).
    pub fn branch_spans_are_value_dead(arm_ops: &[ArmOp]) -> bool {
        use synth_synthesis::optimizer_bridge::estimate_arm_byte_size;

        let mut offsets = Vec::with_capacity(arm_ops.len());
        let mut off = 0usize;
        for op in arm_ops {
            offsets.push(off);
            off += estimate_arm_byte_size(op);
        }

        // No flag→register materialization anywhere in the sequence.
        if arm_ops.iter().any(|op| matches!(op, ArmOp::SetCond { .. })) {
            return false;
        }

        for (i, op) in arm_ops.iter().enumerate() {
            if let ArmOp::BCondOffset { offset, .. } = op {
                if *offset < 0 {
                    return false; // backward branch — not this subset at all
                }
                // Fall-through = next instruction; encoder rule for the
                // target: branch_addr + 4 + 2*offset (same as
                // `encode_sequence_br`). The skipped span is [fall-through,
                // target).
                let span_start = offsets[i] + estimate_arm_byte_size(op);
                let span_end = offsets[i] + 4 + 2 * (*offset as usize);
                for (j, skipped) in arm_ops.iter().enumerate() {
                    if offsets[j] >= span_start && offsets[j] < span_end {
                        match skipped {
                            ArmOp::Udf { .. }
                            | ArmOp::Cmp { .. }
                            | ArmOp::Cmn { .. }
                            | ArmOp::BCondOffset { .. } => {}
                            _ => return false, // a register/VFP write is skippable
                        }
                    }
                }
            }
        }
        true
    }

    /// Straight-line VALUE execution of a trap-guarded sequence: branches and
    /// `UDF`s are register no-ops, every other op executes unconditionally
    /// via the same modeled subset as the branch-taking executor.
    ///
    /// ONLY sound when [`Self::branch_spans_are_value_dead`] holds (see its
    /// doc for the argument); callers must check it first. Produces ite-free
    /// register terms, keeping the trap VC's value clause structurally
    /// aligned with the WASM encoding.
    pub fn encode_sequence_value_straightline(
        &self,
        arm_ops: &[ArmOp],
        state: &mut ArmState,
    ) -> Result<(), String> {
        for op in arm_ops {
            match op {
                ArmOp::BCondOffset { .. } | ArmOp::Udf { .. } => {}
                _ => self.exec_trap_subset_op(op, state)?,
            }
        }
        Ok(())
    }

    /// Execute one non-branch op of the trap-derivation subset. Ops the
    /// shipped trap-guarded lowerings use but `encode_op` leaves unmodeled
    /// (`Cmn`, `Movw`, `Movt`, the ordered VFP compares) get explicit
    /// semantics here; a WHITELIST of register-only value ops delegates to
    /// `encode_op`; anything else is a loud `Err` — `encode_op`'s silent
    /// `_ => {}` default must never green-wash a trap derivation.
    fn exec_trap_subset_op(&self, op: &ArmOp, state: &mut ArmState) -> Result<(), String> {
        match op {
            // CMN: compare negated — flags from rn + op2.
            ArmOp::Cmn { rn, op2 } => {
                let a = state.get_reg(rn).clone();
                let b = self.evaluate_operand2(op2, state);
                let result = a.bvadd(&b);
                self.update_flags_add(state, &a, &b, &result);
                Ok(())
            }
            ArmOp::Movw { rd, imm16 } => {
                state.set_reg(rd, BV::from_u64(*imm16 as u64, 32));
                Ok(())
            }
            ArmOp::Movt { rd, imm16 } => {
                let low = state.get_reg(rd).bvand(BV::from_u64(0xFFFF, 32));
                let v = low.bvor(BV::from_u64((*imm16 as u64) << 16, 32));
                state.set_reg(rd, v);
                Ok(())
            }
            // Ordered VFP compares (the #709 trunc guards): real bit-pattern
            // semantics — result register is 1 iff the ordered relation
            // holds, 0 on NaN. encode_op models these as uninterpreted
            // symbols, which cannot drive a trap derivation.
            ArmOp::F32Lt { rd, sn, sm } => {
                let a = state.get_vfp_reg(sn).clone();
                let b = state.get_vfp_reg(sm).clone();
                let r = self.bool_to_bv32(&f32_cmp_result(F32CmpKind::Lt, &a, &b));
                state.set_reg(rd, r);
                Ok(())
            }
            ArmOp::F32Gt { rd, sn, sm } => {
                let a = state.get_vfp_reg(sn).clone();
                let b = state.get_vfp_reg(sm).clone();
                let r = self.bool_to_bv32(&f32_cmp_result(F32CmpKind::Gt, &a, &b));
                state.set_reg(rd, r);
                Ok(())
            }
            ArmOp::F32Ge { rd, sn, sm } => {
                let a = state.get_vfp_reg(sn).clone();
                let b = state.get_vfp_reg(sm).clone();
                let r = self.bool_to_bv32(&f32_cmp_result(F32CmpKind::Ge, &a, &b));
                state.set_reg(rd, r);
                Ok(())
            }
            // Ordered VFP.F64 compares (the #756 f64→i32 trunc guards): real
            // bit-pattern semantics over the 64-bit D-register operands — 1 iff
            // the ordered relation holds, 0 on NaN. encode_op models these as
            // uninterpreted symbols, which cannot drive a trap derivation.
            ArmOp::F64Lt { rd, dn, dm } => {
                let a = state.get_vfp_reg(dn).clone();
                let b = state.get_vfp_reg(dm).clone();
                let r = self.bool_to_bv32(&f64_cmp_result(F32CmpKind::Lt, &a, &b));
                state.set_reg(rd, r);
                Ok(())
            }
            ArmOp::F64Gt { rd, dn, dm } => {
                let a = state.get_vfp_reg(dn).clone();
                let b = state.get_vfp_reg(dm).clone();
                let r = self.bool_to_bv32(&f64_cmp_result(F32CmpKind::Gt, &a, &b));
                state.set_reg(rd, r);
                Ok(())
            }
            ArmOp::F64Ge { rd, dn, dm } => {
                let a = state.get_vfp_reg(dn).clone();
                let b = state.get_vfp_reg(dm).clone();
                let r = self.bool_to_bv32(&f64_cmp_result(F32CmpKind::Ge, &a, &b));
                state.set_reg(rd, r);
                Ok(())
            }
            // Register/flag-only value ops the covered lowerings use:
            // delegate to the existing encode_op semantics.
            ArmOp::Cmp { .. }
            | ArmOp::Add { .. }
            | ArmOp::Sub { .. }
            | ArmOp::Rsb { .. }
            | ArmOp::Mov { .. }
            | ArmOp::And { .. }
            | ArmOp::Orr { .. }
            | ArmOp::Eor { .. }
            | ArmOp::Mul { .. }
            | ArmOp::Mls { .. }
            | ArmOp::Sdiv { .. }
            | ArmOp::Udiv { .. }
            | ArmOp::SetCond { .. }
            | ArmOp::Nop
            | ArmOp::F32Const { .. }
            | ArmOp::I32TruncF32S { .. }
            | ArmOp::I32TruncF32U { .. }
            // f64 trunc guards (#756): F64Const sets the D-reg to the real
            // 64-bit float bit pattern (load-bearing for the derived compare);
            // the saturating VCVT pseudo-ops write only the RESULT register,
            // which the trap derivation ignores.
            | ArmOp::F64Const { .. }
            | ArmOp::I32TruncF64S { .. }
            | ArmOp::I32TruncF64U { .. }
            | ArmOp::I64TruncF64S { .. }
            | ArmOp::I64TruncF64U { .. }
            // Ldr/Str: the value model treats loads as fresh symbols and
            // stores as no-ops (no memory-contents model) — fine for a trap
            // derivation, where only the guard's flags/registers matter.
            | ArmOp::Ldr { .. }
            | ArmOp::Str { .. } => {
                self.encode_op(op, state);
                Ok(())
            }
            // Subword accesses (#752 gate coverage for the guarded
            // i32.load8/16 + i32.store8/16 shapes): same treatment as
            // Ldr/Str — a load writes a fresh symbol (no memory-contents
            // model), a store touches no register. Neither affects flags,
            // so the trap derivation is untouched; modeling them here just
            // lets guarded subword sequences through instead of a loud
            // decline.
            ArmOp::Ldrb { rd, .. }
            | ArmOp::Ldrsb { rd, .. }
            | ArmOp::Ldrh { rd, .. }
            | ArmOp::Ldrsh { rd, .. } => {
                let result = BV::new_const(format!("load_{rd:?}"), 32);
                state.set_reg(rd, result);
                Ok(())
            }
            ArmOp::Strb { .. } | ArmOp::Strh { .. } => Ok(()),
            other => Err(format!(
                "op {other:?} outside the trap-derivation subset — loud decline"
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::with_verification_context;

    #[test]
    fn test_arm_add_semantics() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Set up concrete values for testing
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));
            state.set_reg(&Reg::R2, BV::from_i64(20, 32));

            // Execute: ADD R0, R1, R2
            let op = ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            };

            encoder.encode_op(&op, &mut state);

            // Check result: R0 should be 30
            let result = state.get_reg(&Reg::R0).simplify();
            assert_eq!(result.as_i64(), Some(30));
        });
    }

    #[test]
    fn test_arm_sub_semantics() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            state.set_reg(&Reg::R1, BV::from_i64(50, 32));
            state.set_reg(&Reg::R2, BV::from_i64(20, 32));

            let op = ArmOp::Sub {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            };

            encoder.encode_op(&op, &mut state);

            let result = state.get_reg(&Reg::R0);
            assert_eq!(result.simplify().as_i64(), Some(30));
        });
    }

    #[test]
    fn test_arm_mov_immediate() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            let op = ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(42),
            };

            encoder.encode_op(&op, &mut state);

            let result = state.get_reg(&Reg::R0);
            assert_eq!(result.simplify().as_i64(), Some(42));
        });
    }

    #[test]
    fn test_arm_bitwise_ops() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            state.set_reg(&Reg::R1, BV::from_i64(0b1010, 32));
            state.set_reg(&Reg::R2, BV::from_i64(0b1100, 32));

            // Test AND
            let and_op = ArmOp::And {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            };
            encoder.encode_op(&and_op, &mut state);
            assert_eq!(state.get_reg(&Reg::R0).simplify().as_i64(), Some(0b1000));

            // Test ORR
            let orr_op = ArmOp::Orr {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            };
            encoder.encode_op(&orr_op, &mut state);
            assert_eq!(state.get_reg(&Reg::R0).simplify().as_i64(), Some(0b1110));

            // Test EOR (XOR)
            let eor_op = ArmOp::Eor {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            };
            encoder.encode_op(&eor_op, &mut state);
            assert_eq!(state.get_reg(&Reg::R0).simplify().as_i64(), Some(0b0110));
        });
    }

    #[test]
    fn test_arm_mls() {
        // Test MLS (Multiply and Subtract): Rd = Ra - Rn * Rm
        // This is used for remainder: a % b = a - (a/b) * b
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test: 17 % 5 = 17 - (17/5) * 5 = 17 - 3*5 = 17 - 15 = 2
            // Ra = 17, Rn = 3 (quotient), Rm = 5 (divisor)
            state.set_reg(&Reg::R0, BV::from_i64(17, 32)); // Ra (dividend)
            state.set_reg(&Reg::R1, BV::from_i64(3, 32)); // Rn (quotient)
            state.set_reg(&Reg::R2, BV::from_i64(5, 32)); // Rm (divisor)

            let mls_op = ArmOp::Mls {
                rd: Reg::R3,
                rn: Reg::R1,
                rm: Reg::R2,
                ra: Reg::R0,
            };
            encoder.encode_op(&mls_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R3).simplify().as_i64(),
                Some(2),
                "MLS: 17 - 3*5 = 2"
            );

            // Test: 100 - 7 * 3 = 100 - 21 = 79
            state.set_reg(&Reg::R0, BV::from_i64(100, 32));
            state.set_reg(&Reg::R1, BV::from_i64(7, 32));
            state.set_reg(&Reg::R2, BV::from_i64(3, 32));

            let mls_op2 = ArmOp::Mls {
                rd: Reg::R3,
                rn: Reg::R1,
                rm: Reg::R2,
                ra: Reg::R0,
            };
            encoder.encode_op(&mls_op2, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R3).simplify().as_i64(),
                Some(79),
                "MLS: 100 - 7*3 = 79"
            );

            // Test with negative numbers: (-17) - 3 * 5 = -17 - 15 = -32
            state.set_reg(&Reg::R0, BV::from_i64(-17, 32));
            state.set_reg(&Reg::R1, BV::from_i64(3, 32));
            state.set_reg(&Reg::R2, BV::from_i64(5, 32));

            let mls_op3 = ArmOp::Mls {
                rd: Reg::R3,
                rn: Reg::R1,
                rm: Reg::R2,
                ra: Reg::R0,
            };
            encoder.encode_op(&mls_op3, &mut state);
            // Result is -32, but as_i64() returns unsigned, so we need to convert
            let result = state.get_reg(&Reg::R3).simplify().as_i64();
            let signed_result = result.map(|v| (v as i32) as i64);
            assert_eq!(signed_result, Some(-32), "MLS: -17 - 3*5 = -32");
        });
    }

    #[test]
    fn test_arm_shift_ops() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            state.set_reg(&Reg::R1, BV::from_i64(8, 32));

            // Test LSL (logical shift left) with immediate
            let lsl_op = ArmOp::Lsl {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 2,
            };
            encoder.encode_op(&lsl_op, &mut state);
            assert_eq!(state.get_reg(&Reg::R0).simplify().as_i64(), Some(32));

            // Test LSR (logical shift right) with immediate
            let lsr_op = ArmOp::Lsr {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 2,
            };
            encoder.encode_op(&lsr_op, &mut state);
            assert_eq!(state.get_reg(&Reg::R0).simplify().as_i64(), Some(2));
        });
    }

    #[test]
    fn test_arm_ror_comprehensive() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test ROR with 0x12345678
            // ROR by 8 should rotate right by 8 bits
            state.set_reg(&Reg::R1, BV::from_u64(0x12345678, 32));
            let ror_op = ArmOp::Ror {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 8,
            };
            encoder.encode_op(&ror_op, &mut state);
            // 0x12345678 ROR 8 = 0x78123456
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0x78123456),
                "ROR by 8"
            );

            // Test ROR by 16 (swap halves)
            let ror_op_16 = ArmOp::Ror {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 16,
            };
            encoder.encode_op(&ror_op_16, &mut state);
            // 0x12345678 ROR 16 = 0x56781234
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0x56781234),
                "ROR by 16"
            );

            // Test ROR by 0 (no change)
            let ror_op_0 = ArmOp::Ror {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 0,
            };
            encoder.encode_op(&ror_op_0, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0x12345678),
                "ROR by 0"
            );

            // Test ROR by 32 (full rotation, back to original)
            let ror_op_32 = ArmOp::Ror {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 32,
            };
            encoder.encode_op(&ror_op_32, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0x12345678),
                "ROR by 32"
            );

            // Test ROR by 4 (nibble rotation)
            state.set_reg(&Reg::R1, BV::from_u64(0xABCDEF01, 32));
            let ror_op_4 = ArmOp::Ror {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 4,
            };
            encoder.encode_op(&ror_op_4, &mut state);
            // 0xABCDEF01 ROR 4 = 0x1ABCDEF0
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0x1ABCDEF0),
                "ROR by 4"
            );

            // Test ROR with 1-bit rotation
            state.set_reg(&Reg::R1, BV::from_u64(0x80000001, 32));
            let ror_op_1 = ArmOp::Ror {
                rd: Reg::R0,
                rn: Reg::R1,
                shift: 1,
            };
            encoder.encode_op(&ror_op_1, &mut state);
            // 0x80000001 ROR 1 = 0xC0000000
            let result = state.get_reg(&Reg::R0).simplify().as_i64();
            let signed_result = result.map(|v| (v as i32) as i64);
            assert_eq!(
                signed_result,
                Some(0xC0000000_u32 as i32 as i64),
                "ROR by 1"
            );
        });
    }

    #[test]
    fn test_arm_clz_comprehensive() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test CLZ(0) = 32
            state.set_reg(&Reg::R1, BV::from_i64(0, 32));
            let clz_op = ArmOp::Clz {
                rd: Reg::R0,
                rm: Reg::R1,
            };
            encoder.encode_op(&clz_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(32),
                "CLZ(0) should be 32"
            );

            // Test CLZ(1) = 31
            state.set_reg(&Reg::R1, BV::from_i64(1, 32));
            encoder.encode_op(&clz_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(31),
                "CLZ(1) should be 31"
            );

            // Test CLZ(0x80000000) = 0
            state.set_reg(&Reg::R1, BV::from_u64(0x80000000, 32));
            encoder.encode_op(&clz_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0),
                "CLZ(0x80000000) should be 0"
            );

            // Test CLZ(0x00FF0000) = 8
            state.set_reg(&Reg::R1, BV::from_u64(0x00FF0000, 32));
            encoder.encode_op(&clz_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(8),
                "CLZ(0x00FF0000) should be 8"
            );

            // Test CLZ(0x00001000) = 19
            state.set_reg(&Reg::R1, BV::from_u64(0x00001000, 32));
            encoder.encode_op(&clz_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(19),
                "CLZ(0x00001000) should be 19"
            );

            // Test CLZ(0xFFFFFFFF) = 0
            state.set_reg(&Reg::R1, BV::from_u64(0xFFFFFFFF, 32));
            encoder.encode_op(&clz_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0),
                "CLZ(0xFFFFFFFF) should be 0"
            );
        });
    }

    #[test]
    fn test_arm_rbit_comprehensive() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            let rbit_op = ArmOp::Rbit {
                rd: Reg::R0,
                rm: Reg::R1,
            };

            // Test RBIT(0) = 0
            state.set_reg(&Reg::R1, BV::from_i64(0, 32));
            encoder.encode_op(&rbit_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(0),
                "RBIT(0) should be 0"
            );

            // Test RBIT(1) = 0x80000000 (bit 0 → bit 31)
            state.set_reg(&Reg::R1, BV::from_i64(1, 32));
            encoder.encode_op(&rbit_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_u64(),
                Some(0x80000000),
                "RBIT(1) should be 0x80000000"
            );

            // Test RBIT(0x80000000) = 1 (bit 31 → bit 0)
            state.set_reg(&Reg::R1, BV::from_u64(0x80000000, 32));
            encoder.encode_op(&rbit_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "RBIT(0x80000000) should be 1"
            );

            // Test RBIT(0xFF000000) = 0x000000FF (top byte → bottom byte)
            state.set_reg(&Reg::R1, BV::from_u64(0xFF000000, 32));
            encoder.encode_op(&rbit_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_u64(),
                Some(0x000000FF),
                "RBIT(0xFF000000) should be 0x000000FF"
            );

            // Test RBIT(0x12345678) - specific pattern
            state.set_reg(&Reg::R1, BV::from_u64(0x12345678, 32));
            encoder.encode_op(&rbit_op, &mut state);
            // 0x12345678 reversed = 0x1E6A2C48
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_u64(),
                Some(0x1E6A2C48),
                "RBIT(0x12345678) should be 0x1E6A2C48"
            );

            // Test RBIT(0xFFFFFFFF) = 0xFFFFFFFF (all bits stay)
            state.set_reg(&Reg::R1, BV::from_u64(0xFFFFFFFF, 32));
            encoder.encode_op(&rbit_op, &mut state);
            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_u64(),
                Some(0xFFFFFFFF),
                "RBIT(0xFFFFFFFF) should be 0xFFFFFFFF"
            );
        });
    }

    #[test]
    fn test_arm_cmp_flags() {
        // Test CMP instruction and condition flag updates

        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test 1: CMP with equal values (10 - 10 = 0)
            // Should set: Z=1, N=0, C=1 (no borrow), V=0
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));

            let cmp_op = ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            };
            encoder.encode_op(&cmp_op, &mut state);

            assert_eq!(
                state.flags.z.simplify().as_bool(),
                Some(true),
                "Z flag should be set (equal)"
            );
            assert_eq!(
                state.flags.n.simplify().as_bool(),
                Some(false),
                "N flag should be clear (non-negative)"
            );
            assert_eq!(
                state.flags.c.simplify().as_bool(),
                Some(true),
                "C flag should be set (no borrow)"
            );
            assert_eq!(
                state.flags.v.simplify().as_bool(),
                Some(false),
                "V flag should be clear (no overflow)"
            );

            // Test 2: CMP with first > second (20 - 10 = 10)
            // Should set: Z=0, N=0, C=1 (no borrow), V=0
            state.set_reg(&Reg::R0, BV::from_i64(20, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));
            encoder.encode_op(&cmp_op, &mut state);

            assert_eq!(
                state.flags.z.simplify().as_bool(),
                Some(false),
                "Z flag should be clear (not equal)"
            );
            assert_eq!(
                state.flags.n.simplify().as_bool(),
                Some(false),
                "N flag should be clear (positive result)"
            );
            assert_eq!(
                state.flags.c.simplify().as_bool(),
                Some(true),
                "C flag should be set (no borrow)"
            );
            assert_eq!(
                state.flags.v.simplify().as_bool(),
                Some(false),
                "V flag should be clear (no overflow)"
            );

            // Test 3: CMP with first < second (unsigned: will wrap)
            // 10 - 20 = -10 (0xFFFFFFF6 in two's complement)
            // Should set: Z=0, N=1 (negative), C=0 (borrow), V=0
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(20, 32));
            encoder.encode_op(&cmp_op, &mut state);

            assert_eq!(
                state.flags.z.simplify().as_bool(),
                Some(false),
                "Z flag should be clear"
            );
            assert_eq!(
                state.flags.n.simplify().as_bool(),
                Some(true),
                "N flag should be set (negative result)"
            );
            assert_eq!(
                state.flags.c.simplify().as_bool(),
                Some(false),
                "C flag should be clear (borrow occurred)"
            );
            assert_eq!(
                state.flags.v.simplify().as_bool(),
                Some(false),
                "V flag should be clear"
            );

            // Test 4: Signed overflow case
            // Subtracting large negative from positive should overflow
            // 0x7FFFFFFF (max positive) - 0x80000000 (min negative)
            // Result wraps to negative, but mathematically should be huge positive
            state.set_reg(&Reg::R0, BV::from_i64(0x7FFFFFFF, 32));
            state.set_reg(&Reg::R1, BV::from_i64(-2147483648i64, 32)); // 0x80000000
            encoder.encode_op(&cmp_op, &mut state);

            assert_eq!(
                state.flags.z.simplify().as_bool(),
                Some(false),
                "Z flag should be clear"
            );
            assert_eq!(
                state.flags.n.simplify().as_bool(),
                Some(true),
                "N flag should be set (wrapped result)"
            );
            assert_eq!(
                state.flags.c.simplify().as_bool(),
                Some(false),
                "C flag should be clear"
            );
            assert_eq!(
                state.flags.v.simplify().as_bool(),
                Some(true),
                "V flag should be set (overflow)"
            );

            // Test 5: Zero comparison
            state.set_reg(&Reg::R0, BV::from_i64(0, 32));
            state.set_reg(&Reg::R1, BV::from_i64(0, 32));
            encoder.encode_op(&cmp_op, &mut state);

            assert_eq!(
                state.flags.z.simplify().as_bool(),
                Some(true),
                "Z flag should be set (0 - 0 = 0)"
            );
            assert_eq!(
                state.flags.n.simplify().as_bool(),
                Some(false),
                "N flag should be clear"
            );
            assert_eq!(
                state.flags.c.simplify().as_bool(),
                Some(true),
                "C flag should be set"
            );
            assert_eq!(
                state.flags.v.simplify().as_bool(),
                Some(false),
                "V flag should be clear"
            );
        });
    }

    #[test]
    fn test_arm_flags_all_combinations() {
        // Test that flags correctly distinguish all comparison outcomes

        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            let cmp_op = ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            };

            // Test signed comparisons using flags
            // For signed comparison A vs B (after CMP A, B):
            // - EQ (equal): Z=1
            // - NE (not equal): Z=0
            // - LT (less than): N != V
            // - LE (less or equal): Z=1 OR (N != V)
            // - GT (greater than): Z=0 AND (N == V)
            // - GE (greater or equal): N == V

            // Case: 5 compared to 10 (5 < 10)
            state.set_reg(&Reg::R0, BV::from_i64(5, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));
            encoder.encode_op(&cmp_op, &mut state);

            let n = state.flags.n.simplify().as_bool().unwrap();
            let z = state.flags.z.simplify().as_bool().unwrap();
            let v = state.flags.v.simplify().as_bool().unwrap();

            assert!(!z, "Not equal");
            assert!(n != v, "5 < 10 signed (N != V)");

            // Case: -5 compared to 10 (-5 < 10)
            state.set_reg(&Reg::R0, BV::from_i64(-5, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));
            encoder.encode_op(&cmp_op, &mut state);

            let n = state.flags.n.simplify().as_bool().unwrap();
            let v = state.flags.v.simplify().as_bool().unwrap();
            assert!(n != v, "-5 < 10 signed (N != V)");
        });
    }

    #[test]
    fn test_arm_setcond_eq() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test EQ condition: 10 == 10
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));

            // CMP R0, R1 (sets Z=1 since equal)
            let cmp_op = ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            };
            encoder.encode_op(&cmp_op, &mut state);

            // SetCond R0, EQ (should set R0 = 1)
            let setcond_op = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::EQ,
            };
            encoder.encode_op(&setcond_op, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "EQ condition (10 == 10) should return 1"
            );

            // Test NE condition: 10 != 5
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(5, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_ne = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::NE,
            };
            encoder.encode_op(&setcond_ne, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "NE condition (10 != 5) should return 1"
            );
        });
    }

    #[test]
    fn test_arm_setcond_signed() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test LT signed: 5 < 10
            state.set_reg(&Reg::R0, BV::from_i64(5, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));

            let cmp_op = ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            };
            encoder.encode_op(&cmp_op, &mut state);

            let setcond_lt = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::LT,
            };
            encoder.encode_op(&setcond_lt, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "LT signed (5 < 10) should return 1"
            );

            // Test GE signed: 10 >= 5
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(5, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_ge = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::GE,
            };
            encoder.encode_op(&setcond_ge, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "GE signed (10 >= 5) should return 1"
            );

            // Test GT signed: 10 > 5
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(5, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_gt = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::GT,
            };
            encoder.encode_op(&setcond_gt, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "GT signed (10 > 5) should return 1"
            );

            // Test LE signed: 5 <= 10
            state.set_reg(&Reg::R0, BV::from_i64(5, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_le = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::LE,
            };
            encoder.encode_op(&setcond_le, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "LE signed (5 <= 10) should return 1"
            );
        });
    }

    #[test]
    fn test_arm_setcond_unsigned() {
        with_verification_context(|| {
            let encoder = ArmSemantics::new();
            let mut state = ArmState::new_symbolic();

            // Test LO unsigned: 5 < 10
            state.set_reg(&Reg::R0, BV::from_i64(5, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));

            let cmp_op = ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            };
            encoder.encode_op(&cmp_op, &mut state);

            let setcond_lo = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::LO,
            };
            encoder.encode_op(&setcond_lo, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "LO unsigned (5 < 10) should return 1"
            );

            // Test HS unsigned: 10 >= 5
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(5, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_hs = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::HS,
            };
            encoder.encode_op(&setcond_hs, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "HS unsigned (10 >= 5) should return 1"
            );

            // Test HI unsigned: 10 > 5
            state.set_reg(&Reg::R0, BV::from_i64(10, 32));
            state.set_reg(&Reg::R1, BV::from_i64(5, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_hi = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::HI,
            };
            encoder.encode_op(&setcond_hi, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "HI unsigned (10 > 5) should return 1"
            );

            // Test LS unsigned: 5 <= 10
            state.set_reg(&Reg::R0, BV::from_i64(5, 32));
            state.set_reg(&Reg::R1, BV::from_i64(10, 32));

            encoder.encode_op(&cmp_op, &mut state);

            let setcond_ls = ArmOp::SetCond {
                rd: Reg::R0,
                cond: synth_synthesis::Condition::LS,
            };
            encoder.encode_op(&setcond_ls, &mut state);

            assert_eq!(
                state.get_reg(&Reg::R0).simplify().as_i64(),
                Some(1),
                "LS unsigned (5 <= 10) should return 1"
            );
        });
    }
}
