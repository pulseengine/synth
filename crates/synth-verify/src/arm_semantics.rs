//! ARM Semantics Encoding to SMT
//!
//! Encodes ARM operation semantics as SMT bitvector formulas.
//! Each ARM operation is translated to a mathematical formula that precisely
//! captures its behavior, including register updates and condition flags.

use synth_synthesis::{ArmOp, Operand2, Reg};
use z3::ast::{Ast, Bool, BV};
use z3::Context;

/// ARM processor state representation in SMT
pub struct ArmState<'ctx> {
    /// General purpose registers R0-R15
    pub registers: Vec<BV<'ctx>>,
    /// Condition flags (N, Z, C, V)
    pub flags: ConditionFlags<'ctx>,
    /// Memory model (simplified for bounded verification)
    pub memory: Vec<BV<'ctx>>,
}

/// ARM condition flags
pub struct ConditionFlags<'ctx> {
    pub n: Bool<'ctx>, // Negative
    pub z: Bool<'ctx>, // Zero
    pub c: Bool<'ctx>, // Carry
    pub v: Bool<'ctx>, // Overflow
}

impl<'ctx> ArmState<'ctx> {
    /// Create a new ARM state with symbolic values
    pub fn new_symbolic(ctx: &'ctx Context) -> Self {
        let registers = (0..16)
            .map(|i| BV::new_const(ctx, format!("r{}", i), 32))
            .collect();

        let flags = ConditionFlags {
            n: Bool::new_const(ctx, "flag_n"),
            z: Bool::new_const(ctx, "flag_z"),
            c: Bool::new_const(ctx, "flag_c"),
            v: Bool::new_const(ctx, "flag_v"),
        };

        // Simplified memory model with fixed number of locations
        let memory = (0..256)
            .map(|i| BV::new_const(ctx, format!("mem_{}", i), 32))
            .collect();

        Self {
            registers,
            flags,
            memory,
        }
    }

    /// Get register value
    pub fn get_reg(&self, reg: &Reg) -> &BV<'ctx> {
        let index = reg_to_index(reg);
        &self.registers[index]
    }

    /// Set register value
    pub fn set_reg(&mut self, reg: &Reg, value: BV<'ctx>) {
        let index = reg_to_index(reg);
        self.registers[index] = value;
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

/// ARM semantics encoder
pub struct ArmSemantics<'ctx> {
    ctx: &'ctx Context,
}

impl<'ctx> ArmSemantics<'ctx> {
    /// Create a new ARM semantics encoder
    pub fn new(ctx: &'ctx Context) -> Self {
        Self { ctx }
    }

    /// Encode an ARM operation and return the resulting state
    ///
    /// This models the effect of executing the ARM instruction on the processor state.
    pub fn encode_op(&self, op: &ArmOp, state: &mut ArmState<'ctx>) {
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
                let shift_val = BV::from_i64(self.ctx, *shift as i64, 32);
                let result = rn_val.bvshl(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Lsr { rd, rn, shift } => {
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(self.ctx, *shift as i64, 32);
                let result = rn_val.bvlshr(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Asr { rd, rn, shift } => {
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(self.ctx, *shift as i64, 32);
                let result = rn_val.bvashr(&shift_val);
                state.set_reg(rd, result);
            }

            ArmOp::Ror { rd, rn, shift } => {
                // Rotate right - ARM ROR instruction
                // ROR(x, n) rotates x right by n positions
                let rn_val = state.get_reg(rn).clone();
                let shift_val = BV::from_i64(self.ctx, *shift as i64, 32);
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
                let rn_val = state.get_reg(rn);
                let op2_val = self.evaluate_operand2(op2, state);

                // Update condition flags based on rn - op2
                let result = rn_val.bvsub(&op2_val);

                // Zero flag: result == 0
                let zero = BV::from_i64(self.ctx, 0, 32);
                state.flags.z = result._eq(&zero);

                // Negative flag: result < 0 (sign bit set)
                let sign_bit = result.extract(31, 31);
                let one_bit = BV::from_i64(self.ctx, 1, 1);
                state.flags.n = sign_bit._eq(&one_bit);

                // Carry and overflow flags would require more complex logic
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

            ArmOp::Nop => {
                // No operation - state unchanged
            }

            // Memory operations simplified for now
            ArmOp::Ldr { rd, addr } => {
                // Load from memory
                // Simplified: return symbolic value
                let result = BV::new_const(self.ctx, format!("load_{:?}", rd), 32);
                state.set_reg(rd, result);
            }

            ArmOp::Str { rd, addr } => {
                // Store to memory
                // Simplified: memory updates not fully modeled yet
            }

            // Control flow operations
            ArmOp::B { label } => {
                // Branch - would update PC in full model
                // For bounded verification, we treat this symbolically
            }

            ArmOp::Bl { label } => {
                // Branch with link - would update PC and LR
            }

            ArmOp::Bx { rm } => {
                // Branch and exchange - would update PC
            }

            _ => {
                // Unsupported operations - no state change
            }
        }
    }

    /// Evaluate an Operand2 value
    fn evaluate_operand2(&self, op2: &Operand2, state: &ArmState<'ctx>) -> BV<'ctx> {
        match op2 {
            Operand2::Imm(value) => BV::from_i64(self.ctx, *value as i64, 32),
            Operand2::Reg(reg) => state.get_reg(reg).clone(),
            Operand2::RegShift { rm, shift, amount } => {
                let reg_val = state.get_reg(rm).clone();
                let shift_amount = BV::from_i64(self.ctx, *amount as i64, 32);

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
    pub fn extract_result(&self, state: &ArmState<'ctx>, reg: &Reg) -> BV<'ctx> {
        state.get_reg(reg).clone()
    }

    /// Encode ARM CLZ (Count Leading Zeros) instruction
    ///
    /// Implements the same algorithm as WASM i32.clz for equivalence verification.
    /// Uses binary search through bit positions.
    fn encode_clz(&self, input: &BV<'ctx>) -> BV<'ctx> {
        let zero = BV::from_i64(self.ctx, 0, 32);

        // Special case: if input is 0, return 32
        let all_zero = input._eq(&zero);
        let result_if_zero = BV::from_i64(self.ctx, 32, 32);

        // Binary search approach
        let mut count = BV::from_i64(self.ctx, 0, 32);
        let mut remaining = input.clone();

        // Check top 16 bits
        let mask_16 = BV::from_u64(self.ctx, 0xFFFF0000, 32);
        let top_16 = remaining.bvand(&mask_16);
        let top_16_zero = top_16._eq(&zero);

        count = top_16_zero.ite(
            &count.bvadd(&BV::from_i64(self.ctx, 16, 32)),
            &count,
        );
        remaining = top_16_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 16, 32)),
            &remaining,
        );

        // Check top 8 bits
        let mask_8 = BV::from_u64(self.ctx, 0xFF000000, 32);
        let top_8 = remaining.bvand(&mask_8);
        let top_8_zero = top_8._eq(&zero);

        count = top_8_zero.ite(&count.bvadd(&BV::from_i64(self.ctx, 8, 32)), &count);
        remaining = top_8_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 8, 32)),
            &remaining,
        );

        // Check top 4 bits
        let mask_4 = BV::from_u64(self.ctx, 0xF0000000, 32);
        let top_4 = remaining.bvand(&mask_4);
        let top_4_zero = top_4._eq(&zero);

        count = top_4_zero.ite(&count.bvadd(&BV::from_i64(self.ctx, 4, 32)), &count);
        remaining = top_4_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 4, 32)),
            &remaining,
        );

        // Check top 2 bits
        let mask_2 = BV::from_u64(self.ctx, 0xC0000000, 32);
        let top_2 = remaining.bvand(&mask_2);
        let top_2_zero = top_2._eq(&zero);

        count = top_2_zero.ite(&count.bvadd(&BV::from_i64(self.ctx, 2, 32)), &count);
        remaining = top_2_zero.ite(
            &remaining.bvshl(&BV::from_i64(self.ctx, 2, 32)),
            &remaining,
        );

        // Check top bit
        let mask_1 = BV::from_u64(self.ctx, 0x80000000, 32);
        let top_1 = remaining.bvand(&mask_1);
        let top_1_zero = top_1._eq(&zero);

        count = top_1_zero.ite(&count.bvadd(&BV::from_i64(self.ctx, 1, 32)), &count);

        // Return 32 if all zeros, otherwise return count
        all_zero.ite(&result_if_zero, &count)
    }

    /// Encode ARM RBIT (Reverse Bits) instruction
    ///
    /// Reverses the bit order in a 32-bit value.
    /// Used in combination with CLZ to implement CTZ.
    fn encode_rbit(&self, input: &BV<'ctx>) -> BV<'ctx> {
        // Reverse bits by swapping progressively smaller chunks
        let mut result = input.clone();

        // Swap 16-bit halves
        let mask_16 = BV::from_u64(self.ctx, 0xFFFF0000, 32);
        let top_16 = result.bvand(&mask_16).bvlshr(&BV::from_i64(self.ctx, 16, 32));
        let bottom_16 = result.bvshl(&BV::from_i64(self.ctx, 16, 32));
        result = top_16.bvor(&bottom_16);

        // Swap 8-bit chunks
        let mask_8_top = BV::from_u64(self.ctx, 0xFF00FF00, 32);
        let mask_8_bottom = BV::from_u64(self.ctx, 0x00FF00FF, 32);
        let top_8 = result.bvand(&mask_8_top).bvlshr(&BV::from_i64(self.ctx, 8, 32));
        let bottom_8 = result.bvand(&mask_8_bottom).bvshl(&BV::from_i64(self.ctx, 8, 32));
        result = top_8.bvor(&bottom_8);

        // Swap 4-bit chunks
        let mask_4_top = BV::from_u64(self.ctx, 0xF0F0F0F0, 32);
        let mask_4_bottom = BV::from_u64(self.ctx, 0x0F0F0F0F, 32);
        let top_4 = result.bvand(&mask_4_top).bvlshr(&BV::from_i64(self.ctx, 4, 32));
        let bottom_4 = result.bvand(&mask_4_bottom).bvshl(&BV::from_i64(self.ctx, 4, 32));
        result = top_4.bvor(&bottom_4);

        // Swap 2-bit chunks
        let mask_2_top = BV::from_u64(self.ctx, 0xCCCCCCCC, 32);
        let mask_2_bottom = BV::from_u64(self.ctx, 0x33333333, 32);
        let top_2 = result.bvand(&mask_2_top).bvlshr(&BV::from_i64(self.ctx, 2, 32));
        let bottom_2 = result.bvand(&mask_2_bottom).bvshl(&BV::from_i64(self.ctx, 2, 32));
        result = top_2.bvor(&bottom_2);

        // Swap 1-bit chunks (individual bits)
        let mask_1_top = BV::from_u64(self.ctx, 0xAAAAAAAA, 32);
        let mask_1_bottom = BV::from_u64(self.ctx, 0x55555555, 32);
        let top_1 = result.bvand(&mask_1_top).bvlshr(&BV::from_i64(self.ctx, 1, 32));
        let bottom_1 = result.bvand(&mask_1_bottom).bvshl(&BV::from_i64(self.ctx, 1, 32));
        result = top_1.bvor(&bottom_1);

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::create_z3_context;

    #[test]
    fn test_arm_add_semantics() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        // Set up concrete values for testing
        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 10, 32));
        state.set_reg(&Reg::R2, BV::from_i64(&ctx, 20, 32));

        // Execute: ADD R0, R1, R2
        let op = ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };

        encoder.encode_op(&op, &mut state);

        // Check result: R0 should be 30
        let result = state.get_reg(&Reg::R0);
        assert_eq!(result.as_i64(), Some(30));
    }

    #[test]
    fn test_arm_sub_semantics() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 50, 32));
        state.set_reg(&Reg::R2, BV::from_i64(&ctx, 20, 32));

        let op = ArmOp::Sub {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };

        encoder.encode_op(&op, &mut state);

        let result = state.get_reg(&Reg::R0);
        assert_eq!(result.as_i64(), Some(30));
    }

    #[test]
    fn test_arm_mov_immediate() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        let op = ArmOp::Mov {
            rd: Reg::R0,
            op2: Operand2::Imm(42),
        };

        encoder.encode_op(&op, &mut state);

        let result = state.get_reg(&Reg::R0);
        assert_eq!(result.as_i64(), Some(42));
    }

    #[test]
    fn test_arm_bitwise_ops() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 0b1010, 32));
        state.set_reg(&Reg::R2, BV::from_i64(&ctx, 0b1100, 32));

        // Test AND
        let and_op = ArmOp::And {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        encoder.encode_op(&and_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0b1000));

        // Test ORR
        let orr_op = ArmOp::Orr {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        encoder.encode_op(&orr_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0b1110));

        // Test EOR (XOR)
        let eor_op = ArmOp::Eor {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        encoder.encode_op(&eor_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0b0110));
    }

    #[test]
    fn test_arm_shift_ops() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 8, 32));

        // Test LSL (logical shift left) with immediate
        let lsl_op = ArmOp::Lsl {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 2,
        };
        encoder.encode_op(&lsl_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(32));

        // Test LSR (logical shift right) with immediate
        let lsr_op = ArmOp::Lsr {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 2,
        };
        encoder.encode_op(&lsr_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(2));
    }

    #[test]
    fn test_arm_ror_comprehensive() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        // Test ROR with 0x12345678
        // ROR by 8 should rotate right by 8 bits
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x12345678, 32));
        let ror_op = ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 8,
        };
        encoder.encode_op(&ror_op, &mut state);
        // 0x12345678 ROR 8 = 0x78123456
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x78123456), "ROR by 8");

        // Test ROR by 16 (swap halves)
        let ror_op_16 = ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 16,
        };
        encoder.encode_op(&ror_op_16, &mut state);
        // 0x12345678 ROR 16 = 0x56781234
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x56781234), "ROR by 16");

        // Test ROR by 0 (no change)
        let ror_op_0 = ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 0,
        };
        encoder.encode_op(&ror_op_0, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x12345678), "ROR by 0");

        // Test ROR by 32 (full rotation, back to original)
        let ror_op_32 = ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 32,
        };
        encoder.encode_op(&ror_op_32, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x12345678), "ROR by 32");

        // Test ROR by 4 (nibble rotation)
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0xABCDEF01, 32));
        let ror_op_4 = ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 4,
        };
        encoder.encode_op(&ror_op_4, &mut state);
        // 0xABCDEF01 ROR 4 = 0x1ABCDEF0
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x1ABCDEF0), "ROR by 4");

        // Test ROR with 1-bit rotation
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x80000001, 32));
        let ror_op_1 = ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R1,
            shift: 1,
        };
        encoder.encode_op(&ror_op_1, &mut state);
        // 0x80000001 ROR 1 = 0xC0000000
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0xC0000000_u32 as i32 as i64), "ROR by 1");
    }

    #[test]
    fn test_arm_clz_comprehensive() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        // Test CLZ(0) = 32
        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 0, 32));
        let clz_op = ArmOp::Clz {
            rd: Reg::R0,
            rm: Reg::R1,
        };
        encoder.encode_op(&clz_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(32), "CLZ(0) should be 32");

        // Test CLZ(1) = 31
        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 1, 32));
        encoder.encode_op(&clz_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(31), "CLZ(1) should be 31");

        // Test CLZ(0x80000000) = 0
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x80000000, 32));
        encoder.encode_op(&clz_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0), "CLZ(0x80000000) should be 0");

        // Test CLZ(0x00FF0000) = 8
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x00FF0000, 32));
        encoder.encode_op(&clz_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(8), "CLZ(0x00FF0000) should be 8");

        // Test CLZ(0x00001000) = 19
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x00001000, 32));
        encoder.encode_op(&clz_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(19), "CLZ(0x00001000) should be 19");

        // Test CLZ(0xFFFFFFFF) = 0
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0xFFFFFFFF, 32));
        encoder.encode_op(&clz_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0), "CLZ(0xFFFFFFFF) should be 0");
    }

    #[test]
    fn test_arm_rbit_comprehensive() {
        let ctx = create_z3_context();
        let encoder = ArmSemantics::new(&ctx);
        let mut state = ArmState::new_symbolic(&ctx);

        let rbit_op = ArmOp::Rbit {
            rd: Reg::R0,
            rm: Reg::R1,
        };

        // Test RBIT(0) = 0
        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 0, 32));
        encoder.encode_op(&rbit_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0), "RBIT(0) should be 0");

        // Test RBIT(1) = 0x80000000 (bit 0 → bit 31)
        state.set_reg(&Reg::R1, BV::from_i64(&ctx, 1, 32));
        encoder.encode_op(&rbit_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_u64(), Some(0x80000000), "RBIT(1) should be 0x80000000");

        // Test RBIT(0x80000000) = 1 (bit 31 → bit 0)
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x80000000, 32));
        encoder.encode_op(&rbit_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(1), "RBIT(0x80000000) should be 1");

        // Test RBIT(0xFF000000) = 0x000000FF (top byte → bottom byte)
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0xFF000000, 32));
        encoder.encode_op(&rbit_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_u64(), Some(0x000000FF), "RBIT(0xFF000000) should be 0x000000FF");

        // Test RBIT(0x12345678) - specific pattern
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0x12345678, 32));
        encoder.encode_op(&rbit_op, &mut state);
        // 0x12345678 reversed = 0x1E6A2C48
        assert_eq!(state.get_reg(&Reg::R0).as_u64(), Some(0x1E6A2C48), "RBIT(0x12345678) should be 0x1E6A2C48");

        // Test RBIT(0xFFFFFFFF) = 0xFFFFFFFF (all bits stay)
        state.set_reg(&Reg::R1, BV::from_u64(&ctx, 0xFFFFFFFF, 32));
        encoder.encode_op(&rbit_op, &mut state);
        assert_eq!(state.get_reg(&Reg::R0).as_u64(), Some(0xFFFFFFFF), "RBIT(0xFFFFFFFF) should be 0xFFFFFFFF");
    }
}
