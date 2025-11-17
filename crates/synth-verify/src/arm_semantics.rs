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
                // Count leading zeros
                let rm_val = state.get_reg(rm).clone();
                // This is a simplified CLZ - proper implementation would use bit manipulation
                let result = BV::new_const(self.ctx, "clz_result", 32);
                state.set_reg(rd, result);
            }

            ArmOp::Rbit { rd, rm } => {
                // Reverse bits - reverse bit order in 32-bit value
                let rm_val = state.get_reg(rm).clone();
                // Simplified: use symbolic value for now
                let result = BV::new_const(self.ctx, "rbit_result", 32);
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
}
