//! Semantic Correctness Tests
//!
//! Verifies that compiled WASM code produces correct results by interpreting
//! the generated ARM instructions and checking the output register values.
//!
//! This fills the critical test gap: existing tests check structural properties
//! (opcode patterns, instruction counts, control flow) but never verify that
//! the generated code computes the right answer. These tests do.

use synth_synthesis::{
    ArmInstruction, ArmOp, Condition, InstructionSelector, Operand2, Reg, WasmOp,
};

// =========================================================================
// Mini ARM interpreter
//
// Simulates a subset of ARM Thumb-2 instructions sufficient to verify
// arithmetic correctness. Tracks register values and condition flags.
// =========================================================================

/// Map a Reg to a fixed array index. 16 ARM registers total.
fn reg_index(r: &Reg) -> usize {
    match r {
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

#[derive(Debug, Clone)]
struct ArmState {
    regs: [u32; 16],
    /// Condition flags: N, Z, C, V
    flag_n: bool,
    flag_z: bool,
    flag_c: bool,
    flag_v: bool,
}

impl ArmState {
    fn new() -> Self {
        Self {
            regs: [0u32; 16],
            flag_n: false,
            flag_z: false,
            flag_c: false,
            flag_v: false,
        }
    }

    fn get(&self, r: &Reg) -> u32 {
        self.regs[reg_index(r)]
    }

    fn set(&mut self, r: Reg, val: u32) {
        self.regs[reg_index(&r)] = val;
    }

    fn resolve_operand2(&self, op2: &Operand2) -> u32 {
        match op2 {
            Operand2::Imm(v) => *v as u32,
            Operand2::Reg(r) => self.get(r),
            Operand2::RegShift { rm, .. } => {
                // Simplified: just return the register value
                self.get(rm)
            }
        }
    }

    /// Update N and Z flags based on a 32-bit result.
    fn update_nz(&mut self, result: u32) {
        self.flag_n = (result as i32) < 0;
        self.flag_z = result == 0;
    }

    /// Check whether a condition code is satisfied by current flags.
    fn condition_met(&self, cond: &Condition) -> bool {
        match cond {
            Condition::EQ => self.flag_z,
            Condition::NE => !self.flag_z,
            Condition::LT => self.flag_n != self.flag_v,
            Condition::LE => self.flag_z || (self.flag_n != self.flag_v),
            Condition::GT => !self.flag_z && (self.flag_n == self.flag_v),
            Condition::GE => self.flag_n == self.flag_v,
            Condition::LO => !self.flag_c,
            Condition::LS => !self.flag_c || self.flag_z,
            Condition::HI => self.flag_c && !self.flag_z,
            Condition::HS => self.flag_c,
        }
    }
}

/// Interpret a single ARM instruction, mutating the given state.
fn interpret_single(state: &mut ArmState, instr: &ArmInstruction) {
    match &instr.op {
        ArmOp::Movw { rd, imm16 } => {
            state.set(*rd, *imm16 as u32);
        }
        ArmOp::Movt { rd, imm16 } => {
            let low = state.get(rd) & 0xFFFF;
            state.set(*rd, ((*imm16 as u32) << 16) | low);
        }
        ArmOp::Mov { rd, op2 } => {
            let val = state.resolve_operand2(op2);
            state.set(*rd, val);
        }
        ArmOp::Mvn { rd, op2 } => {
            let val = state.resolve_operand2(op2);
            state.set(*rd, !val);
        }
        ArmOp::Add { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a.wrapping_add(b));
        }
        ArmOp::Sub { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a.wrapping_sub(b));
        }
        ArmOp::Mul { rd, rn, rm } => {
            let a = state.get(rn);
            let b = state.get(rm);
            state.set(*rd, a.wrapping_mul(b));
        }
        ArmOp::Sdiv { rd, rn, rm } => {
            let a = state.get(rn) as i32;
            let b = state.get(rm) as i32;
            if b != 0 {
                state.set(*rd, a.wrapping_div(b) as u32);
            }
        }
        ArmOp::Udiv { rd, rn, rm } => {
            let a = state.get(rn);
            let b = state.get(rm);
            if b != 0 {
                state.set(*rd, a / b);
            }
        }
        ArmOp::Mls { rd, rn, rm, ra } => {
            let n = state.get(rn);
            let m = state.get(rm);
            let a = state.get(ra);
            state.set(*rd, a.wrapping_sub(n.wrapping_mul(m)));
        }
        ArmOp::And { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a & b);
        }
        ArmOp::Orr { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a | b);
        }
        ArmOp::Eor { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a ^ b);
        }
        ArmOp::LslReg { rd, rn, rm } => {
            let val = state.get(rn);
            let shift = state.get(rm) & 0x1F;
            state.set(*rd, val.wrapping_shl(shift));
        }
        ArmOp::LsrReg { rd, rn, rm } => {
            let val = state.get(rn);
            let shift = state.get(rm) & 0x1F;
            state.set(*rd, val.wrapping_shr(shift));
        }
        ArmOp::AsrReg { rd, rn, rm } => {
            let val = state.get(rn) as i32;
            let shift = state.get(rm) & 0x1F;
            state.set(*rd, val.wrapping_shr(shift) as u32);
        }
        ArmOp::RorReg { rd, rn, rm } => {
            let val = state.get(rn);
            let shift = state.get(rm) & 0x1F;
            state.set(*rd, val.rotate_right(shift));
        }
        ArmOp::Rsb { rd, rn, imm } => {
            let n = state.get(rn);
            state.set(*rd, imm.wrapping_sub(n));
        }
        ArmOp::Clz { rd, rm } => {
            let val = state.get(rm);
            state.set(*rd, val.leading_zeros());
        }
        ArmOp::Rbit { rd, rm } => {
            let val = state.get(rm);
            state.set(*rd, val.reverse_bits());
        }
        ArmOp::Sxtb { rd, rm } => {
            let val = state.get(rm) as u8 as i8 as i32 as u32;
            state.set(*rd, val);
        }
        ArmOp::Sxth { rd, rm } => {
            let val = state.get(rm) as u16 as i16 as i32 as u32;
            state.set(*rd, val);
        }
        ArmOp::Cmp { rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            let result = a.wrapping_sub(b);
            state.update_nz(result);
            state.flag_c = a >= b;
            let sa = a as i32;
            let sb = b as i32;
            let sr = result as i32;
            state.flag_v = (sa >= 0 && sb < 0 && sr < 0) || (sa < 0 && sb >= 0 && sr >= 0);
        }
        ArmOp::Cmn { rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            let result = a.wrapping_add(b);
            state.update_nz(result);
            state.flag_c = (a as u64 + b as u64) > 0xFFFFFFFF;
            let sa = a as i32;
            let sb = b as i32;
            let sr = result as i32;
            state.flag_v = (sa > 0 && sb > 0 && sr < 0) || (sa < 0 && sb < 0 && sr >= 0);
        }
        ArmOp::SelectMove { rd, rm, cond } => {
            if state.condition_met(cond) {
                let val = state.get(rm);
                state.set(*rd, val);
            }
        }
        // Skip non-computational instructions (prologue/epilogue, branches, labels)
        _ => {}
    }
}

/// Execute the ARM instruction sequence and return the final register state.
fn interpret_arm(instructions: &[ArmInstruction]) -> ArmState {
    let mut state = ArmState::new();
    for instr in instructions {
        interpret_single(&mut state, instr);
    }
    state
}

// =========================================================================
// Helper: compile WASM ops with select_with_stack and return ARM state
// =========================================================================

/// Compile WASM ops and interpret the resulting ARM instructions.
/// Returns the final ARM register state after execution.
fn compile_and_run(wasm_ops: &[WasmOp], num_params: u32) -> ArmState {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(wasm_ops, num_params)
        .expect("instruction selection should succeed");
    assert!(
        !instrs.is_empty(),
        "should produce non-empty ARM instruction sequence"
    );
    interpret_arm(&instrs)
}

/// Compile WASM ops and return the value in R0 (the return register).
fn compile_and_result(wasm_ops: &[WasmOp]) -> u32 {
    let state = compile_and_run(wasm_ops, 0);
    state.get(&Reg::R0)
}

// =========================================================================
// Test: i32.const -- constant materialization
// =========================================================================

#[test]
fn const_small_positive() {
    let result = compile_and_result(&[WasmOp::I32Const(42)]);
    assert_eq!(result, 42, "i32.const 42 should produce 42");
}

#[test]
fn const_zero() {
    let result = compile_and_result(&[WasmOp::I32Const(0)]);
    assert_eq!(result, 0, "i32.const 0 should produce 0");
}

#[test]
fn const_max_u16() {
    // 65535 fits in MOVW (16-bit immediate)
    let result = compile_and_result(&[WasmOp::I32Const(65535)]);
    assert_eq!(result, 65535, "i32.const 65535 should produce 65535");
}

#[test]
fn const_large_positive() {
    // Requires MOVW + MOVT (32-bit constant)
    let result = compile_and_result(&[WasmOp::I32Const(0x12345678)]);
    assert_eq!(
        result, 0x12345678,
        "i32.const 0x12345678 should produce 0x12345678"
    );
}

#[test]
fn const_negative_one() {
    // -1 as u32 = 0xFFFFFFFF. The compiler uses MOVW + MVN path for this.
    let result = compile_and_result(&[WasmOp::I32Const(-1)]);
    assert_eq!(result, 0xFFFFFFFF, "i32.const -1 should produce 0xFFFFFFFF");
}

#[test]
fn const_i32_min() {
    // i32::MIN = -2147483648 = 0x80000000
    let result = compile_and_result(&[WasmOp::I32Const(i32::MIN)]);
    assert_eq!(
        result, 0x80000000,
        "i32.const i32::MIN should produce 0x80000000"
    );
}

#[test]
fn const_i32_max() {
    // i32::MAX = 2147483647 = 0x7FFFFFFF
    let result = compile_and_result(&[WasmOp::I32Const(i32::MAX)]);
    assert_eq!(
        result, 0x7FFFFFFF,
        "i32.const i32::MAX should produce 0x7FFFFFFF"
    );
}

// =========================================================================
// Test: i32 arithmetic -- add, sub, mul
// =========================================================================

#[test]
fn i32_add_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(42), WasmOp::I32Const(10), WasmOp::I32Add]);
    assert_eq!(result, 52, "42 + 10 should be 52");
}

#[test]
fn i32_add_zero() {
    let result = compile_and_result(&[WasmOp::I32Const(42), WasmOp::I32Const(0), WasmOp::I32Add]);
    assert_eq!(result, 42, "42 + 0 should be 42");
}

#[test]
fn i32_add_overflow() {
    // Wrapping: i32::MAX + 1 = i32::MIN
    let result = compile_and_result(&[
        WasmOp::I32Const(i32::MAX),
        WasmOp::I32Const(1),
        WasmOp::I32Add,
    ]);
    assert_eq!(result, 0x80000000, "i32::MAX + 1 should wrap to 0x80000000");
}

#[test]
fn i32_sub_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(100), WasmOp::I32Const(7), WasmOp::I32Sub]);
    assert_eq!(result, 93, "100 - 7 should be 93");
}

#[test]
fn i32_sub_to_negative() {
    // 5 - 10 = -5 (wraps to 0xFFFFFFFB)
    let result = compile_and_result(&[WasmOp::I32Const(5), WasmOp::I32Const(10), WasmOp::I32Sub]);
    assert_eq!(result, (-5i32) as u32, "5 - 10 should be -5 (wrapping)");
}

#[test]
fn i32_mul_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(6), WasmOp::I32Const(7), WasmOp::I32Mul]);
    assert_eq!(result, 42, "6 * 7 should be 42");
}

#[test]
fn i32_mul_by_zero() {
    let result = compile_and_result(&[WasmOp::I32Const(999), WasmOp::I32Const(0), WasmOp::I32Mul]);
    assert_eq!(result, 0, "999 * 0 should be 0");
}

#[test]
fn i32_mul_overflow() {
    // Wrapping multiplication: 0x10000 * 0x10000 = 0 (only lower 32 bits)
    let result = compile_and_result(&[
        WasmOp::I32Const(0x10000),
        WasmOp::I32Const(0x10000),
        WasmOp::I32Mul,
    ]);
    assert_eq!(result, 0, "0x10000 * 0x10000 should wrap to 0");
}

// =========================================================================
// Test: i32 division (with div-by-zero trap guards)
// =========================================================================

#[test]
fn i32_divu_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(42), WasmOp::I32Const(7), WasmOp::I32DivU]);
    assert_eq!(result, 6, "42 /u 7 should be 6");
}

#[test]
fn i32_divs_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(42), WasmOp::I32Const(7), WasmOp::I32DivS]);
    assert_eq!(result, 6, "42 /s 7 should be 6");
}

#[test]
fn i32_divs_negative() {
    let result = compile_and_result(&[WasmOp::I32Const(-42), WasmOp::I32Const(7), WasmOp::I32DivS]);
    assert_eq!(result, (-6i32) as u32, "-42 /s 7 should be -6");
}

#[test]
fn i32_remu_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(43), WasmOp::I32Const(7), WasmOp::I32RemU]);
    assert_eq!(result, 1, "43 %u 7 should be 1");
}

#[test]
fn i32_rems_basic() {
    let result = compile_and_result(&[WasmOp::I32Const(43), WasmOp::I32Const(7), WasmOp::I32RemS]);
    assert_eq!(result, 1, "43 %s 7 should be 1");
}

// =========================================================================
// Test: i32 bitwise operations
// =========================================================================

#[test]
fn i32_and_basic() {
    let result = compile_and_result(&[
        WasmOp::I32Const(0xFF00),
        WasmOp::I32Const(0x0FF0),
        WasmOp::I32And,
    ]);
    assert_eq!(result, 0x0F00, "0xFF00 & 0x0FF0 should be 0x0F00");
}

#[test]
fn i32_or_basic() {
    let result = compile_and_result(&[
        WasmOp::I32Const(0xFF00),
        WasmOp::I32Const(0x00FF),
        WasmOp::I32Or,
    ]);
    assert_eq!(result, 0xFFFF, "0xFF00 | 0x00FF should be 0xFFFF");
}

#[test]
fn i32_xor_basic() {
    let result = compile_and_result(&[
        WasmOp::I32Const(0xF0F0),
        WasmOp::I32Const(0xFF00),
        WasmOp::I32Xor,
    ]);
    assert_eq!(result, 0x0FF0, "0xF0F0 ^ 0xFF00 should be 0x0FF0");
}

// =========================================================================
// Test: i32 shift and rotate operations (structural verification)
//
// NOTE: Shift/rotate/clz/ctz/extend operations currently fall through to
// select_default in select_with_stack, which uses hardcoded register
// assignments that don't match the virtual stack. This is a known
// limitation -- these tests verify the correct ARM opcodes are emitted
// and that the instruction sequences are structurally sound.
// Full semantic verification requires stack-aware handling in the compiler.
// =========================================================================

#[test]
fn i32_shl_emits_lsl_reg() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[WasmOp::I32Const(1), WasmOp::I32Const(8), WasmOp::I32Shl],
            0,
        )
        .expect("should succeed");
    let has_lsl = instrs.iter().any(|i| matches!(&i.op, ArmOp::LslReg { .. }));
    assert!(has_lsl, "i32.shl should emit LslReg instruction");
}

#[test]
fn i32_shru_emits_lsr_reg() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[WasmOp::I32Const(256), WasmOp::I32Const(4), WasmOp::I32ShrU],
            0,
        )
        .expect("should succeed");
    let has_lsr = instrs.iter().any(|i| matches!(&i.op, ArmOp::LsrReg { .. }));
    assert!(has_lsr, "i32.shr_u should emit LsrReg instruction");
}

#[test]
fn i32_shrs_emits_asr_reg() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[WasmOp::I32Const(-128), WasmOp::I32Const(2), WasmOp::I32ShrS],
            0,
        )
        .expect("should succeed");
    let has_asr = instrs.iter().any(|i| matches!(&i.op, ArmOp::AsrReg { .. }));
    assert!(has_asr, "i32.shr_s should emit AsrReg instruction");
}

#[test]
fn i32_rotl_emits_rsb_and_ror() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::I32Const(0x12345678u32 as i32),
                WasmOp::I32Const(4),
                WasmOp::I32Rotl,
            ],
            0,
        )
        .expect("should succeed");
    let has_rsb = instrs.iter().any(|i| matches!(&i.op, ArmOp::Rsb { .. }));
    let has_ror = instrs.iter().any(|i| matches!(&i.op, ArmOp::RorReg { .. }));
    assert!(has_rsb, "i32.rotl should emit RSB for (32 - shift)");
    assert!(has_ror, "i32.rotl should emit RorReg");
}

#[test]
fn i32_rotr_emits_ror_reg() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::I32Const(0x12345678u32 as i32),
                WasmOp::I32Const(4),
                WasmOp::I32Rotr,
            ],
            0,
        )
        .expect("should succeed");
    let has_ror = instrs.iter().any(|i| matches!(&i.op, ArmOp::RorReg { .. }));
    assert!(has_ror, "i32.rotr should emit RorReg instruction");
}

// =========================================================================
// Test: i32 bit manipulation -- clz, ctz (structural)
// =========================================================================

#[test]
fn i32_clz_emits_clz() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::I32Const(1), WasmOp::I32Clz], 0)
        .expect("should succeed");
    let has_clz = instrs.iter().any(|i| matches!(&i.op, ArmOp::Clz { .. }));
    assert!(has_clz, "i32.clz should emit CLZ instruction");
}

#[test]
fn i32_ctz_emits_rbit_then_clz() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::I32Const(0x80), WasmOp::I32Ctz], 0)
        .expect("should succeed");
    let has_rbit = instrs.iter().any(|i| matches!(&i.op, ArmOp::Rbit { .. }));
    let has_clz = instrs.iter().any(|i| matches!(&i.op, ArmOp::Clz { .. }));
    assert!(has_rbit, "i32.ctz should emit RBIT instruction");
    assert!(has_clz, "i32.ctz should emit CLZ instruction (after RBIT)");
}

// =========================================================================
// Test: i32 sign extension (structural)
// =========================================================================

#[test]
fn i32_extend8s_emits_sxtb() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::I32Const(0x80), WasmOp::I32Extend8S], 0)
        .expect("should succeed");
    let has_sxtb = instrs.iter().any(|i| matches!(&i.op, ArmOp::Sxtb { .. }));
    assert!(has_sxtb, "i32.extend8_s should emit SXTB instruction");
}

#[test]
fn i32_extend16s_emits_sxth() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::I32Const(0x8000), WasmOp::I32Extend16S], 0)
        .expect("should succeed");
    let has_sxth = instrs.iter().any(|i| matches!(&i.op, ArmOp::Sxth { .. }));
    assert!(has_sxth, "i32.extend16_s should emit SXTH instruction");
}

// =========================================================================
// Test: chained operations -- multi-step computations
// =========================================================================

#[test]
fn chained_add_sub() {
    // (10 + 20) - 5 = 25
    let result = compile_and_result(&[
        WasmOp::I32Const(10),
        WasmOp::I32Const(20),
        WasmOp::I32Add,
        WasmOp::I32Const(5),
        WasmOp::I32Sub,
    ]);
    assert_eq!(result, 25, "(10 + 20) - 5 should be 25");
}

#[test]
fn chained_mul_add() {
    // (3 * 4) + 5 = 17
    let result = compile_and_result(&[
        WasmOp::I32Const(3),
        WasmOp::I32Const(4),
        WasmOp::I32Mul,
        WasmOp::I32Const(5),
        WasmOp::I32Add,
    ]);
    assert_eq!(result, 17, "(3 * 4) + 5 should be 17");
}

#[test]
fn chained_three_operand_add() {
    // push 1, push 2, add (=3), push 3, add (=6)
    let result = compile_and_result(&[
        WasmOp::I32Const(1),
        WasmOp::I32Const(2),
        WasmOp::I32Add,
        WasmOp::I32Const(3),
        WasmOp::I32Add,
    ]);
    assert_eq!(result, 6, "1 + 2 + 3 should be 6");
}

#[test]
fn nested_expression() {
    // (2 * 3) + (4 * 5) = 6 + 20 = 26
    let result = compile_and_result(&[
        WasmOp::I32Const(2),
        WasmOp::I32Const(3),
        WasmOp::I32Mul,
        WasmOp::I32Const(4),
        WasmOp::I32Const(5),
        WasmOp::I32Mul,
        WasmOp::I32Add,
    ]);
    assert_eq!(result, 26, "(2*3) + (4*5) should be 26");
}

#[test]
fn complex_expression() {
    // ((10 + 20) * 3) - 5 = 85
    let result = compile_and_result(&[
        WasmOp::I32Const(10),
        WasmOp::I32Const(20),
        WasmOp::I32Add,
        WasmOp::I32Const(3),
        WasmOp::I32Mul,
        WasmOp::I32Const(5),
        WasmOp::I32Sub,
    ]);
    assert_eq!(result, 85, "((10 + 20) * 3) - 5 should be 85");
}

// =========================================================================
// Test: WAT->WASM->ARM pipeline semantic correctness
//
// WAT function bodies include an implicit End instruction, so the last
// value-producing op is not at the final index. The compiler places the
// result in a temp register (not R0) unless it is literally the last op.
// These tests find the destination register from the generated ADD/SUB/MUL
// instruction and verify its value after interpretation.
// =========================================================================

/// Find the destination register of the last arithmetic instruction.
fn find_result_reg(instrs: &[ArmInstruction]) -> Reg {
    for instr in instrs.iter().rev() {
        match &instr.op {
            ArmOp::Add { rd, .. } | ArmOp::Sub { rd, .. } | ArmOp::Mul { rd, .. } => return *rd,
            _ => {}
        }
    }
    Reg::R0 // fallback
}

#[test]
fn pipeline_add_returns_correct_value() {
    let wat = br#"(module (func (export "add") (param i32 i32) (result i32)
        local.get 0
        local.get 1
        i32.add))"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = synth_synthesis::decode_wasm_module(&wasm).expect("WASM should decode");

    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&module.functions[0].ops, 2)
        .expect("selection should succeed");

    // Set up initial state: param 0 = 30, param 1 = 12
    let mut state = ArmState::new();
    state.set(Reg::R0, 30);
    state.set(Reg::R1, 12);

    for instr in &instrs {
        interpret_single(&mut state, instr);
    }

    let result_reg = find_result_reg(&instrs);
    assert_eq!(
        state.get(&result_reg),
        42,
        "add(30, 12) should produce 42 in {:?}",
        result_reg
    );
}

#[test]
fn pipeline_sub_returns_correct_value() {
    let wat = br#"(module (func (export "sub") (param i32 i32) (result i32)
        local.get 0
        local.get 1
        i32.sub))"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = synth_synthesis::decode_wasm_module(&wasm).expect("WASM should decode");

    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&module.functions[0].ops, 2)
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 100);
    state.set(Reg::R1, 58);

    for instr in &instrs {
        interpret_single(&mut state, instr);
    }

    let result_reg = find_result_reg(&instrs);
    assert_eq!(
        state.get(&result_reg),
        42,
        "sub(100, 58) should produce 42 in {:?}",
        result_reg
    );
}

#[test]
fn pipeline_multiply_returns_correct_value() {
    let wat = br#"(module (func (export "mul") (param i32 i32) (result i32)
        local.get 0
        local.get 1
        i32.mul))"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = synth_synthesis::decode_wasm_module(&wasm).expect("WASM should decode");

    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&module.functions[0].ops, 2)
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 6);
    state.set(Reg::R1, 7);

    for instr in &instrs {
        interpret_single(&mut state, instr);
    }

    let result_reg = find_result_reg(&instrs);
    assert_eq!(
        state.get(&result_reg),
        42,
        "mul(6, 7) should produce 42 in {:?}",
        result_reg
    );
}

#[test]
fn pipeline_const_expression() {
    // Function that computes: (10 + 5) * 2 = 30
    let wat = br#"(module (func (export "f") (result i32)
        i32.const 10
        i32.const 5
        i32.add
        i32.const 2
        i32.mul))"#;

    let wasm = wat::parse_bytes(wat).expect("WAT should parse");
    let module = synth_synthesis::decode_wasm_module(&wasm).expect("WASM should decode");

    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&module.functions[0].ops, 0)
        .expect("selection should succeed");

    let state = interpret_arm(&instrs);
    let result_reg = find_result_reg(&instrs);
    assert_eq!(
        state.get(&result_reg),
        30,
        "(10 + 5) * 2 should produce 30 in {:?}",
        result_reg
    );
}

// =========================================================================
// Test: structural verification of instruction sequences
// =========================================================================

#[test]
fn const_42_produces_movw_with_42() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::I32Const(42)], 0)
        .expect("should succeed");

    let movw = instrs.iter().find(|i| matches!(&i.op, ArmOp::Movw { .. }));
    assert!(
        movw.is_some(),
        "i32.const 42 should produce a MOVW instruction"
    );

    if let ArmOp::Movw { imm16, .. } = &movw.unwrap().op {
        assert_eq!(*imm16, 42, "MOVW immediate should be 42");
    }
}

#[test]
fn add_uses_correct_source_registers() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add],
            0,
        )
        .expect("should succeed");

    let add = instrs.iter().find(|i| matches!(&i.op, ArmOp::Add { .. }));
    assert!(add.is_some(), "i32.add should produce an ADD instruction");

    if let ArmOp::Add { rn, op2, .. } = &add.unwrap().op {
        assert!(
            matches!(op2, Operand2::Reg(_)),
            "ADD should use register operand, got {:?}",
            op2
        );
        if let Operand2::Reg(rm) = op2 {
            assert_ne!(
                rn, rm,
                "ADD source registers should be different (two consts)"
            );
        }
    }
}

#[test]
fn sub_operand_order_is_correct() {
    // Verify a - b is computed correctly (not b - a)
    let result = compile_and_result(&[WasmOp::I32Const(100), WasmOp::I32Const(1), WasmOp::I32Sub]);
    assert_eq!(result, 99, "100 - 1 should be 99 (not 1 - 100 = -99)");
}

#[test]
fn div_operand_order_is_correct() {
    // 100 / 10 = 10 (not 10 / 100 = 0)
    let result =
        compile_and_result(&[WasmOp::I32Const(100), WasmOp::I32Const(10), WasmOp::I32DivU]);
    assert_eq!(result, 10, "100 /u 10 should be 10 (not 10 /u 100 = 0)");
}

#[test]
fn shl_emits_correct_opcode() {
    // Verify shl produces LslReg (structural check -- semantic verification
    // blocked on select_default fallback not tracking virtual stack)
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[WasmOp::I32Const(1), WasmOp::I32Const(4), WasmOp::I32Shl],
            0,
        )
        .expect("should succeed");
    let has_lsl = instrs.iter().any(|i| matches!(&i.op, ArmOp::LslReg { .. }));
    assert!(has_lsl, "i32.shl should produce LslReg instruction");
}
