//! Regression for the fuzz crash surfaced by the gating harness
//! `wasm_ops_lower_or_error` on PR #113:
//!
//!     FuzzInput { num_params: 1, ops: [I32DivS] }
//!
//! `I32DivS` is a binary operator that needs two values on the wasm stack,
//! but the harness intentionally feeds it with an empty stack to exercise
//! the lowering paths' error-handling. The contract that the harness
//! enforces is *return `Err`, do not panic*. The original failure was a
//! panic somewhere inside the optimized or non-optimized lowering pipeline.
//!
//! This test reproduces the input and asserts that both paths return
//! cleanly (either `Ok` or `Err`), with no panic.

use synth_core::WasmOp;
use synth_synthesis::{InstructionSelector, OptimizerBridge, RuleDatabase};

#[test]
fn i32_divs_with_empty_stack_does_not_panic_optimized_path() {
    let wasm_ops = vec![WasmOp::I32DivS];

    let bridge = OptimizerBridge::new();
    // The pipeline may return Err here — that's the contract. The point is
    // *no panic*. If this regresses we want a structured error, not a crash.
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(&wasm_ops) {
        // If it does succeed, the second stage must also not panic.
        let _arm_ops = bridge.ir_to_arm(&instructions, 1);
    }
}

#[test]
fn i32_divs_with_empty_stack_does_not_panic_non_optimized_path() {
    let wasm_ops = vec![WasmOp::I32DivS];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    // Again: Err is fine, panic is not.
    let _ = selector.select_with_stack(&wasm_ops, 1);
}

/// Same shape as the fuzz harness body — keeps the test close to the
/// actual contract being enforced upstream.
#[test]
fn i32_divs_with_empty_stack_mirrors_fuzz_harness_contract() {
    let wasm_ops = vec![WasmOp::I32DivS];
    let num_params: u32 = 1;

    let bridge = OptimizerBridge::new();
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(&wasm_ops) {
        let _ = bridge.ir_to_arm(&instructions, num_params.min(4) as usize);
    }

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let _ = selector.select_with_stack(&wasm_ops, num_params.min(4));
}

/// Follow-up crash found by the same fuzz harness on this PR's CI run:
///
///     FuzzInput { num_params: 2424832, ops: [Unreachable, I32GeS] }
///
/// The original `Unreachable => Bail` rule in the pre-flight check let
/// the input slip through to `wasm_to_ir`, where I32GeS at stack depth 0
/// produced IR referencing unmapped vregs and tripped the defensive
/// panic. Fixed by modeling `Unreachable` as a stack-neutral op (`pops: 0,
/// pushes: 0`) so the pre-flight catches the subsequent op's underflow.
#[test]
fn unreachable_then_binary_op_does_not_panic_optimized_path() {
    let wasm_ops = vec![WasmOp::Unreachable, WasmOp::I32GeS];

    let bridge = OptimizerBridge::new();
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(&wasm_ops) {
        let _ = bridge.ir_to_arm(&instructions, 4);
    }
}

#[test]
fn unreachable_then_binary_op_does_not_panic_non_optimized_path() {
    let wasm_ops = vec![WasmOp::Unreachable, WasmOp::I32GeS];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let _ = selector.select_with_stack(&wasm_ops, 4);
}

/// Second follow-up crash from the same fuzz harness:
///
///     FuzzInput { num_params: 30736388, ops: [Return, I64Eqz, I32Const(0)] }
///
/// Same shape as the `Unreachable` case — `Return` was also bailing in
/// the pre-flight, letting the I64Eqz reach `wasm_to_ir` with empty
/// stack. Fixed by modeling all wasm terminators (`Return`, `Br`,
/// `BrTable`) as stack-neutral so subsequent ops still get underflow-
/// checked.
#[test]
fn return_then_binary_op_does_not_panic_optimized_path() {
    let wasm_ops = vec![WasmOp::Return, WasmOp::I64Eqz, WasmOp::I32Const(0)];

    let bridge = OptimizerBridge::new();
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(&wasm_ops) {
        let _ = bridge.ir_to_arm(&instructions, 4);
    }
}

#[test]
fn return_then_binary_op_does_not_panic_non_optimized_path() {
    let wasm_ops = vec![WasmOp::Return, WasmOp::I64Eqz, WasmOp::I32Const(0)];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let _ = selector.select_with_stack(&wasm_ops, 4);
}

/// Third follow-up crash — a wasm_to_ir slot-accounting bug, not a pre-
/// flight gap:
///
///     FuzzInput { num_params: ..., ops: [LocalGet(0), Nop, I64ExtendI32U] }
///
/// `wasm_to_ir` uses `inst_id` for both "instruction position" and "vreg
/// slot index". Every wasm op consumed one inst_id slot, including
/// `Nop` (which fell through to the `_ => Opcode::Nop` catch-all).
/// The subsequent `I64ExtendI32U` referenced `inst_id - 1` for its src
/// slot — which was the Nop's unmapped slot, panic.
///
/// Fix: explicit `WasmOp::Nop => continue` arm in wasm_to_ir, BEFORE
/// the catch-all. The catch-all stays as Opcode::Nop (keeps its bug-
/// finder role for unsupported-op back-references — issue #93's class).
#[test]
fn local_get_then_nop_then_extend_does_not_panic_optimized_path() {
    let wasm_ops = vec![WasmOp::LocalGet(0), WasmOp::Nop, WasmOp::I64ExtendI32U];

    let bridge = OptimizerBridge::new();
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(&wasm_ops) {
        let _ = bridge.ir_to_arm(&instructions, 4);
    }
}

#[test]
fn local_get_then_nop_then_extend_does_not_panic_non_optimized_path() {
    let wasm_ops = vec![WasmOp::LocalGet(0), WasmOp::Nop, WasmOp::I64ExtendI32U];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let _ = selector.select_with_stack(&wasm_ops, 4);
}
