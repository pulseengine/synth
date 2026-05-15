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
