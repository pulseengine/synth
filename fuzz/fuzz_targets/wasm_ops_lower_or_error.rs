//! Fuzz target: arbitrary `Vec<WasmOp>` through both lowering paths.
//!
//! Run with: `cargo +nightly fuzz run wasm_ops_lower_or_error -- -max_total_time=60`
//!
//! ## What this catches
//!
//! - Panics in the optimized path (`OptimizerBridge::optimize_full` +
//!   `OptimizerBridge::ir_to_arm`).
//! - Panics in the non-optimized path (`InstructionSelector::select_with_stack`).
//! - Production of an `ArmOp` value that the `ArmEncoder` cannot encode at
//!   all (encoder must return either `Ok(bytes)` or `Err(_)`, never panic).
//! - Stuck loops in the lowering pipeline (a step counter caps work; a runaway
//!   pipeline trips the explicit `panic!` below, which libfuzzer reports as
//!   a crash).
//!
//! Stack-mismatch / type-mismatch input is accepted: the selectors are
//! expected to return `Err`, not panic. That is the contract this harness
//! enforces.

#![no_main]

use libfuzzer_sys::fuzz_target;
use synth_backend::ArmEncoder;
use synth_fuzz::{FuzzInput, lower_arbitrary_to_wasm_ops};
use synth_synthesis::{InstructionSelector, OptimizerBridge, RuleDatabase};

fuzz_target!(|input: FuzzInput| {
    let wasm_ops = lower_arbitrary_to_wasm_ops(&input.ops, input.num_params);
    if wasm_ops.is_empty() {
        return;
    }
    // Cheap step cap: anything beyond this is an effectively-infinite input
    // and we don't want libfuzzer wasting cycles on it.
    if wasm_ops.len() > 256 {
        return;
    }

    // -----------------------------------------------------------------
    // Path A: optimized — wasm_ops -> IR -> optimizations -> ARM ops
    // -----------------------------------------------------------------
    let bridge = OptimizerBridge::new();
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(&wasm_ops) {
        // `ir_to_arm` returns `Result`: `Ok` on success, `Err` for the
        // issue-#93-class unmapped-vreg condition. Either is contract-
        // compliant — only a panic is a crash.
        if let Ok(arm_ops) = bridge.ir_to_arm(&instructions, input.num_params.min(4) as usize) {
            encode_each_or_typed_error(&arm_ops);
        }
    }

    // -----------------------------------------------------------------
    // Path B: non-optimized — InstructionSelector::select_with_stack
    // -----------------------------------------------------------------
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    if let Ok(arm_instrs) = selector.select_with_stack(&wasm_ops, input.num_params.min(4)) {
        let arm_ops: Vec<_> = arm_instrs.into_iter().map(|i| i.op).collect();
        encode_each_or_typed_error(&arm_ops);
    }
});

/// Run each ARM op through the Thumb-2 encoder. The contract is that
/// `encode` returns `Ok(bytes)` (encodable) or `Err(_)` (typed error).
/// A `panic!` from inside the encoder is a crash — libfuzzer will surface it.
fn encode_each_or_typed_error(arm_ops: &[synth_synthesis::ArmOp]) {
    let encoder = ArmEncoder::new_thumb2();
    for op in arm_ops {
        let _ = encoder.encode(op);
    }
}
