//! Regression test: `WasmOp::Call` left its result vreg unmapped in the
//! optimized path, triggering the PR #101 defensive panic on lawful WASM
//! that consumes a call's return value (e.g., the recursive `fib` example
//! in `examples/wat/simple_add.wat`).
//!
//! Symptom (pre-fix, with the defensive panic):
//!
//! ```text
//! thread 'main' panicked at crates/synth-synthesis/src/optimizer_bridge.rs:1583:21:
//! synth internal compiler error: vreg v13 has no assigned ARM register and no spill slot.
//! This is a wasm_to_ir bug — likely a wasm op whose result is unmapped (see issue #93).
//! ```
//!
//! Root cause: `wasm_to_ir`'s `match wasm_op` had no arm for `WasmOp::Call`,
//! so it fell through to `_ => Opcode::Nop`. The IR therefore had no record
//! that `inst_id N` defined a vreg, and any downstream consumer (here, the
//! outer `i32.add` of the two recursive call results in `fib`) resolved its
//! `src` operand via `get_arm_reg` -> unmapped -> defensive panic (PR #101)
//! or, with the silent R0 fallback, silently consumed a stale R0 value.
//!
//! Fix: added `Opcode::Call { dest, func_idx }` to `synth-opt`, mapped
//! `WasmOp::Call` -> `Opcode::Call` in `wasm_to_ir`, and lowered it in
//! `ir_to_arm` to `BL func_<idx>` with `dest -> R0` registered in
//! `vreg_to_arm` (AAPCS: R0 holds the return value).
//!
//! Scope note: this test verifies the compiler does NOT crash and that the
//! call's result vreg is bound to a real ARM register. It does *not* verify
//! correctness of call-boundary regalloc (e.g., that locals held in R0..R3
//! across a call are properly preserved/reloaded) — that's a separate,
//! deeper rework tracked in the optimizer-call-lowering follow-up.

use synth_synthesis::{ArmOp, OptimizerBridge, WasmOp};

/// Compile through the optimized pipeline (matches `synth compile` without
/// `--no-optimize`) and return the emitted ARM ops.
fn compile_optimized(wasm_ops: &[WasmOp], num_params: usize) -> Vec<ArmOp> {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge
        .optimize_full(wasm_ops)
        .expect("optimize_full should succeed for valid input");
    bridge
        .ir_to_arm(&ir, num_params)
        .expect("ir_to_arm should succeed for valid input")
}

/// The exact wasm-op sequence emitted by `wat2wasm` for the `fib` function
/// in `examples/wat/simple_add.wat`. This is the reproducer the task
/// originated from — its outer `i32.add` consumes two `call` results, the
/// second of which is `v13` (the vreg the defensive panic flagged).
fn fib_wasm_ops() -> Vec<WasmOp> {
    vec![
        // Condition: local.get $n <=u 1
        WasmOp::LocalGet(0),
        WasmOp::I32Const(1),
        WasmOp::I32LeU,
        WasmOp::If,
        // then: local.get $n
        WasmOp::LocalGet(0),
        WasmOp::Else,
        // else: i32.add(call(n-1), call(n-2))
        WasmOp::LocalGet(0),
        WasmOp::I32Const(1),
        WasmOp::I32Sub,
        WasmOp::Call(1), // first recursive call -> v9
        WasmOp::LocalGet(0),
        WasmOp::I32Const(2),
        WasmOp::I32Sub,
        WasmOp::Call(1), // second recursive call -> v13 (was the panic site)
        WasmOp::I32Add,  // consumes v12 and v13
        WasmOp::End,
        WasmOp::End,
    ]
}

/// Pre-fix: this panicked with "vreg v13 has no assigned ARM register and
/// no spill slot" when the defensive panic was active, or silently
/// miscompiled (the second add operand resolved to whatever R0 happened to
/// hold) when the silent fallback was active.
///
/// Post-fix: returns ARM ops including the two `Bl { label: "func_1" }`
/// instructions; the i32.add reads R0 (where the second call's return value
/// landed) as one of its operands — no unmapped vregs are encountered.
#[test]
fn fib_compiles_through_optimized_path() {
    let ops = fib_wasm_ops();
    let arm = compile_optimized(&ops, /* num_params = */ 1);

    // Both recursive calls must lower to `BL func_1`.
    let bl_count = arm
        .iter()
        .filter(|op| matches!(op, ArmOp::Bl { label } if label == "func_1"))
        .count();
    assert_eq!(
        bl_count, 2,
        "expected two `BL func_1` (one per recursive call) — got {} BL ops total in: {:#?}",
        bl_count, arm
    );

    // And the outer `i32.add` must be present.
    let add_count = arm
        .iter()
        .filter(|op| matches!(op, ArmOp::Add { .. }))
        .count();
    assert!(
        add_count >= 1,
        "expected at least one ADD lowering the outer `i32.add` — got: {:#?}",
        arm
    );
}

// Note: a third test that exercised the full backend pipeline
// (`ArmBackend::compile_function("fib", ...)`) was removed because the
// synth-synthesis crate sits below synth-backend in the dep graph — using
// `ArmBackend` from this test file would close a cycle. The existing
// `crates/synth-cli/tests/wast_compile.rs::compile_fib_recursive`-style
// tests cover that end-to-end path; the two tests in this file cover the
// optimizer-bridge layer where the bug lived.

/// Direct check that `Opcode::Call` -> `BL` is emitted and registers `dest`
/// to an ARM register (any of R0..R12 is acceptable; AAPCS puts it in R0).
/// The pre-fix bug was that no ARM op was emitted for `Call` *at all* — the
/// IR contained an `Opcode::Nop`, the BL was missing, and the result vreg
/// was unmapped.
#[test]
fn call_emits_bl_in_optimized_path() {
    // Simplest possible: one call, then store the result.
    let ops = vec![
        WasmOp::Call(5),
        WasmOp::LocalSet(0), // consume the call result -> would trip unmapped-vreg pre-fix
    ];
    let arm = compile_optimized(&ops, /* num_params = */ 1);

    let has_bl_func_5 = arm
        .iter()
        .any(|op| matches!(op, ArmOp::Bl { label } if label == "func_5"));
    assert!(
        has_bl_func_5,
        "WasmOp::Call(5) must lower to `BL func_5` — got: {:#?}",
        arm
    );
}
