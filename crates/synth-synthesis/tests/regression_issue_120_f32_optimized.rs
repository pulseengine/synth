//! Regression test for issue #120 — unmapped-vreg panic on f32 ops in the
//! optimized lowering path.
//!
//! Symptom (pre-fix, with the PR #101 defensive panic active):
//!
//! ```text
//! INFO Compiling function '_ZN17compiler_builtins5float3div3div...E' via backend 'arm'...
//! thread 'main' panicked at crates/synth-synthesis/src/optimizer_bridge.rs:...:
//! synth internal compiler error: vreg v721 has no assigned ARM register and no spill slot.
//! This is a wasm_to_ir bug — likely a wasm op whose result is unmapped (see issue #93).
//! ```
//!
//! Root cause: `OptimizerBridge::wasm_to_ir`'s `match wasm_op` had zero arms
//! for f32/f64 ops, so every float op fell through `_ => Opcode::Nop`. A
//! value-producing float op (e.g. `f32.div`) that emits `Nop` produces no
//! vreg; any downstream consumer of the float result then resolves an
//! unmapped vreg in `ir_to_arm`'s `get_arm_reg` and trips the defensive panic
//! (the #93 silent-drop class, for floats).
//!
//! Fix (issue #120, Option A): the IR `Opcode` enum has no float opcodes, so
//! the optimized path cannot lower floats without a large feature addition.
//! Instead `optimize_full` now detects scalar f32/f64 ops up front and returns
//! a typed `Err(Error::UnsupportedInstruction(...))`. The ARM backend falls
//! back to the non-optimized `InstructionSelector::select_with_stack` path,
//! which handles f32 via VFP/FPU.
//!
//! This test verifies the optimizer-bridge layer (where the bug lived):
//! `optimize_full` declines float modules with a clean `Err` instead of
//! panicking. The end-to-end backend fallback is covered by tests in
//! `crates/synth-backend/src/arm_backend.rs` (synth-synthesis sits below
//! synth-backend in the dep graph, so `ArmBackend` cannot be used here).

use synth_synthesis::{OptimizerBridge, WasmOp};

/// Run a wasm-op sequence through the path that panicked pre-fix:
/// `optimize_full` followed (on success) by `ir_to_arm`. Returns `Ok` if the
/// optimized path accepted the module, `Err` if it cleanly declined it.
/// Must never panic.
fn try_optimized(wasm_ops: &[WasmOp], num_params: usize) -> Result<usize, String> {
    let bridge = OptimizerBridge::new();
    match bridge.optimize_full(wasm_ops) {
        Ok((ir, _cfg, _stats)) => {
            // ir_to_arm is the function that hosts the defensive get_arm_reg
            // panic. Exercising it here proves no unmapped vreg is reached.
            let arm = bridge.ir_to_arm(&ir, num_params);
            Ok(arm.len())
        }
        Err(e) => Err(e.to_string()),
    }
}

/// `f32.div` whose result is consumed by an `f32.store` — the
/// `compiler_builtins float::div` shape from the issue reproducer.
///
/// Pre-fix: `F32Div` and `F32Store` both fell through to `Opcode::Nop`; the
/// store's source vreg was unmapped and `ir_to_arm` panicked.
///
/// Post-fix: `optimize_full` returns `Err` — no panic.
#[test]
fn f32_div_does_not_panic_in_optimized_path() {
    // Stack-balanced: LocalGet(0) is the store address; LocalGet(1)/(2)
    // are the f32.div operands. f32.div pops 2 / pushes 1, then f32.store
    // pops the address + the div result. Depth: 3 -> 2 -> 0. A balanced
    // sequence is required so the pre-flight underflow check passes and
    // the float-decline path (issue #120) is the one exercised.
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::LocalGet(2),
        WasmOp::F32Div,
        WasmOp::F32Store {
            offset: 0,
            align: 2,
        },
    ];

    let result = try_optimized(&ops, /* num_params = */ 3);
    assert!(
        result.is_err(),
        "optimized path must cleanly decline f32.div (issue #120), got Ok: {result:?}"
    );
    let msg = result.unwrap_err();
    assert!(
        msg.contains("float") && msg.contains("120"),
        "error should explain the float limitation and reference issue #120, got: {msg}"
    );
}

/// `f32.div` whose result is the function return value — exercises the
/// value-on-stack-at-end shape.
#[test]
fn f32_div_returned_does_not_panic() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::F32Div,
        WasmOp::End,
    ];

    let result = try_optimized(&ops, 2);
    assert!(
        result.is_err(),
        "optimized path must cleanly decline f32.div return (issue #120), got Ok: {result:?}"
    );
}

/// A representative spread of f32 ops — arithmetic, comparison, math
/// functions, conversions, loads — must each be declined, not panic.
#[test]
fn assorted_f32_ops_are_declined_cleanly() {
    let cases: Vec<Vec<WasmOp>> = vec![
        vec![WasmOp::F32Const(1.5), WasmOp::F32Const(2.5), WasmOp::F32Add],
        vec![WasmOp::F32Const(1.5), WasmOp::F32Const(2.5), WasmOp::F32Mul],
        vec![WasmOp::F32Const(1.5), WasmOp::F32Const(2.5), WasmOp::F32Sub],
        vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Lt],
        vec![WasmOp::LocalGet(0), WasmOp::F32Sqrt],
        vec![WasmOp::LocalGet(0), WasmOp::F32Abs],
        vec![WasmOp::LocalGet(0), WasmOp::F32ConvertI32S],
        vec![WasmOp::LocalGet(0), WasmOp::I32TruncF32S],
        vec![WasmOp::LocalGet(0), WasmOp::I32ReinterpretF32],
        vec![
            WasmOp::LocalGet(0),
            WasmOp::F32Load {
                offset: 0,
                align: 2,
            },
        ],
    ];

    for ops in cases {
        let result = try_optimized(&ops, 2);
        assert!(
            result.is_err(),
            "optimized path must decline f32 ops without panicking, ops={ops:?} got Ok"
        );
    }
}

/// f64 ops — still unsupported in *both* paths, but the optimized path must at
/// least decline them with a typed error rather than panic.
#[test]
fn f64_ops_are_declined_cleanly() {
    let cases: Vec<Vec<WasmOp>> = vec![
        vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F64Div],
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Add],
        vec![WasmOp::LocalGet(0), WasmOp::F64Sqrt],
        vec![WasmOp::LocalGet(0), WasmOp::F64PromoteF32],
    ];

    for ops in cases {
        let result = try_optimized(&ops, 2);
        assert!(
            result.is_err(),
            "optimized path must decline f64 ops without panicking, ops={ops:?} got Ok"
        );
    }
}

/// Sanity guard: a pure integer module must still go through the optimized
/// path unchanged — the float guard must not over-trigger and reject i32 code.
#[test]
fn integer_ops_still_use_optimized_path() {
    let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];
    let result = try_optimized(&ops, 2);
    assert!(
        result.is_ok(),
        "pure i32 module must still optimize, got Err: {result:?}"
    );
}
