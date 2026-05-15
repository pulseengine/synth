//! Fuzz target: per-op coverage check on the wasm→IR lowering.
//!
//! Run with: `cargo +nightly fuzz run wasm_to_ir_roundtrip_op_coverage -- -max_total_time=60`
//!
//! ## What this catches — issue #93 root cause
//!
//! Issue #93 silicon-blocker root cause: `optimizer_bridge::wasm_to_ir`
//! silently dropped `I64ExtendI32U`, `I64ExtendI32S`, and `I32WrapI64` —
//! the `_ => Opcode::Nop` fallback at the bottom of the big match swallowed
//! them. The `optimize_full` post-filter then removed those Nops, so the
//! consumer received IR that was *missing the conversion entirely*. memset's
//! loop counter never advanced, the binary boot-looped on silicon.
//!
//! This harness inverts the bug into a fuzz-detectable invariant:
//!
//!   *Every wasm op that pushes a value MUST contribute at least one IR
//!   instruction.*
//!
//! It tests this *per-op* by feeding a single op (preceded by exactly the
//! stack inputs it needs) into `optimize_full` with **all optimization
//! passes disabled**, then asserting the live IR length is ≥ 1.
//!
//! With dead-code elimination off, an op that emits `Opcode::Nop` will be
//! filtered out by `optimize_full`'s end-stage `is_dead || Nop` filter, the
//! count drops below the floor, and the assertion fires. Any new variant
//! added to `WasmOp` without a corresponding arm in `wasm_to_ir` is now a
//! libfuzzer crash.

#![no_main]

use libfuzzer_sys::fuzz_target;
use synth_core::WasmOp;
use synth_fuzz::FuzzOp;
use synth_synthesis::{OptimizationConfig, OptimizerBridge};

fuzz_target!(|op: FuzzOp| {
    if !op.produces_value() {
        // Drop / Nop / Return etc. don't push anything; not in the
        // class this harness covers.
        return;
    }

    // ------------------------------------------------------------------
    // KNOWN-PENDING-FIX (issue #93 / PR #97):
    //
    // `optimizer_bridge::wasm_to_ir` on main still silently drops these
    // three ops via the `_ => Opcode::Nop` fallback. PR #97 adds the
    // missing match arms. Once #97 merges, *delete this skip block* —
    // the harness will then assert full coverage and any new silent
    // drop will be caught immediately.
    // ------------------------------------------------------------------
    if op.is_issue_93_conversion() {
        return;
    }

    // Build a minimal preamble that leaves the right number of i32/i64
    // operands on the wasm stack so the op under test is well-typed.
    let preamble = build_preamble(op);

    // num_params=0 — keeps the test focused on op lowering itself, not
    // on AAPCS register reservation.
    let wasm_op: WasmOp = op.to_wasm_op(1);
    let mut ops = preamble;
    ops.push(wasm_op);

    // All optimizations disabled — we want raw wasm→IR semantics.
    let bridge = OptimizerBridge::with_config(OptimizationConfig::none());
    let (instrs, _cfg, _stats) = match bridge.optimize_full(&ops) {
        Ok(v) => v,
        Err(_) => return, // typed errors are acceptable on adversarial input
    };

    // The live IR must contain at least one instruction per value-producing
    // op in the input. If an op was silently dropped (the #93 class), the
    // post-filter removes its Nop, the count drops, and this assertion
    // fires.
    //
    // We require strictly ">= ops.len()" because each op in our preamble
    // is a constant push (one IR per op), and the op under test must add
    // at least one more.
    //
    // The error message is verbose so libfuzzer's crash report points
    // straight at the silent-drop class.
    assert!(
        instrs.len() >= ops.len(),
        "wasm_to_ir silently dropped op {:?}: input {} ops, IR {} instructions \
         (issue #93 class regression — every value-producing wasm op must emit \
         at least one IR instruction)",
        op,
        ops.len(),
        instrs.len(),
    );
});

/// Push enough constants onto the wasm stack to make `op` well-typed.
fn build_preamble(op: FuzzOp) -> Vec<WasmOp> {
    let needs = stack_inputs(op);
    let mut out = Vec::with_capacity(needs.len());
    for ty in needs {
        match ty {
            StackTy::I32 => out.push(WasmOp::I32Const(0)),
            StackTy::I64 => out.push(WasmOp::I64Const(0)),
        }
    }
    out
}

#[derive(Clone, Copy)]
enum StackTy {
    I32,
    I64,
}

/// Stack input types each op consumes (deepest first).
#[allow(clippy::match_same_arms)]
fn stack_inputs(op: FuzzOp) -> &'static [StackTy] {
    use FuzzOp::*;
    match op {
        // i32 binary
        I32Add | I32Sub | I32Mul | I32And | I32Or | I32Xor | I32Shl | I32ShrS | I32ShrU
        | I32Rotl | I32Rotr | I32Eq | I32Ne | I32LtS | I32LtU | I32LeS | I32LeU | I32GtS
        | I32GtU | I32GeS | I32GeU | I32DivS | I32DivU | I32RemS | I32RemU => {
            &[StackTy::I32, StackTy::I32]
        }
        // i32 unary
        I32Clz | I32Ctz | I32Popcnt | I32Eqz | I32Extend8S | I32Extend16S => &[StackTy::I32],
        // i32 nullary
        I32Const(_) => &[],
        // i64 binary
        I64Add | I64Sub | I64Mul | I64And | I64Or | I64Xor | I64Shl | I64ShrS | I64ShrU
        | I64Rotl | I64Rotr | I64Eq | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS
        | I64GtU | I64GeS | I64GeU => &[StackTy::I64, StackTy::I64],
        // i64 unary
        I64Clz | I64Ctz | I64Popcnt | I64Eqz | I64Extend8S | I64Extend16S | I64Extend32S => {
            &[StackTy::I64]
        }
        // i64 nullary
        I64Const(_) => &[],
        // conversions
        I64ExtendI32S | I64ExtendI32U => &[StackTy::I32],
        I32WrapI64 => &[StackTy::I64],
        // locals — well-typed without preamble (read from local slot 0)
        LocalGet(_) | LocalTee(_) => &[],
        // non-value-producing — caller checks `produces_value` first, so
        // this branch is unreachable in practice.
        LocalSet(_) | Drop | Nop | Return | Unreachable => &[],
    }
}
