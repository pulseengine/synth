//! Regression test: `WasmOp::Call` in the optimized path.
//!
//! History:
//!  * Originally `wasm_to_ir` had no arm for `WasmOp::Call`, so it fell through
//!    to `Opcode::Nop`, the call's result vreg was unmapped, and any downstream
//!    consumer tripped the PR #101 defensive panic (or silently miscompiled by
//!    consuming a stale R0). That was fixed by adding `Opcode::Call` and
//!    lowering it to `BL func_<idx>` in `ir_to_arm`.
//!
//!  * Issue #188: the optimized path's register allocator does NOT model the
//!    AAPCS caller-saved clobber of a `BL` (R0–R3, R12). A function that holds a
//!    param or temp in a caller-saved register across a call therefore reads a
//!    value the callee overwrote — a *confirmed* miscompile (the `g`/`clob`
//!    reproducer). Because correctly modelling call-boundary regalloc in the
//!    optimized path is a deep rework, `ir_to_arm` now **declines** any function
//!    containing a LOCAL call (`func_idx >= num_imports`, returns `Err`). The
//!    backend's existing fallback (`arm_backend::compile_wasm_to_arm`) then
//!    re-lowers the function with the direct `select_with_stack` selector, which
//!    spills/reloads caller-saved registers across calls (see
//!    `instruction_selector::preserve_caller_saved`). Import calls stay on the
//!    optimized path so the #173 field-name relocation rewrite is preserved.
//!
//! These tests pin that contract: the optimized path declines local calls, and
//! the direct selector lowers them to a `BL` while preserving live caller-saved
//! registers.

use synth_synthesis::{ArmOp, InstructionSelector, OptimizerBridge, RuleDatabase, WasmOp};

/// The exact wasm-op sequence emitted by `wat2wasm` for the `fib` function
/// in `examples/wat/simple_add.wat`. Its outer `i32.add` consumes two `call`
/// results.
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
        WasmOp::Call(1), // first recursive call
        WasmOp::LocalGet(0),
        WasmOp::I32Const(2),
        WasmOp::I32Sub,
        WasmOp::Call(1), // second recursive call
        WasmOp::I32Add,  // consumes both call results
        WasmOp::End,
        WasmOp::End,
    ]
}

/// #188: the optimized path must DECLINE a function containing calls so the
/// backend falls back to the direct selector. (Previously it lowered the calls
/// itself without modelling the caller-saved clobber — the miscompile.)
#[test]
fn optimized_path_declines_functions_with_calls() {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge
        .optimize_full(&fib_wasm_ops())
        .expect("optimize_full should succeed for valid input");
    let res = bridge.ir_to_arm(&ir, /* num_params = */ 1);
    assert!(
        res.is_err(),
        "ir_to_arm must decline call-containing functions (#188) so the backend \
         falls back to the direct selector — got Ok"
    );
}

/// The direct selector lowers `Call` to `BL func_<idx>` and (for a function
/// with a param) preserves the param across the call: a `STR`/`LDR` of the
/// caller-saved param register must bracket the `BL`.
#[test]
fn direct_selector_lowers_and_preserves_across_call() {
    let db = RuleDatabase::new();
    let mut selector = InstructionSelector::new(db.rules().to_vec());

    // param0 is live across a call: `drop(call 5); local.get 0` returns param0.
    let ops = vec![WasmOp::Call(5), WasmOp::Drop, WasmOp::LocalGet(0)];
    let arm = selector
        .select_with_stack(&ops, /* num_params = */ 1)
        .expect("direct selector should lower a call-containing function");

    let has_bl_func_5 = arm
        .iter()
        .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "func_5"));
    assert!(has_bl_func_5, "Call(5) must lower to `BL func_5`");

    // #204: param0 is frame-backed — spilled to a stack slot at entry (before
    // the BL), then `local.get 0` reloads it from that SAME slot after the call.
    // The slot, not R0, is what survives the call; the reload target is a temp.
    let bl_pos = arm
        .iter()
        .position(|i| matches!(&i.op, ArmOp::Bl { .. }))
        .expect("a BL must be emitted");
    let spill_slot = arm[..bl_pos]
        .iter()
        .find_map(|i| match &i.op {
            ArmOp::Str {
                rd: synth_synthesis::Reg::R0,
                addr,
            } => Some(addr.clone()),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!("param0 (R0) must be spilled to a frame slot before the BL — got: {arm:#?}")
        });
    let reloaded_from_slot = arm[bl_pos..].iter().any(|i| {
        matches!(&i.op,
            ArmOp::Ldr { addr, .. }
                if addr.base == spill_slot.base
                    && addr.offset == spill_slot.offset
                    && addr.offset_reg == spill_slot.offset_reg)
    });
    assert!(
        reloaded_from_slot,
        "param0 must be reloaded from its frame slot {spill_slot:?} after the BL — got: {arm:#?}"
    );
}
