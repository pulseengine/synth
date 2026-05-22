//! Regression: `OptimizerBridge::ir_to_arm` must never panic.
//!
//! `ir_to_arm` hosts the `get_arm_reg` closure that maps an IR virtual
//! register to an ARM register. PR #101 made an unmapped vreg a hard
//! `panic!` ("synth internal compiler error: vreg vN has no assigned ARM
//! register ...") — correct at the time (a loud crash beats a silent
//! miscompilation), but it meant the optimized lowering path
//! (`optimize_full` -> `ir_to_arm`) could panic on malformed input.
//!
//! That panic was the last panic site in the optimized path and the reason
//! the `wasm_ops_lower_or_error` fuzz harness sat at `gating: false`. The
//! fix converts `get_arm_reg`'s `panic!` into `Err(Error::synthesis(...))`
//! with the same diagnostic text, and `ir_to_arm` now returns
//! `Result<Vec<ArmOp>>`. The defensive check is preserved — a genuine
//! `wasm_to_ir` bug still surfaces as a rich `Err`, it just no longer kills
//! the process.
//!
//! Contract enforced here: feeding a malformed `Vec<WasmOp>` through
//! `optimize_full` + `ir_to_arm` yields `Ok` or `Err`, never a panic.

use synth_core::WasmOp;
use synth_synthesis::OptimizerBridge;

/// Drive the full optimized pipeline. The `optimize_full` pre-flight
/// (`wasm_stack_check`) may reject the input as `Err`; if it accepts,
/// `ir_to_arm` runs and itself returns `Result`. Neither stage may panic.
fn lower_optimized(wasm_ops: &[WasmOp], num_params: usize) {
    let bridge = OptimizerBridge::new();
    if let Ok((instructions, _cfg, _stats)) = bridge.optimize_full(wasm_ops) {
        // The point of the test: this returns `Ok` or `Err`, never panics.
        // `ir_to_arm` is the function that previously hosted the
        // process-killing `get_arm_reg` panic.
        match bridge.ir_to_arm(&instructions, num_params) {
            Ok(_arm) => {}
            Err(_e) => {}
        }
    }
}

/// The motivating shape: `[I32Const, LocalGet, I32Const, I32Add, I32ShrS,
/// I32Const]`. A mixed arithmetic / shift sequence with a trailing constant
/// that historically could leave a vreg unmapped by the time `ir_to_arm`
/// runs.
#[test]
fn mixed_i32_arith_shift_sequence_does_not_panic() {
    let wasm_ops = vec![
        WasmOp::I32Const(7),
        WasmOp::LocalGet(0),
        WasmOp::I32Const(3),
        WasmOp::I32Add,
        WasmOp::I32ShrS,
        WasmOp::I32Const(1),
    ];
    lower_optimized(&wasm_ops, 4);
}

/// Type-mismatched i64 sequence: an i64 op consuming i32-shaped stack
/// slots. The kind of shape that, pre-fix, could produce IR referencing a
/// vreg `wasm_to_ir` never mapped, tripping `get_arm_reg`'s panic.
#[test]
fn type_mismatched_i64_sequence_does_not_panic() {
    let wasm_ops = vec![
        WasmOp::I32Const(1),
        WasmOp::I32Const(2),
        WasmOp::I64Add,
        WasmOp::I64ShrU,
    ];
    lower_optimized(&wasm_ops, 4);
}

/// An i64 extend feeding an i64 shift — issue-#93's exact class. With the
/// extend handled in `wasm_to_ir` this lowers cleanly, but the harness
/// contract holds regardless: `Ok` or `Err`, never a panic.
#[test]
fn i64_extend_into_shift_does_not_panic() {
    let wasm_ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::I64ExtendI32U,
        WasmOp::I32Const(32),
        WasmOp::I64ShrU,
    ];
    lower_optimized(&wasm_ops, 4);
}

/// Confirms the new `Result` signature on a normal, well-formed program:
/// `ir_to_arm` returns `Ok` with a non-empty instruction stream. This is
/// the happy-path guard — if the `Result` conversion broke ordinary
/// lowering, this fails.
#[test]
fn well_formed_program_lowers_to_ok() {
    let wasm_ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];

    let bridge = OptimizerBridge::new();
    let (instructions, _cfg, _stats) = bridge
        .optimize_full(&wasm_ops)
        .expect("well-formed program optimizes");
    let arm = bridge
        .ir_to_arm(&instructions, 2)
        .expect("well-formed program lowers to ARM");
    assert!(
        !arm.is_empty(),
        "a non-trivial program should emit at least one ARM op"
    );
}

/// Exercise `ir_to_arm` directly with a hand-built IR instruction whose
/// source vreg has no producer — the exact unmapped-vreg condition the
/// `get_arm_reg` check guards. Pre-fix this panicked; post-fix it must be
/// a typed `Err` carrying the issue-#93 diagnostic.
#[test]
fn unmapped_vreg_yields_err_not_panic() {
    use synth_opt::{Instruction, Opcode, Reg as OptReg};

    let bridge = OptimizerBridge::new();
    // A single i32 add whose operands (v100, v101) were never produced by
    // any prior instruction — so `vreg_to_arm` has no mapping and there is
    // no spill slot. This is precisely the state a `wasm_to_ir` gap leaves
    // behind, and the state `get_arm_reg`'s defensive check exists to
    // catch.
    let instrs = vec![Instruction {
        id: 0,
        opcode: Opcode::Add {
            dest: OptReg(0),
            src1: OptReg(100),
            src2: OptReg(101),
        },
        block_id: 0,
        is_dead: false,
    }];

    // The contract: a typed `Err`, never a panic. v100 / v101 have no
    // producer and no spill slot, so `get_arm_reg` must take its defensive
    // branch — pre-fix that was a `panic!`, post-fix a recoverable `Err`.
    let result = bridge.ir_to_arm(&instrs, 0);
    let err = result.expect_err("unmapped src vregs must yield Err, not Ok or panic");
    let msg = err.to_string();
    // The diagnostic must survive the panic -> Err conversion: it is still
    // the issue-#93-class bug-finder, just no longer process-killing.
    assert!(
        msg.contains("no assigned") && msg.contains("issue #93"),
        "unmapped-vreg error lost its diagnostic content: {msg}"
    );
}
