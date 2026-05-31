//! Regression test for issue #93: memset/memcpy/memmove i64-codegen produces
//! non-terminating loop on Cortex-M.
//!
//! Symptom:
//! When `compiler_builtins::memset` is compiled through `synth compile
//! --target cortex-m4f` (the default optimized path), the body of the emitted
//! memset contains a 64-bit shift sequence (`rsb r3,r2,#32; lsl.w r3,r1,r3;
//! lsr.w r0,r0,r2; orr.w r0,r0,r3; lsr.w r1,r1,r2`) where a byte-counter loop
//! should be. On real STM32G474RE silicon the chip enters this loop at
//! `memset+0x4c` and never exits.
//!
//! Root cause:
//! `optimizer_bridge::wasm_to_ir` does NOT handle `WasmOp::I64ExtendI32U` /
//! `WasmOp::I64ExtendI32S`. They fall through the catch-all `_ => Opcode::Nop`,
//! consuming an inst_id slot but never registering the produced i64-pair vregs
//! in `vreg_to_arm`. Subsequent `Opcode::I64ShrU` / `I64Shl` lookups for the
//! shift-count operand miss the map and `get_arm_reg` returns `Reg::R0` as a
//! silent fallback (`optimizer_bridge.rs:1333`). The `I64ShrU` ARM emitter
//! then issues `AND.W R0, R0, #63; SUBS.W R0, R0, #32; ...` — clobbering the
//! first AAPCS parameter (R0, the memset destination pointer / loop pointer).
//! The loop counter / pointer is corrupted on every iteration → non-termination.
//!
//! This test asserts the emission for an `i64.shr_u` whose shift amount comes
//! from `i64.extend_i32_u(local.get $n)` does NOT use R0 as the shift's
//! `rm_lo`/`rm_hi` when the function has 4 AAPCS params (so R0 is reserved).
//!
//! Pre-fix: this assertion fails because the unhandled extend leaves the
//! `Opcode::I64ShrU`'s `src2_lo` / `src2_hi` vregs unmapped, and `ir_to_arm`'s
//! fallback returns R0.
//!
//! Post-fix: `I64ExtendI32U` / `I64ExtendI32S` are handled in `wasm_to_ir`
//! and `ir_to_arm`, so the shift's `rm_lo`/`rm_hi` resolve to the actual
//! register pair the extend wrote into — distinct from any param register.

use synth_synthesis::{ArmOp, InstructionSelector, OptimizerBridge, Reg, WasmOp};

/// Compile the WASM op sequence through the optimized pipeline (the default,
/// matching `synth compile --target cortex-m4f` without `--no-optimize`) and
/// return the emitted ARM ops.
fn compile_optimized(wasm_ops: &[WasmOp], num_params: usize) -> Vec<ArmOp> {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge
        .optimize_full(wasm_ops)
        .expect("optimize_full should succeed for valid input");
    bridge
        .ir_to_arm(&ir, num_params)
        .expect("ir_to_arm should succeed for valid input")
}

/// Returns true if the ARM op is one of the 64-bit shift pseudo-ops (the
/// expansion of which is what corrupts R0 in the bug).
fn is_i64_shift(op: &ArmOp) -> bool {
    matches!(
        op,
        ArmOp::I64Shl { .. } | ArmOp::I64ShrU { .. } | ArmOp::I64ShrS { .. }
    )
}

/// Returns the (rm_lo, rm_hi) of an i64 shift op, or None if not a shift.
fn shift_count_regs(op: &ArmOp) -> Option<(Reg, Reg)> {
    match op {
        ArmOp::I64Shl { rm_lo, rm_hi, .. }
        | ArmOp::I64ShrU { rm_lo, rm_hi, .. }
        | ArmOp::I64ShrS { rm_lo, rm_hi, .. } => Some((*rm_lo, *rm_hi)),
        _ => None,
    }
}

/// Returns the (rn_lo, rn_hi) of an i64 shift op (the value being shifted).
fn shift_value_regs(op: &ArmOp) -> Option<(Reg, Reg)> {
    match op {
        ArmOp::I64Shl { rn_lo, rn_hi, .. }
        | ArmOp::I64ShrU { rn_lo, rn_hi, .. }
        | ArmOp::I64ShrS { rn_lo, rn_hi, .. } => Some((*rn_lo, *rn_hi)),
        _ => None,
    }
}

/// Minimal repro of the broken codegen pattern.
///
/// WASM (4 params; R0..R3 hold them, R0 is memset's destination pointer):
///   ;; build i64 fill word
///   i64.const 0x0101010101010101
///   ;; shift count from a loop-local i32, zero-extended to i64
///   local.get 1                ;; -> R1
///   i64.extend_i32_u           ;; produces an i64 pair on the WASM stack
///   i64.shr_u                  ;; (i64 const) >> (zero-extended i32)
///
/// In the buggy code the I64ShrU's `rm_lo`/`rm_hi` resolve to R0 because the
/// extend was Nopped and the i64 shift count's vregs are unmapped.  The ARM
/// emitter then writes to R0 inside `AND.W R0, R0, #63; SUBS.W R0, R0, #32;
/// ...`, clobbering the AAPCS first-param register.
fn repro_wasm_ops() -> Vec<WasmOp> {
    vec![
        // 4 params (synth's count_params heuristic walks LocalGet indices)
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::LocalGet(2),
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::Drop,
        // i64 fill pattern (the value being shifted)
        WasmOp::I64Const(0x0101_0101_0101_0101),
        // shift amount: take an i32 local and zero-extend to i64
        WasmOp::LocalGet(1),
        WasmOp::I64ExtendI32U,
        // the actual 64-bit logical shift
        WasmOp::I64ShrU,
        WasmOp::Drop,
    ]
}

/// Returns true if any AAPCS parameter register (R0..R3) is the i64 shift's
/// `rm_lo` or `rm_hi` — both of which the ARM emitter clobbers as scratch.
fn shift_clobbers_param_reg(arm_ops: &[ArmOp]) -> bool {
    for op in arm_ops {
        if let Some((rm_lo, rm_hi)) = shift_count_regs(op) {
            for reg in [rm_lo, rm_hi] {
                if matches!(reg, Reg::R0 | Reg::R1 | Reg::R2 | Reg::R3) {
                    return true;
                }
            }
        }
    }
    false
}

/// Sanity check: the no-optimize path (select_with_stack) handles the same
/// repro correctly — its output's i64 shift `rm_lo`/`rm_hi` do not alias an
/// AAPCS param register. This shows the bug is specific to the optimizer
/// path.
#[test]
fn issue_93_no_optimize_path_handles_repro() {
    let wasm = repro_wasm_ops();
    let mut sel = InstructionSelector::new(vec![]);
    let arm: Vec<_> = sel
        .select_with_stack(&wasm, 4)
        .expect("no-optimize path should compile the repro")
        .into_iter()
        .map(|i| i.op)
        .collect();
    assert!(arm.iter().any(|o| matches!(o, ArmOp::I64ShrU { .. })));
    // This repro is call-free, so params stay register-backed (frame-backing is
    // reserved for call-containing functions, #204). The no-optimize path's i64
    // shift count must therefore not alias an AAPCS param register the emitter
    // clobbers as scratch.
    assert!(
        !shift_clobbers_param_reg(&arm),
        "no-optimize path also clobbers AAPCS params (unexpected): {:#?}",
        arm.iter().filter(|o| is_i64_shift(o)).collect::<Vec<_>>()
    );
}

#[test]
fn issue_93_optimized_i64_shr_u_does_not_use_r0_as_shift_count() {
    // 4-param function — R0..R3 are all live AAPCS params on entry.
    // The i64.shr_u's shift count must NOT map to any of R0..R3.
    let wasm = repro_wasm_ops();
    let arm = compile_optimized(&wasm, 4);

    // Make sure the op we care about was actually emitted.
    let n_shifts = arm.iter().filter(|o| is_i64_shift(o)).count();
    assert!(
        n_shifts >= 1,
        "expected at least one I64ShrU in optimized output; got: {:#?}",
        arm
    );

    // The shift count regs (rm_lo, rm_hi) are clobbered by the emitter.
    // They must not alias an AAPCS param register, otherwise the param is
    // destroyed on every shift (e.g. the memset loop pointer in R0).
    assert!(
        !shift_clobbers_param_reg(&arm),
        "I64 shift's rm_lo/rm_hi (clobbered by the emitter) aliases an AAPCS \
         param register R0..R3 — would corrupt the parameter on every shift. \
         Shift ops: {:#?}",
        arm.iter().filter(|o| is_i64_shift(o)).collect::<Vec<_>>()
    );
}

#[test]
fn issue_93_optimized_i64_shr_u_value_and_count_are_distinct() {
    // The i64-being-shifted (rn_lo:rn_hi) and the i64 shift count
    // (rm_lo:rm_hi) must occupy disjoint registers — otherwise the AND/SUBS
    // on rm_lo would corrupt the value, and the LSR on rn_lo would no longer
    // see the original. This also pre-empts the `R0 fallback` regression
    // from being silently masked by happening to alias the value's regs.
    let wasm = repro_wasm_ops();
    let arm = compile_optimized(&wasm, 4);

    for op in &arm {
        if let (Some((rn_lo, rn_hi)), Some((rm_lo, rm_hi))) =
            (shift_value_regs(op), shift_count_regs(op))
        {
            assert_ne!(rn_lo, rm_lo, "rn_lo aliases rm_lo (clobbers value)");
            assert_ne!(rn_lo, rm_hi, "rn_lo aliases rm_hi (clobbers value)");
            assert_ne!(rn_hi, rm_lo, "rn_hi aliases rm_lo (clobbers value)");
            assert_ne!(rn_hi, rm_hi, "rn_hi aliases rm_hi (clobbers value)");
        }
    }
}

#[test]
fn issue_93_optimized_i64_shl_does_not_use_r0_as_shift_count() {
    // Same scenario, but using i64.shl instead of i64.shr_u — the shl
    // emitter has the same clobber pattern on rm_lo/rm_hi.
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::LocalGet(2),
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::I64Const(0x0101_0101_0101_0101),
        WasmOp::LocalGet(2),
        WasmOp::I64ExtendI32U,
        WasmOp::I64Shl,
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert!(
        arm.iter().any(|o| matches!(o, ArmOp::I64Shl { .. })),
        "expected an I64Shl in the output: {:#?}",
        arm
    );
    assert!(
        !shift_clobbers_param_reg(&arm),
        "I64Shl's rm_lo/rm_hi aliases an AAPCS param register: {:#?}",
        arm
    );
}

#[test]
fn issue_93_optimized_i64_shr_s_does_not_use_r0_as_shift_count() {
    // Same scenario for the arithmetic right shift.
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::LocalGet(2),
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::I64Const(-1),
        WasmOp::LocalGet(3),
        WasmOp::I64ExtendI32S,
        WasmOp::I64ShrS,
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert!(
        arm.iter().any(|o| matches!(o, ArmOp::I64ShrS { .. })),
        "expected an I64ShrS in the output: {:#?}",
        arm
    );
    assert!(
        !shift_clobbers_param_reg(&arm),
        "I64ShrS's rm_lo/rm_hi aliases an AAPCS param register: {:#?}",
        arm
    );
}
