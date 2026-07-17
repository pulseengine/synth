//! #782a — trunc_sat (nontrapping saturating float→int) lowering contracts on
//! the ARM32 shipping path (`select_with_stack`, the path falcon's
//! `--relocatable` cortex-m7dp compile takes).
//!
//! WASM §4.3.2 `trunc_sat` is TOTAL: NaN → 0, out-of-range saturates to the
//! integer bound, never traps. ARM `VCVT.{S32,U32}.F32/F64` (round-toward-
//! zero) implements exactly that, so the CORRECT lowering is the bare VCVT —
//! deliberately WITHOUT the #709 domain guard whose whole job is to make the
//! TRAPPING `trunc` forms trap. These tests pin both directions:
//!
//!  * sat forms emit NO `Udf` (a guard would turn saturation into a spurious
//!    trap — a miscompile);
//!  * the trapping twins KEEP their `Udf` guard (the #709 soundness surface
//!    must not be eroded by the new arms);
//!  * the i64-target sat forms LOWER (v0.49 #782 finale) via the sound
//!    branch-free FP word-decompose — trap-free, register-pair result, NO Udf;
//!  * everything f32/f64 honest-rejects without the required FPU (the
//!    f32-source i64 forms promote to f64, so they still decline on a
//!    single-precision target — the double-FPU capability is genuinely absent).
//!
//! The execution truth (boundary table vs wasmtime under unicorn, ARM32 +
//! aarch64 + native) lives in `scripts/repro/trunc_sat_782_differential.py`.

use synth_core::target::FPUPrecision;
use synth_synthesis::rules::ArmOp;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

fn selector(fpu: Option<FPUPrecision>, name: &str) -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_target(fpu, name);
    sel
}

/// Lower `(param <f32|f64>) (result _) op(local.get 0)` on the given target.
fn lower(
    fpu: Option<FPUPrecision>,
    name: &str,
    op: WasmOp,
    param_is_f64: bool,
) -> Result<Vec<ArmOp>, String> {
    let mut sel = selector(fpu, name);
    if param_is_f64 {
        sel.set_params_f64(vec![true]);
    } else {
        sel.set_params_f32(vec![true]);
    }
    let ops = vec![WasmOp::LocalGet(0), op, WasmOp::End];
    sel.select_with_stack(&ops, 1)
        .map(|instrs| instrs.into_iter().map(|i| i.op).collect())
        .map_err(|e| e.to_string())
}

fn has_udf(ops: &[ArmOp]) -> bool {
    ops.iter().any(|o| matches!(o, ArmOp::Udf { .. }))
}

fn has_vcvt_f32(ops: &[ArmOp], signed: bool) -> bool {
    ops.iter().any(|o| {
        if signed {
            matches!(o, ArmOp::I32TruncF32S { .. })
        } else {
            matches!(o, ArmOp::I32TruncF32U { .. })
        }
    })
}

fn has_vcvt_f64(ops: &[ArmOp], signed: bool) -> bool {
    ops.iter().any(|o| {
        if signed {
            matches!(o, ArmOp::I32TruncF64S { .. })
        } else {
            matches!(o, ArmOp::I32TruncF64U { .. })
        }
    })
}

// ---------------------------------------------------------------------------
// sat forms: bare VCVT, NO guard
// ---------------------------------------------------------------------------

#[test]
fn i32_trunc_sat_f32_is_bare_vcvt_no_guard() {
    for (op, signed) in [
        (WasmOp::I32TruncSatF32S, true),
        (WasmOp::I32TruncSatF32U, false),
    ] {
        let ops = lower(Some(FPUPrecision::Single), "cortex-m4f", op.clone(), false)
            .unwrap_or_else(|e| panic!("{op:?} must lower on cortex-m4f: {e}"));
        assert!(
            has_vcvt_f32(&ops, signed),
            "{op:?} must emit the saturating VCVT, got {ops:?}"
        );
        assert!(
            !has_udf(&ops),
            "{op:?} is TOTAL (§4.3.2) — a Udf guard would spuriously trap \
             where WASM saturates: {ops:?}"
        );
    }
}

#[test]
fn i32_trunc_sat_f64_is_bare_vcvt_no_guard() {
    for (op, signed) in [
        (WasmOp::I32TruncSatF64S, true),
        (WasmOp::I32TruncSatF64U, false),
    ] {
        let ops = lower(Some(FPUPrecision::Double), "cortex-m7dp", op.clone(), true)
            .unwrap_or_else(|e| panic!("{op:?} must lower on cortex-m7dp: {e}"));
        assert!(
            has_vcvt_f64(&ops, signed),
            "{op:?} must emit the saturating VCVT.F64, got {ops:?}"
        );
        assert!(!has_udf(&ops), "{op:?} is TOTAL — no Udf guard: {ops:?}");
    }
}

// ---------------------------------------------------------------------------
// the trapping twins KEEP the #709 guard (soundness surface unchanged)
// ---------------------------------------------------------------------------

#[test]
fn trapping_trunc_still_carries_the_709_udf_guard() {
    let f32_ops = lower(
        Some(FPUPrecision::Single),
        "cortex-m4f",
        WasmOp::I32TruncF32S,
        false,
    )
    .expect("trapping trunc_f32_s must still lower");
    assert!(
        has_udf(&f32_ops),
        "i32.trunc_f32_s must KEEP its #709 trap guard: {f32_ops:?}"
    );

    let f64_ops = lower(
        Some(FPUPrecision::Double),
        "cortex-m7dp",
        WasmOp::I32TruncF64S,
        true,
    )
    .expect("trapping trunc_f64_s must still lower");
    assert!(
        has_udf(&f64_ops),
        "i32.trunc_f64_s must KEEP its #709 trap guard: {f64_ops:?}"
    );
}

// ---------------------------------------------------------------------------
// i64-target sat forms: LOWERED on cortex-m7dp (v0.49 #782 finale)
// ---------------------------------------------------------------------------
//
// Honesty-gate FLIP (the v0.46 lesson — moved, not deleted): the i64 forms
// LOUD-declined through v0.48; v0.49 lowers them via the branch-free FP
// word-decompose. This test now pins that they COMPILE, are TRAP-FREE (no Udf —
// §4.3.2 trunc_sat is total), and carry the decompose signature (the saturating
// VCVT.U32.F64 that does the word split, and the I64Sub that realises the
// conditional two's-complement negate / register-pair result).

#[test]
fn i64_trunc_sat_forms_lower_trap_free_on_cortex_m7dp() {
    for (op, is_f64, signed) in [
        (WasmOp::I64TruncSatF32S, false, true),
        (WasmOp::I64TruncSatF32U, false, false),
        (WasmOp::I64TruncSatF64S, true, true),
        (WasmOp::I64TruncSatF64U, true, false),
    ] {
        let ops = lower(
            Some(FPUPrecision::Double),
            "cortex-m7dp",
            op.clone(),
            is_f64,
        )
        .unwrap_or_else(|e| {
            panic!("{op:?} must LOWER on cortex-m7dp (#782 finale), not decline: {e}")
        });
        // §4.3.2 trunc_sat is TOTAL — a Udf guard would spuriously trap.
        assert!(
            !has_udf(&ops),
            "{op:?} is TOTAL (§4.3.2) — the i64 lowering must NEVER trap: {ops:?}"
        );
        // The word decompose uses the saturating VCVT.U32.F64 for both halves
        // (all four forms — unsigned decompose is the shared core).
        assert!(
            ops.iter().any(|o| matches!(o, ArmOp::I32TruncF64U { .. })),
            "{op:?} must decompose via the saturating VCVT.U32.F64: {ops:?}"
        );
        // The SIGNED forms carry the branch-free conditional two's-complement
        // negate (I64Sub of the register pair against the sign mask); the
        // unsigned forms return the raw magnitude and need no I64Sub.
        assert_eq!(
            ops.iter().any(|o| matches!(o, ArmOp::I64Sub { .. })),
            signed,
            "{op:?}: I64Sub presence must match the signed post-processing: {ops:?}"
        );
    }
}

/// The f32-source i64 forms promote to f64, so on a SINGLE-precision target
/// (no double FPU) they still honest-decline — the capability is genuinely
/// absent. (The decline surfaces at ISA validation, not here, but the selector
/// itself declines the f64-source i64 forms on m4f via the double-FPU gate.)
#[test]
fn i64_trunc_sat_f64_source_declines_on_single_precision() {
    for op in [WasmOp::I64TruncSatF64S, WasmOp::I64TruncSatF64U] {
        let err = lower(Some(FPUPrecision::Single), "cortex-m4f", op.clone(), true)
            .expect_err(&format!("{op:?} needs a double FPU — must decline on m4f"));
        assert!(
            err.contains("double-precision") || err.contains("f64") || err.contains("FPU"),
            "{op:?} single-precision decline must name the capability: {err}"
        );
    }
}

// ---------------------------------------------------------------------------
// capability gates: no FPU / single-precision honest-reject
// ---------------------------------------------------------------------------

#[test]
fn trunc_sat_honest_rejects_without_required_fpu() {
    // f32-source sat forms on a no-FPU target (cortex-m3).
    let err = lower(None, "cortex-m3", WasmOp::I32TruncSatF32S, false)
        .expect_err("trunc_sat_f32 must honest-reject on cortex-m3 (no FPU)");
    assert!(
        err.contains("FPU"),
        "no-FPU decline must name the capability: {err}"
    );
    // f64-source sat forms on a single-precision target (cortex-m4f).
    let err = lower(
        Some(FPUPrecision::Single),
        "cortex-m4f",
        WasmOp::I32TruncSatF64S,
        true,
    )
    .expect_err("trunc_sat_f64 must honest-reject on cortex-m4f (single-precision)");
    assert!(
        err.contains("double-precision") || err.contains("f64"),
        "single-precision decline must name the capability: {err}"
    );
}
