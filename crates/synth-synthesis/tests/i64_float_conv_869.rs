//! #869 — the ARM 64-bit integer<->float conversion family lowering contracts
//! on the shipping path (`select_with_stack`, the path falcon's
//! `--relocatable` cortex-m7dp compile takes).
//!
//!  * the four CONVERTS (`f32/f64.convert_i64_{s,u}`) are TOTAL — they lower
//!    on m7dp with NO `Udf` (a guard would be a spurious trap);
//!  * the four TRAPPING truncations (`i64.trunc_f32/f64_{s,u}`) carry the
//!    #709-class i64 domain guard: exactly two `Udf` trap sites (upper +
//!    lower bound; NaN falls out of the first ordered compare) in front of
//!    the #782 word-decompose;
//!  * the nontrapping `i64.trunc_sat_*` twins still emit NO `Udf` (the new
//!    guard must not leak into the saturating forms);
//!  * every family member LOUD-declines on a single-precision target
//!    (m4f/m7 — the lowerings run on f64 machinery, undefined on FPv4-SP)
//!    and on a no-FPU target (m3).
//!
//! The execution truth (boundary + trap rows + double-rounding killers +
//! fuzz vs wasmtime under unicorn) lives in
//! `scripts/repro/i64_float_conv_869_differential.py`.

use synth_core::target::FPUPrecision;
use synth_synthesis::rules::ArmOp;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

fn selector(fpu: Option<FPUPrecision>, name: &str) -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_target(fpu, name);
    sel
}

/// Lower `(param <ty>) (result _) op(local.get 0)` on the given target.
fn lower(
    fpu: Option<FPUPrecision>,
    name: &str,
    op: WasmOp,
    param: Param,
) -> Result<Vec<ArmOp>, String> {
    let mut sel = selector(fpu, name);
    match param {
        Param::I64 => sel.set_params_i64(vec![true]),
        Param::F32 => sel.set_params_f32(vec![true]),
        Param::F64 => sel.set_params_f64(vec![true]),
    }
    let ops = vec![WasmOp::LocalGet(0), op, WasmOp::End];
    sel.select_with_stack(&ops, 1)
        .map(|instrs| instrs.into_iter().map(|i| i.op).collect())
        .map_err(|e| e.to_string())
}

#[derive(Clone, Copy)]
enum Param {
    I64,
    F32,
    F64,
}

fn udf_count(ops: &[ArmOp]) -> usize {
    ops.iter()
        .filter(|o| matches!(o, ArmOp::Udf { .. }))
        .count()
}

fn family() -> Vec<(WasmOp, Param, bool)> {
    // (op, param type, is_trapping_trunc)
    vec![
        (WasmOp::F32ConvertI64S, Param::I64, false),
        (WasmOp::F32ConvertI64U, Param::I64, false),
        (WasmOp::F64ConvertI64S, Param::I64, false),
        (WasmOp::F64ConvertI64U, Param::I64, false),
        (WasmOp::I64TruncF32S, Param::F32, true),
        (WasmOp::I64TruncF32U, Param::F32, true),
        (WasmOp::I64TruncF64S, Param::F64, true),
        (WasmOp::I64TruncF64U, Param::F64, true),
    ]
}

// ---------------------------------------------------------------------------
// m7dp (double-precision): all eight lower; guard geometry pinned
// ---------------------------------------------------------------------------

#[test]
fn m7dp_lowers_all_eight_converts_guardfree_truncs_double_guarded() {
    for (op, param, trapping) in family() {
        let ops = lower(Some(FPUPrecision::Double), "cortex-m7dp", op.clone(), param)
            .unwrap_or_else(|e| panic!("{op:?} must lower on cortex-m7dp, got decline: {e}"));
        let udfs = udf_count(&ops);
        if trapping {
            assert_eq!(
                udfs, 2,
                "{op:?}: the trapping trunc must carry exactly the two-bound \
                 #709-class domain guard (upper + lower UDF), found {udfs}"
            );
        } else {
            assert_eq!(
                udfs, 0,
                "{op:?}: converts are TOTAL — a Udf is a spurious trap"
            );
        }
    }
}

#[test]
fn m7dp_trunc_sat_twins_stay_guard_free() {
    // The #869 guard must not leak into the NONTRAPPING saturating forms.
    for (op, param) in [
        (WasmOp::I64TruncSatF32S, Param::F32),
        (WasmOp::I64TruncSatF32U, Param::F32),
        (WasmOp::I64TruncSatF64S, Param::F64),
        (WasmOp::I64TruncSatF64U, Param::F64),
    ] {
        let ops = lower(Some(FPUPrecision::Double), "cortex-m7dp", op.clone(), param)
            .unwrap_or_else(|e| panic!("{op:?} must lower on cortex-m7dp: {e}"));
        assert_eq!(
            udf_count(&ops),
            0,
            "{op:?}: trunc_sat NEVER traps (§4.3.2) — a Udf is a miscompile"
        );
    }
}

#[test]
fn m7dp_f32_convert_carries_round_to_odd_fixup_and_single_demote() {
    // The f32 converts must go through the f64 build + demote (one
    // VCVT.F32.F64) — and the fixup's 64-bit increment must be the MODELED
    // Adds/Adc pair, never the reg_effect-None I64Add pseudo-op (the
    // range-realloc segment-liveness hazard caught at land time).
    for op in [WasmOp::F32ConvertI64S, WasmOp::F32ConvertI64U] {
        let ops = lower(
            Some(FPUPrecision::Double),
            "cortex-m7dp",
            op.clone(),
            Param::I64,
        )
        .unwrap();
        let demotes = ops
            .iter()
            .filter(|o| matches!(o, ArmOp::F32DemoteF64 { .. }))
            .count();
        assert_eq!(demotes, 1, "{op:?}: exactly one final demote rounding");
        assert!(
            !ops.iter().any(|o| matches!(o, ArmOp::I64Add { .. })),
            "{op:?}: the fixup increment must be modeled Adds/Adc, not the \
             I64Add pseudo-op (realloc segment-liveness hazard)"
        );
        assert!(
            ops.iter().any(|o| matches!(o, ArmOp::Adds { .. }))
                && ops.iter().any(|o| matches!(o, ArmOp::Adc { .. })),
            "{op:?}: missing the Adds/Adc round-to-odd increment"
        );
    }
}

// ---------------------------------------------------------------------------
// capability honesty: single-precision and no-FPU targets decline loudly
// ---------------------------------------------------------------------------

#[test]
fn single_precision_m4f_declines_every_family_member() {
    for (op, param, _) in family() {
        let err = lower(Some(FPUPrecision::Single), "cortex-m4f", op.clone(), param).expect_err(
            &format!("{op:?} must LOUD-decline on single-precision m4f (f64 machinery)"),
        );
        assert!(
            err.contains("double-precision"),
            "{op:?}: decline must name the missing capability, got: {err}"
        );
    }
}

#[test]
fn no_fpu_m3_declines_every_family_member() {
    for (op, param, _) in family() {
        lower(None, "cortex-m3", op.clone(), param)
            .expect_err(&format!("{op:?} must LOUD-decline on no-FPU cortex-m3"));
    }
}
