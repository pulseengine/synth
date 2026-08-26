//! #1069 (RQ-60-VFPPRESSURE increment 1) — AEABI builtin routing for the
//! i64<->f32 conversion family on SINGLE-precision FPU targets.
//!
//! The reach failure under test: a function whose WASM signature contains NO
//! f64 anywhere (e.g. `(param i64) (result f32)` + `f32.convert_i64_u`) was
//! refused on cortex-m4f/m7 for "needing f64", because the #869 INLINE
//! lowering of the conversion runs on double-precision machinery. The fix
//! routes exactly the six i64/f32-typed family members through the AEABI
//! runtime helpers (`__aeabi_l2f`/`ul2f`, `__aeabi_f2lz`/`f2ulz` — base-AAPCS
//! core-register calls, zero VFP pressure) when the target is single-precision
//! AND the compile is `--relocatable` (the linker resolves the symbols from
//! the embedder's runtime: libgcc / compiler-rt / kiln builtins).
//!
//! Soundness contracts pinned here (the #633/#666/#709/#665/#642 class — the
//! AEABI helpers are MORE-TOTAL than WASM):
//!  * trapping truncs carry the two-bound f32 domain guard (exactly 2 `Udf`)
//!    IN FRONT of the call — NaN/out-of-range traps, the helper never sees
//!    undefined input;
//!  * trunc_sat emits NO `Udf` (§4.3.2 never traps) — saturation/NaN results
//!    are selected inline, the helper only gets in-range values;
//!  * converts are total — no `Udf`;
//!  * the f64-TYPED family members (f64.convert_i64_*, i64.trunc[_sat]_f64_*)
//!    still LOUD-decline by name on single-precision: their WASM types carry
//!    f64, which the hardware genuinely cannot represent;
//!  * non-relocatable single-precision still declines (no linker to resolve
//!    the symbols), and the message now names the `--relocatable` route;
//!  * cortex-m7dp keeps the #869 inline lowering — no `__aeabi_*` call ever
//!    appears there (frozen-anchor safety: shipping m7dp bytes do not move).
//!
//! The execution truth (boundary + trap rows + fuzz vs wasmtime under
//! unicorn, with the builtins provided as spec-exact stubs) lives in
//! `scripts/repro/aeabi_i64_float_1069_differential.py`.

use synth_core::target::FPUPrecision;
use synth_synthesis::rules::ArmOp;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

#[derive(Clone, Copy)]
enum Param {
    I64,
    F32,
    F64,
}

fn lower(
    fpu: Option<FPUPrecision>,
    name: &str,
    relocatable: bool,
    op: WasmOp,
    param: Param,
) -> Result<Vec<ArmOp>, String> {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_target(fpu, name);
    sel.set_relocatable(relocatable);
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

fn udf_count(ops: &[ArmOp]) -> usize {
    ops.iter()
        .filter(|o| matches!(o, ArmOp::Udf { .. }))
        .count()
}

fn bl_targets(ops: &[ArmOp]) -> Vec<String> {
    ops.iter()
        .filter_map(|o| match o {
            ArmOp::Bl { label } => Some(label.clone()),
            _ => None,
        })
        .collect()
}

/// (op, param type, expected builtin, expected Udf count)
fn routed_family() -> Vec<(WasmOp, Param, &'static str, usize)> {
    vec![
        (WasmOp::F32ConvertI64S, Param::I64, "__aeabi_l2f", 0),
        (WasmOp::F32ConvertI64U, Param::I64, "__aeabi_ul2f", 0),
        (WasmOp::I64TruncF32S, Param::F32, "__aeabi_f2lz", 2),
        (WasmOp::I64TruncF32U, Param::F32, "__aeabi_f2ulz", 2),
        (WasmOp::I64TruncSatF32S, Param::F32, "__aeabi_f2lz", 0),
        (WasmOp::I64TruncSatF32U, Param::F32, "__aeabi_f2ulz", 0),
    ]
}

/// The family members whose WASM types genuinely carry f64 — NOT routed.
fn f64_typed_family() -> Vec<(WasmOp, Param)> {
    vec![
        (WasmOp::F64ConvertI64S, Param::I64),
        (WasmOp::F64ConvertI64U, Param::I64),
        (WasmOp::I64TruncF64S, Param::F64),
        (WasmOp::I64TruncF64U, Param::F64),
        (WasmOp::I64TruncSatF64S, Param::F64),
        (WasmOp::I64TruncSatF64U, Param::F64),
    ]
}

// ---------------------------------------------------------------------------
// THE RED-FIRST GATE: single-precision + relocatable now LOWERS the six
// i64/f32-typed members through the named AEABI builtin. RED on pre-#1069
// main (every row declined "requires a double-precision FPU target").
// ---------------------------------------------------------------------------

#[test]
fn m4f_relocatable_routes_all_six_through_named_aeabi_builtins() {
    for (op, param, builtin, udfs_expected) in routed_family() {
        let ops = lower(
            Some(FPUPrecision::Single),
            "cortex-m4f",
            true,
            op.clone(),
            param,
        )
        .unwrap_or_else(|e| {
            panic!("{op:?} must lower on single-precision m4f --relocatable, got decline: {e}")
        });
        let bls = bl_targets(&ops);
        assert_eq!(
            bls,
            vec![builtin.to_string()],
            "{op:?}: exactly one call, to {builtin}, got {bls:?}"
        );
        assert_eq!(
            udf_count(&ops),
            udfs_expected,
            "{op:?}: expected {udfs_expected} Udf trap sites (trapping truncs \
             carry the two-bound guard; converts and trunc_sat never trap)"
        );
        // Zero D-register (f64) machinery: the whole point of the route.
        assert!(
            !ops.iter().any(|o| matches!(
                o,
                ArmOp::F64PromoteF32 { .. }
                    | ArmOp::F64ConvertI32S { .. }
                    | ArmOp::F64ConvertI32U { .. }
                    | ArmOp::F32DemoteF64 { .. }
            )),
            "{op:?}: the AEABI route must not touch f64 machinery on FPv4-SP"
        );
    }
}

// ---------------------------------------------------------------------------
// Capability honesty around the route
// ---------------------------------------------------------------------------

#[test]
fn m4f_non_relocatable_still_declines_and_names_the_route() {
    for (op, param, _, _) in routed_family() {
        let err = lower(
            Some(FPUPrecision::Single),
            "cortex-m4f",
            false,
            op.clone(),
            param,
        )
        .expect_err(&format!(
            "{op:?} must still LOUD-decline on m4f without --relocatable \
             (no linker to resolve __aeabi_*)"
        ));
        assert!(
            err.contains("double-precision"),
            "{op:?}: decline must keep naming the missing capability, got: {err}"
        );
        assert!(
            err.contains("--relocatable"),
            "{op:?}: decline must name the closable gap (the AEABI route \
             one flag away), got: {err}"
        );
    }
}

#[test]
fn f64_typed_members_still_decline_on_m4f_even_relocatable() {
    for (op, param) in f64_typed_family() {
        let err = lower(
            Some(FPUPrecision::Single),
            "cortex-m4f",
            true,
            op.clone(),
            param,
        )
        .expect_err(&format!(
            "{op:?} carries f64 in its WASM type — single-precision must \
             LOUD-decline it, route or no route"
        ));
        assert!(
            err.contains("double-precision") || err.contains("f64"),
            "{op:?}: decline must name the missing capability, got: {err}"
        );
    }
}

#[test]
fn no_fpu_m3_declines_the_whole_family_even_relocatable() {
    for (op, param, _, _) in routed_family() {
        lower(None, "cortex-m3", true, op.clone(), param).expect_err(&format!(
            "{op:?} must LOUD-decline on no-FPU cortex-m3 (the route needs \
             an S-register home for the f32 half)"
        ));
    }
    for (op, param) in f64_typed_family() {
        lower(None, "cortex-m3", true, op.clone(), param)
            .expect_err(&format!("{op:?} must LOUD-decline on no-FPU cortex-m3"));
    }
}

// ---------------------------------------------------------------------------
// m7dp inline path untouched: no __aeabi_* call ever appears there. The
// byte-level frozen anchors gate the full stream; this pins the mechanism.
// ---------------------------------------------------------------------------

#[test]
fn m7dp_keeps_inline_lowering_no_aeabi_calls() {
    for (op, param, _, _) in routed_family() {
        let ops = lower(
            Some(FPUPrecision::Double),
            "cortex-m7dp",
            true,
            op.clone(),
            param,
        )
        .unwrap_or_else(|e| panic!("{op:?} must lower inline on cortex-m7dp: {e}"));
        assert!(
            bl_targets(&ops).is_empty(),
            "{op:?}: m7dp must keep the #869 self-contained inline lowering \
             (no __aeabi_* link obligation there) — found calls {:?}",
            bl_targets(&ops)
        );
    }
}
