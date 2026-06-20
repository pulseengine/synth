//! VCR-RA-010 path-A substrate — scry's constant-rematerialization signal, in-tree.
//!
//! Locks, as a regression-guarded in-tree test, the capability the VCR-RA-010
//! "untrusted regalloc oracle" (path A) will consume: scry's interval domain
//! identifies locals with a SINGLETON interval `[c, c]` = a provably-constant
//! value, which the register allocator can REMATERIALIZE (re-emit the constant
//! at the use) instead of spilling/reloading. That is exactly the
//! const-materialization waste gale measured on the hot path (#390 pass-5, the
//! `#0x7e`/`#0x7f` clamps; #209 const-CSE).
//!
//! This is the UNWIRED substrate (the VCR-RA "build side-by-side, frozen-safe"
//! pattern): a DEV-dependency exercised only by this test — the production
//! `synth` binary does not pull scry, no codegen changes, the frozen fixtures
//! are bit-identical by construction. When the regalloc wiring becomes the
//! active increment, this signal feeds remat candidate selection (a HINT only;
//! VCR-RA-003 re-validates, so nothing scry asserts enters the TCB).
//!
//! MEASURED 2026-06-20 (recorded in VCR-RA-010): on the hot kernels, singleton
//! (known-constant) locals were flight_seam_flat 44/70, control_step 6/24,
//! controller_step 6/20 — strong signal exactly where the const-materialization
//! waste lives. Thresholds below are conservative (well under the measured
//! values) so the test asserts "substantial const-remat signal exists" without
//! being brittle to scry precision changes across versions.

use scry_analyze_core::{AbstractValue, AnalysisConfig, analyze};

fn fixture(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

/// Count locals scry proves are a single constant (`I32`/`I64` singleton
/// interval) across all program points — the rematerialization candidates.
fn const_local_count(wasm_rel: &str) -> usize {
    let bytes = std::fs::read(fixture(wasm_rel)).expect("fixture in-tree");
    let cfg = AnalysisConfig {
        widening_threshold: None,
        emit_diagnostics: false,
        taint_policy: None,
    };
    let r = analyze(bytes, cfg).expect("scry analyzes a valid Core module");
    r.invariants
        .points
        .iter()
        .flat_map(|p| &p.locals)
        .filter(|l| match &l.value {
            AbstractValue::I32Interval(iv) | AbstractValue::I64Interval(iv) => iv.lo == iv.hi,
            _ => false,
        })
        .count()
}

#[test]
fn scry_finds_const_remat_signal_on_hot_kernels_ra010() {
    // flight_seam_flat — the #209/#390 const-materialization hot kernel.
    // Measured 44 singleton-interval locals; assert substantial signal exists.
    let flight = const_local_count("scripts/repro/flight_seam_flat.wasm");
    assert!(
        flight >= 20,
        "scry should surface substantial const-remat signal on flight_seam_flat \
         (measured 44 singleton-interval locals); got {flight}"
    );

    // control_step (the 0x00210A55 fixture's source wasm) — measured 6.
    let control = const_local_count("scripts/repro/control_step.wasm");
    assert!(
        control >= 3,
        "scry should surface const-remat signal on control_step \
         (measured 6 singleton-interval locals); got {control}"
    );
}
