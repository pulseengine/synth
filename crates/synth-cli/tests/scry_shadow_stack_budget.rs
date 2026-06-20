//! VCR-MEM-001 (#383) layer-2 substrate — scry shadow-stack-depth proof, in-tree.
//!
//! Proves, in CI against the REAL gust-family module, that synth can obtain a
//! SOUND worst-case shadow-stack budget from scry (`scry-sai-core` v1.12, the
//! crates.io library finalized in scry#51 / scry PR #53). This is the layer-2
//! "proof the budget is sufficient" half of #383 — the half scry owns:
//!
//!   - layer-1 (synth-side): the ELF `.bss` retarget mechanics that consume the
//!     budget — still silicon-gated on gale's `--stack-first` answer.
//!   - layer-2 (scry-side, THIS): `analyze().stack_usage.max_stack_bytes` is the
//!     proven depth; `function_summaries[].recursive` is the honest-fail gate;
//!     `reachable_from_exports` (new in v1.12) prunes provably-dead deep paths.
//!
//! This is the UNWIRED substrate (the VCR-RA "build side-by-side, frozen-safe"
//! pattern): a DEV-dependency exercised only by this test, so the production
//! `synth` binary does not pull scry and no codegen byte changes — the frozen
//! fixtures are bit-identical by construction. When the gated consumption step
//! lands, this call graduates to a feature-gated production dependency.
//!
//! The numbers below are the measurement recorded in VCR-MEM-001: synth reserves
//! 65536 bytes for `msgq_put`'s shadow stack (the full declared page); scry
//! proves the true worst case is 32 bytes — a 2048× over-reservation the layer-1
//! retarget will collapse.

use scry_analyze_core::{AnalysisConfig, StackBound, analyze};

/// Absolute path to a repo fixture (tests run with CWD = the crate dir).
fn fixture(rel: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(rel)
}

#[test]
fn scry_proves_msgq_shadow_stack_budget_383() {
    let bytes = std::fs::read(fixture("scripts/repro/msgq_put_359.wasm"))
        .expect("the #359/#383 gust-family fixture is in-tree");

    let cfg = AnalysisConfig {
        widening_threshold: None,
        emit_diagnostics: false,
        taint_policy: None,
    };
    let r = analyze(bytes, cfg).expect("scry analyzes a valid Core module");

    // (1) PROVEN BUDGET — the layer-1 retarget will reserve this instead of the
    //     full 65536-byte declared page. Bytes(32) is the recorded measurement.
    assert_eq!(
        r.stack_usage.max_stack_bytes,
        StackBound::Bytes(32),
        "scry's proven worst-case shadow-stack depth for msgq_put"
    );

    // (2) HONEST-FAIL GATE — no reachable recursion cycle, so the bound is a real
    //     number (not Unbounded). A recursive module would flip this and synth
    //     would refuse rather than under-reserve.
    assert!(
        !r.function_summaries.iter().any(|s| s.recursive),
        "msgq_put has no reachable recursion → the budget is a finite proof"
    );

    // (3) REACHABILITY (v1.12 FEAT-022) — a sound superset; non-empty here, and
    //     synth may prune any function absent from it. Confirms the dedicated
    //     call exists in the consumed API (it was absent in v1.11).
    assert!(
        !r.reachable_from_exports.is_empty(),
        "reachable_from_exports is the sound superset synth prunes against"
    );
}
