//! VCR-MEM-001 (#383) layer-2 substrate — scry shadow-stack-depth proof, in-tree.
//!
//! Proves, in CI against the REAL gust-family module, that synth can obtain a
//! SOUND worst-case shadow-stack budget from scry (`scry-sai-core`, the crates.io
//! library finalized in scry#51 / scry PR #53). First validated on v1.12, then
//! across the SCPV v3 major bump (v2.x); re-verified GREEN on **scry v2.3.0** then
//! **v2.5.0** (2026-06-27) — the consumed surface (`stack_usage.max_stack_bytes`,
//! `function_summaries[].recursive`, `reachable_from_exports`) is unchanged, so
//! the "2.x bump is transparent" claim in `Cargo.toml` is empirically backed, not
//! just asserted. scry v2.4.0/v2.5.0 are behavioral-precision + soundness updates
//! with no API/contract change: v2.4.0 models `memory.size`/`grow` (FEAT-038);
//! v2.5.0 (FEAT-039) makes `reachable_from_exports` sound in the OPEN world — a
//! function reachable only via an ESCAPED funcref (exported table / exported
//! funcref global / passed to an import) is no longer dropped. That value is
//! exactly the "sound superset" synth's layer-1 shadow-stack pruning relies on:
//! under <=2.4.0 such a module could prune a genuinely-reachable function and
//! UNDER-reserve. `scry_reachable_superset_is_open_world_sound_383_feat039` below
//! pins that soundness property in synth's CI (with a closed-world dead-function
//! contrast so it is non-vacuous), so a future scry regression of FEAT-039 reddens
//! synth's gate rather than silently re-introducing the under-reservation. This is
//! the layer-2 "proof the budget is sufficient" half of #383 — the half scry owns:
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

/// VCR-MEM-001 (#383) — pin scry v2.5.0's FEAT-039 open-world soundness fix for
/// the `reachable_from_exports` superset synth's layer-1 shadow-stack pruning
/// consumes. A function reachable ONLY via an escaped funcref (here: present in
/// an EXPORTED funcref table, never called in-module) is host-dispatchable, so it
/// MUST be in the sound superset — under scry <=2.4.0 it was wrongly omitted, and
/// pruning the complement would drop a genuinely-reachable function and
/// UNDER-reserve its shadow stack. Wiring this into synth's CI means a future scry
/// regression of FEAT-039 reddens synth's gate instead of silently re-introducing
/// the under-reservation. The closed-world dead-function contrast keeps the test
/// non-vacuous: it proves the superset still PRUNES (it is not trivially "all").
#[test]
fn scry_reachable_superset_is_open_world_sound_383_feat039() {
    let cfg = || AnalysisConfig {
        widening_threshold: None,
        emit_diagnostics: false,
        taint_policy: None,
    };

    // ESCAPE: func 1 is only in an exported funcref table — never called by the
    // exported `main`. Host code can `call_indirect` it through the table.
    let escaping = wat::parse_str(
        r#"(module
             (table (export "t") 1 funcref)
             (elem (i32.const 0) 1)
             (func (export "main"))
             (func (result i32) i32.const 7))"#,
    )
    .expect("valid wat");
    let r = analyze(escaping, cfg()).expect("scry analyzes the escaping module");
    assert!(
        r.reachable_from_exports.contains(&1),
        "FEAT-039: a function in an EXPORTED funcref table is host-dispatchable ⇒ \
         must be in the sound superset synth prunes against (got {:?}) — under \
         scry <=2.4.0 this was dropped and synth would under-reserve",
        r.reachable_from_exports
    );

    // CONTRAST (non-vacuity): a closed, escape-free module — func 1 is neither
    // exported, called, nor address-taken, so the superset still PRUNES it. If
    // this stopped holding, the superset would be trivially "everything" and the
    // escape assertion above would prove nothing.
    let closed = wat::parse_str(
        r#"(module
             (func (export "main"))
             (func (result i32) i32.const 7))"#,
    )
    .expect("valid wat");
    let r2 = analyze(closed, cfg()).expect("scry analyzes the closed module");
    assert!(
        r2.reachable_from_exports.contains(&0),
        "the exported root is reachable (got {:?})",
        r2.reachable_from_exports
    );
    assert!(
        !r2.reachable_from_exports.contains(&1),
        "a non-exported, uncalled, address-not-taken function MUST be pruned in a \
         closed escape-free module — else the superset is vacuously 'all' (got {:?})",
        r2.reachable_from_exports
    );
}
