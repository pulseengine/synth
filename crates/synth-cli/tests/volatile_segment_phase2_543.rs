//! #543 Phase 2 — the optimizer HONORS `--volatile-segment <base>:<len>`:
//! no address-caching optimization fires for a linear-memory access inside a
//! marked DMA-window range.
//!
//! Phase 1 (`volatile_segment_flag_543.rs`) proved the flag parses, threads,
//! and stays byte-INERT on the default configuration. Phase 2 is the codegen
//! back-off itself, locked here as red→green oracles against the two
//! address-caching levers that live on the optimized path:
//!
//!   1. base-CSE / const-address-fold (#468, `SYNTH_BASE_CSE=1`,
//!      `optimizer_bridge::plan_base_cse`): a const-address access whose window
//!      intersects a marked range is EXCLUDED from the fold set — it keeps its
//!      verbatim per-access materialize-and-access codegen — while accesses
//!      outside the range still fold (surgical, per-access back-off). Dynamic
//!      (statically-unknown) addresses were never fold candidates, so they are
//!      always left verbatim — the conservative stance.
//!
//!   2. const-CSE (`SYNTH_CONST_CSE=1`, both the bridge-level cache and
//!      `liveness::apply_const_cse`): declines WHOLESALE while any range is
//!      marked, because at that level a cached constant cannot be classified
//!      address-vs-data — every constant is re-materialized at each occurrence,
//!      the documented volatile contract (conservative v1).
//!
//! Both levers are opt-in env flags, so the DEFAULT pipeline consumes the
//! ranges vacuously: `--volatile-segment` with default env stays byte-inert
//! (the Phase-1 test still passes) and an empty range vector changes nothing by
//! construction (the frozen-codegen anchors still pass).
//!
//! Semantic (results-level) equivalence in both modes is the separate
//! `scripts/repro/volatile_segment_543_differential.py` unicorn-vs-wasmtime
//! oracle — the ranges must preserve RESULTS and only change access patterns.
//!
//! Traceability: rivet `VCR-DMA-001`, gale decision `DD-DMA-REGION-001`.

use object::{Object, ObjectSection};
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// Compile a fixture on the optimized ARM path (self-contained image — the only
/// path where base-CSE and const-CSE live) and return its `.text` bytes.
/// `envs` supplies the opt-in lever flags (e.g. `SYNTH_BASE_CSE=1`), `extra`
/// any additional CLI args (e.g. `--volatile-segment ...`).
fn compile_text(
    fixture_name: &str,
    out_tag: &str,
    envs: &[(&str, &str)],
    extra: &[&str],
) -> Vec<u8> {
    let path = fixture(fixture_name);
    let elf = format!("/tmp/volseg543_p2_{out_tag}.elf");
    let mut args = vec![
        "compile",
        path.to_str().unwrap(),
        "-o",
        &elf,
        "-b",
        "arm",
        "--target",
        "cortex-m4",
        "--all-exports",
    ];
    args.extend_from_slice(extra);
    let mut cmd = Command::new(synth());
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let out = cmd.args(&args).output().expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed (tag={out_tag}): exit={:?} stderr={}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    obj.section_by_name(".text")
        .expect("fixture must have a .text section")
        .data()
        .expect("read .text")
        .to_vec()
}

const FIXTURE: &str = "volatile_segment_543.wat";
const BASE_CSE: (&str, &str) = ("SYNTH_BASE_CSE", "1");

/// The red→green Phase-2 oracle for base-CSE (#468).
///
/// The fixture has 4 const-address stores: 2 inside the DMA window
/// [0x100,0x110), 2 outside. Four compiles pin the whole behavior lattice:
///   C  — no base-CSE, no ranges: the verbatim baseline (per-access
///        `movw/movt R12` base + `add` + store);
///   A  — base-CSE, no ranges: all 4 stores fold (strictly smaller than C —
///        non-vacuity: the optimization genuinely fires on this shape);
///   P  — base-CSE + `--volatile-segment 0x100:16`: the 2 window stores stay
///        verbatim, the 2 outside still fold — strictly between A and C.
///        (On pre-Phase-2 main P==A: the flag was ignored — the RED assertion.)
///   F  — base-CSE + a range covering ALL 4 stores: base-CSE fully declines,
///        byte-identical to C — every store survives verbatim.
#[test]
fn base_cse_honors_volatile_window_543() {
    let c = compile_text(FIXTURE, "baseline", &[], &[]);
    let a = compile_text(FIXTURE, "folded", &[BASE_CSE], &[]);
    let p = compile_text(
        FIXTURE,
        "window",
        &[BASE_CSE],
        &["--volatile-segment", "0x100:16"],
    );
    let f = compile_text(
        FIXTURE,
        "fullcover",
        &[BASE_CSE],
        &["--volatile-segment", "0x80:144"],
    );

    assert!(
        a.len() < c.len(),
        "non-vacuity: base-CSE must fire on this fixture without ranges \
         (folded {} B !< baseline {} B)",
        a.len(),
        c.len()
    );
    assert!(
        a.len() < p.len(),
        "#543 Phase 2 RED CHECK: --volatile-segment 0x100:16 must suppress the \
         folds of the 2 window stores, growing .text over the fully-folded \
         form (window {} B vs folded {} B — equal means the flag is IGNORED)",
        p.len(),
        a.len()
    );
    assert!(
        p.len() < c.len(),
        "surgical back-off: the 2 OUTSIDE stores must still fold under a \
         partial range (window {} B !< baseline {} B)",
        p.len(),
        c.len()
    );
    assert_eq!(
        f, c,
        "full-coverage range must fully decline base-CSE: every store \
         survives verbatim, byte-identical to never enabling SYNTH_BASE_CSE"
    );
}

/// The red→green Phase-2 oracle for const-CSE: any marked range ⇒ wholesale
/// decline (conservative v1 — constants can't be classified address-vs-data),
/// byte-identical to never enabling `SYNTH_CONST_CSE`. Uses the existing
/// const-CSE headroom fixture whose flag-ON reduction is already CI-pinned
/// (`const_cse_reduction_242.rs`).
#[test]
fn const_cse_declines_wholesale_under_volatile_543() {
    const CSE: (&str, &str) = ("SYNTH_CONST_CSE", "1");
    let base = compile_text("const_cse.wat", "cse_baseline", &[], &[]);
    let on = compile_text("const_cse.wat", "cse_on", &[CSE], &[]);
    let on_volatile = compile_text(
        "const_cse.wat",
        "cse_on_volatile",
        &[CSE],
        &["--volatile-segment", "0x100:16"],
    );

    assert!(
        on.len() < base.len(),
        "non-vacuity: const-CSE must fire on the headroom fixture \
         ({} B !< {} B)",
        on.len(),
        base.len()
    );
    assert_eq!(
        on_volatile, base,
        "#543 Phase 2 RED CHECK: with a marked volatile range const-CSE must \
         decline wholesale — byte-identical to SYNTH_CONST_CSE unset (a \
         difference means an aliasing rewrite still fired)"
    );
}

/// Empty-config identity, stated positively: passing NO `--volatile-segment`
/// with the levers ON is unchanged behavior — the gates reduce to the pre-#543
/// path by construction. (The default-env inertness of the flag itself is the
/// Phase-1 `volatile_segment_flag_is_byte_inert_543` test; the flag-off frozen
/// bytes are the `frozen_codegen_bytes.rs` anchors.)
#[test]
fn volatile_gates_are_identity_when_no_range_marked_543() {
    let a1 = compile_text(FIXTURE, "id_a", &[BASE_CSE], &[]);
    let a2 = compile_text(FIXTURE, "id_b", &[BASE_CSE], &[]);
    assert_eq!(a1, a2, "deterministic compile");
}
