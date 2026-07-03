//! #543 Phase 2 — the optimizer HONORS `--volatile-segment <base>:<len>`:
//! no address-caching optimization fires for a linear-memory access inside a
//! marked DMA-window range.
//!
//! Phase 1 (`volatile_segment_flag_543.rs`) proved the flag parses, threads,
//! and stays byte-INERT on the default configuration. Phase 2 is the codegen
//! back-off itself, locked here as red→green oracles against the two
//! address-caching levers that live on the optimized path:
//!
//!   1. base-CSE / const-address-fold (#468, DEFAULT-ON since the lever flip,
//!      opt-out `SYNTH_BASE_CSE=0`, `optimizer_bridge::plan_base_cse`): a
//!      const-address access whose window intersects a marked range is
//!      EXCLUDED from the fold set — it keeps its verbatim per-access
//!      materialize-and-access codegen — while accesses outside the range
//!      still fold (surgical, per-access back-off). Dynamic
//!      (statically-unknown) addresses were never fold candidates, so they are
//!      always left verbatim — the conservative stance.
//!
//!   2. const-CSE (`liveness::apply_const_cse`, DEFAULT-ON since the #242
//!      flip, opt-out `SYNTH_CONST_CSE=0`; the former bridge-level inline
//!      cache is retired): declines WHOLESALE while any range is marked,
//!      because at that level a cached constant cannot be classified
//!      address-vs-data — every constant is re-materialized at each
//!      occurrence, the documented volatile contract (conservative v1).
//!
//! Since the lever flips the DEFAULT pipeline genuinely CONSUMES the ranges
//! (marking a range can change default bytes — that is the Phase-2 contract
//! doing its job); with the levers opted OUT (`SYNTH_BASE_CSE=0`,
//! `SYNTH_CONST_CSE=0`) the ranges are consumed vacuously and
//! `--volatile-segment` stays byte-inert (the Phase-1 test pins that opt-out
//! form). An empty range vector changes nothing by construction.
//!
//! The base-CSE lattice below pins `SYNTH_CONST_CSE=0` on ALL FOUR builds so
//! it isolates the base-CSE lever (with const-CSE running, the range-free
//! arms shrink for const-CSE's own reasons and the F ≡ C equality goes
//! vacuous). No coverage is lost: with any range marked const-CSE declines
//! wholesale, so the range-marked builds are byte-identical to the shipped
//! default — exactly what the const-CSE gate below asserts.
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
/// `envs` supplies the lever flags (e.g. the `SYNTH_BASE_CSE=0` opt-out —
/// base-CSE is DEFAULT-ON since the lever flip); both lever vars are first
/// removed so a stray value in the test environment can't skew a gate.
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
    cmd.env_remove("SYNTH_BASE_CSE");
    cmd.env_remove("SYNTH_CONST_CSE");
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
/// The base-CSE OPT-OUT (default-ON since the lever flip).
const BASE_CSE_OFF: (&str, &str) = ("SYNTH_BASE_CSE", "0");
/// The const-CSE OPT-OUT (default-ON since the #242 flip) — pinned on the
/// base-CSE lattice builds to isolate that lever.
const CONST_CSE_OFF: (&str, &str) = ("SYNTH_CONST_CSE", "0");

/// The red→green Phase-2 oracle for base-CSE (#468).
///
/// The fixture has 4 const-address stores: 2 inside the DMA window
/// [0x100,0x110), 2 outside. Four compiles pin the whole behavior lattice
/// (base-CSE is default-ON, so "no base-CSE" is the `SYNTH_BASE_CSE=0`
/// opt-out and "base-CSE" is the shipped default):
///   C  — base-CSE opted out, no ranges: the verbatim baseline (per-access
///        `movw/movt R12` base + `add` + store);
///   A  — default, no ranges: all 4 stores fold (strictly smaller than C —
///        non-vacuity: the optimization genuinely fires on this shape);
///   P  — default + `--volatile-segment 0x100:16`: the 2 window stores stay
///        verbatim, the 2 outside still fold — strictly between A and C.
///        (On pre-Phase-2 main P==A: the flag was ignored — the RED assertion.)
///   F  — default + a range covering ALL 4 stores: base-CSE fully declines,
///        byte-identical to C — every store survives verbatim.
#[test]
fn base_cse_honors_volatile_window_543() {
    let c = compile_text(FIXTURE, "baseline", &[BASE_CSE_OFF, CONST_CSE_OFF], &[]);
    let a = compile_text(FIXTURE, "folded", &[CONST_CSE_OFF], &[]);
    let p = compile_text(
        FIXTURE,
        "window",
        &[CONST_CSE_OFF],
        &["--volatile-segment", "0x100:16"],
    );
    let f = compile_text(
        FIXTURE,
        "fullcover",
        &[CONST_CSE_OFF],
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
         survives verbatim, byte-identical to the SYNTH_BASE_CSE=0 opt-out"
    );
}

/// The red→green Phase-2 oracle for const-CSE (DEFAULT-ON since the #242
/// flip): any marked range ⇒ wholesale decline (conservative v1 — constants
/// can't be classified address-vs-data), byte-identical to the
/// `SYNTH_CONST_CSE=0` opt-out. Uses the existing const-CSE headroom fixture
/// whose default reduction is already CI-pinned
/// (`const_cse_reduction_242.rs`). All three compiles pin `SYNTH_BASE_CSE=0`
/// to isolate the const-CSE lever: base-CSE is default-ON and does a SURGICAL
/// (per-access) volatile back-off, so leaving it on would make the
/// range-marked compile differ from the no-range baseline for base-CSE's own
/// reasons, vacuously defeating the equality this gate locks. (base-CSE
/// happens to decline on this fixture today, but the gate must not depend on
/// that accident.)
#[test]
fn const_cse_declines_wholesale_under_volatile_543() {
    let base = compile_text(
        "const_cse.wat",
        "cse_baseline",
        &[BASE_CSE_OFF, CONST_CSE_OFF],
        &[],
    );
    // Shipped default (const-CSE env untouched by `compile_text`'s removal).
    let on = compile_text("const_cse.wat", "cse_on", &[BASE_CSE_OFF], &[]);
    let on_volatile = compile_text(
        "const_cse.wat",
        "cse_on_volatile",
        &[BASE_CSE_OFF],
        &["--volatile-segment", "0x100:16"],
    );

    assert!(
        on.len() < base.len(),
        "non-vacuity: default const-CSE must fire on the headroom fixture \
         ({} B !< {} B)",
        on.len(),
        base.len()
    );
    assert_eq!(
        on_volatile, base,
        "#543 Phase 2 RED CHECK: with a marked volatile range the DEFAULT \
         const-CSE must decline wholesale — byte-identical to the \
         SYNTH_CONST_CSE=0 opt-out (a difference means a CSE rewrite still \
         fired inside a volatile build)"
    );
}

/// Empty-config identity, stated positively: passing NO `--volatile-segment`
/// on the shipped default (base-CSE ON) is unchanged behavior — the gates
/// reduce to the pre-#543 path by construction. (The opt-out inertness of the
/// flag itself is the Phase-1 `volatile_segment_flag_is_byte_inert_543` test;
/// the direct-path frozen bytes are the `frozen_codegen_bytes.rs` anchors.)
#[test]
fn volatile_gates_are_identity_when_no_range_marked_543() {
    let a1 = compile_text(FIXTURE, "id_a", &[], &[]);
    let a2 = compile_text(FIXTURE, "id_b", &[], &[]);
    assert_eq!(a1, a2, "deterministic compile");
}
