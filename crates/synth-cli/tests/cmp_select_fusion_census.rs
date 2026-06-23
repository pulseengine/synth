//! VCR-SEL-004 / VCR-ORACLE-001 (#242, #428) — cmp→select fusion CENSUS.
//!
//! The blast-radius datum for gale's default-on FLIP decision. The flip turns
//! `SYNTH_CMP_SELECT_FUSE` on by default (byte-changing, silicon-gated); its
//! go/no-go rests on three pieces of evidence — gale owns runtime correctness
//! (`gust_codegen_bench`) and the M4-regression check (G474RE DWT); the synth-side
//! half is the *blast radius*: across the real frozen fixtures, how many select
//! sites fuse, split into the in-place single-move form vs the two-move
//! `mov{c}…mov{invert(c)}` form whose `mov{invert(c)}` arm #7 made reachable.
//!
//! HEADLINE FINDING (locked here): on EVERY real frozen fixture the two-move count
//! is ZERO — all fused sites are the in-place form. #7's two-move arm fires on no
//! real frozen fixture; its only exercisers are gale's `gust_mix` bench and the
//! synthetic `cmp_select_two_move.wat`. So the flip's novel-at-runtime path has
//! *thin real-code coverage* — gale's bench is load-bearing for it, not redundant.
//!
//! Frozen-safe: drives the shipped binary with `SYNTH_CMP_SELECT_FUSE=1`
//! `SYNTH_FUSE_STATS=1` and parses the `[cmp-select-fuse] N … (K two-move, M
//! in-place)` diagnostic. The flag is OFF by default, so production bytes are
//! unchanged (the frozen byte gates #445/#446 lock that). This test changes no
//! emitted bytes; it records a measurement baseline. If a selector change moves
//! these counts, the census moves and a reviewer sees the blast radius shift.

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

/// Compile `fix` (a frozen fixture) with fusion + stats on; return the summed
/// `(total, two_move)` across every `[cmp-select-fuse]` line (one per function).
fn census(fix: &str) -> (usize, usize) {
    let path = fixture(fix);
    let out = Command::new(synth())
        .env("SYNTH_CMP_SELECT_FUSE", "1")
        .env("SYNTH_FUSE_STATS", "1")
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &format!("/tmp/census_{fix}.elf"),
            "--target",
            "cortex-m4",
            "--all-exports",
            "--relocatable",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {fix}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let mut total = 0usize;
    let mut two_move = 0usize;
    for l in combined.lines().filter(|l| l.contains("[cmp-select-fuse]")) {
        // `[cmp-select-fuse] N select(s) fused to predicated moves (K two-move, M in-place)`
        let n: usize = l
            .split("[cmp-select-fuse]")
            .nth(1)
            .and_then(|r| r.trim_start().split(' ').next())
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| panic!("unparseable fuse line: {l}"));
        // `… moves (K two-move, …)` — anchor on the "two-move" token and take the
        // trailing number before it (can't split on '(' — `select(s)` has one too).
        let k: usize = l
            .split("two-move")
            .next()
            .and_then(|seg| {
                seg.trim_end()
                    .rsplit(|c: char| c.is_whitespace() || c == '(')
                    .find(|s| !s.is_empty())
            })
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| panic!("unparseable two-move count: {l}"));
        total += n;
        two_move += k;
    }
    (total, two_move)
}

/// Per-fixture baseline: `(fixture, total_fused, two_move)`. Measured 2026-06-23
/// on the v0.12.0 selector. `in_place = total - two_move`.
const BASELINE: &[(&str, usize, usize)] = &[
    ("control_step.wasm", 3, 0),
    ("flight_seam.wasm", 12, 0),
    ("flight_seam_flat.wasm", 12, 0),
    ("signed_div_const.wasm", 0, 0),
];

#[test]
fn fusion_census_matches_frozen_baseline_428() {
    let mut grand_total = 0usize;
    let mut grand_two_move = 0usize;
    for &(fix, want_total, want_two_move) in BASELINE {
        let (total, two_move) = census(fix);
        assert_eq!(
            (total, two_move),
            (want_total, want_two_move),
            "{fix}: fusion census drifted — got (total={total}, two_move={two_move}), \
             baseline (total={want_total}, two_move={want_two_move}). A selector change \
             altered the cmp→select blast radius; re-measure and update BASELINE \
             deliberately (and tell gale — the flip blast radius moved)."
        );
        grand_total += total;
        grand_two_move += two_move;
    }
    // Non-vacuity: the lever genuinely reaches real code (not a plumbing no-op).
    assert!(
        grand_total >= 1,
        "expected cmp→select to fuse on the frozen fixtures (got {grand_total})"
    );
    // The headline finding: #7's two-move arm fires on NO real frozen fixture.
    // If this ever becomes non-zero, a real fixture started exercising the
    // mov{invert(c)} arm — that is GOOD (more real coverage of the flip's novel
    // path) but must be a deliberate baseline update, and gale should know its
    // bench is no longer the sole runtime exerciser.
    assert_eq!(
        grand_two_move, 0,
        "a real frozen fixture now exercises the two-move arm ({grand_two_move} sites) — \
         update BASELINE and notify gale that the flip's runtime path gained real-code \
         coverage beyond gust_mix"
    );
}
