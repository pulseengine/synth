//! VCR-SEL-004 (#428) — the two-move arm is now REACHABLE (#7 closed the gap).
//!
//! gale's `gust_codegen_bench` on `gust_mix` surfaced two observations: the
//! cmp→select fusion fired one clamp and declined its sibling, and the two-move
//! `moveq→mov{invert(c)}` arm never executed end-to-end. Investigation (objdump of
//! a synthetic two-move fixture) showed a SINGLE root cause: `fuse_cmp_select`'s
//! `reg_dead_by_redef` only deleted the `SetCond` when the boolean was explicitly
//! *redefined* downstream — but the real selector ABANDONS the boolean temp after
//! the select (used once, not live-out, never rewritten), so the guard declined
//! for BOTH the declined clamp and every two-move shape.
//!
//! #7 fixed it: `reg_dead_by_redef` now recognizes the function's RETURN terminator
//! (`bx lr` / `pop {…,pc}`) — at which the only live-out registers are the ABI
//! result regs {R0,R1} — so an abandoned boolean in `R2`..`R8` is proven dead and
//! the two-move arm fuses end-to-end. This test LOCKS the reachability: the
//! synthetic two-move fixture (`val2` a live param ⇒ `movne dst,v1; moveq dst,v2`)
//! now fuses exactly 1 site, while an in-place fixture fuses several (non-vacuous).
//! Frozen-safe: flag-off (default) is byte-identical (gates #445/#446 stay green);
//! the default-on flip + gale's re-bench (which now exercises the two-move arm for
//! the first time) remain the separate gated step.
//!
//! Measure-only: drives the shipped binary with `SYNTH_CMP_SELECT_FUSE=1`
//! `SYNTH_FUSE_STATS=1` and parses the `[cmp-select-fuse] N select(s) fused` line.
//! Changes no production code and no emitted bytes (the flag is off by default).

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

/// Compile `fix` with fusion + stats on; return the total `N` across all
/// `[cmp-select-fuse] N select(s) fused` lines (one per function).
fn fused_count(fix: &str) -> usize {
    let path = fixture(fix);
    let out = Command::new(synth())
        .env("SYNTH_CMP_SELECT_FUSE", "1")
        .env("SYNTH_FUSE_STATS", "1")
        .args([
            "compile",
            path.to_str().unwrap(),
            "-o",
            &format!("/tmp/cstm_{fix}.elf"),
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
    combined
        .lines()
        .filter(|l| l.contains("[cmp-select-fuse]"))
        .filter_map(|l| {
            l.split("[cmp-select-fuse]")
                .nth(1)?
                .trim_start()
                .split(' ')
                .next()?
                .parse::<usize>()
                .ok()
        })
        .sum()
}

#[test]
fn two_move_select_arm_is_reachable_428() {
    // Non-vacuity: an in-place fixture fuses several sites, so the harness
    // genuinely observes fusion — a count on the two-move fixture is real, not a
    // parsing/plumbing artifact.
    let in_place = fused_count("control_step.wasm");
    assert!(
        in_place >= 1,
        "control_step should fuse its in-place clamps (got {in_place})"
    );

    // #7 closed the gap: the selector emits the two-move form for this fixture
    // (val2 a live param), and reg_dead_by_redef now recognizes the abandoned,
    // not-live-out boolean as dead at the function's return terminator — so the
    // two-move `mov{c} … mov{invert(c)}` arm fuses end-to-end. (Previously declined;
    // see fuse_two_move_abandoned_boolean_before_pop_return in liveness.rs for the
    // IR-level soundness, and the negatives that keep it sound: result-reg boolean,
    // branch-in-tail, bx-to-non-LR all still decline.)
    let two_move = fused_count("cmp_select_two_move.wat");
    assert_eq!(
        two_move, 1,
        "the two-move arm must now be reachable (fused {two_move}, want 1) — if 0, \
         the #7 deadness fix regressed; if >1 the fixture changed"
    );
}
