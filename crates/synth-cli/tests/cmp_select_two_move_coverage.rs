//! VCR-SEL-004 characterization (#428) — the two-move arm is unreachable today.
//!
//! gale's `gust_codegen_bench` on `gust_mix` surfaced two observations: the
//! cmp→select fusion fired one clamp and declined its sibling, and the two-move
//! `moveq→mov{invert(c)}` arm never executed end-to-end. Investigation (objdump of
//! a synthetic two-move fixture) showed a SINGLE root cause: `fuse_cmp_select`'s
//! `reg_dead_by_redef` requires an explicit downstream *redefinition* of the
//! boolean before it will delete the `SetCond`. The real selector ABANDONS the
//! boolean temp after the select (used once, not live-out, never rewritten), so
//! the guard conservatively declines — for BOTH the declined clamp and every
//! two-move shape. The two-move arm is therefore effectively unreachable through
//! the real selector under the current guard.
//!
//! This test LOCKS that finding: the synthetic two-move fixture (`val2` a live
//! param ⇒ the selector emits `movne dst,v1; moveq dst,v2`) currently fuses ZERO
//! sites, while an in-place fixture fuses several (so the harness is not vacuously
//! seeing "0"). When the deadness guard is improved to treat "abandoned +
//! not-live-out" as dead (the byte-changing VCR-SEL-004 follow-on that also closes
//! gale's clamp #2), this assertion flips: update the expectation to `> 0` and
//! re-freeze the differentials.
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
fn two_move_select_arm_currently_declines_428() {
    // Non-vacuity: an in-place fixture fuses several sites, so the harness
    // genuinely observes fusion — a "0" on the two-move fixture is real, not a
    // parsing/plumbing artifact.
    let in_place = fused_count("control_step.wasm");
    assert!(
        in_place >= 1,
        "control_step should fuse its in-place clamps (got {in_place}) — if this \
         is 0 the harness is broken, not the two-move finding"
    );

    // The finding: the selector emits the two-move form for this fixture (val2 a
    // live param), but reg_dead_by_redef declines it (boolean abandoned, not
    // redefined before return). FLIP TO `>= 1` when the deadness guard recognizes
    // "abandoned + not-live-out" as dead (VCR-SEL-004 follow-on; re-freeze then).
    let two_move = fused_count("cmp_select_two_move.wat");
    assert_eq!(
        two_move, 0,
        "two-move fixture fused {two_move} sites — the deadness guard now reaches \
         the two-move arm. This is the EXPECTED future state: flip this assertion \
         to `>= 1`, exercise the mov{{invert(c)}} arm under a differential, and \
         re-freeze the frozen fixtures."
    );
}
