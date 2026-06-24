//! VCR-RA recovery-rung measurement (#242) — assert which exhaustion-recovery
//! rung `select_direct` uses for the corpus fixtures that exercise the ladder.
//!
//! `SYNTH_RECOVERY_STATS=1` makes the backend log `[recovery-stats] rung=…` per
//! function (logging only — emitted bytes are unchanged, the frozen byte gate is
//! unaffected). This test pins the rung classification documented in
//! `scripts/repro/register_exhaustion_recovery_ladder.md`: the recovery ladder is
//! the failure surface the verified allocator (#242) must subsume, and this is the
//! executable record of how big that surface is on the in-repo corpus (3 fixtures).

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

/// Compile a fixture with `SYNTH_RECOVERY_STATS=1` and return the captured
/// `[recovery-stats]` stderr lines joined.
fn recovery_stats(wasm: &str) -> String {
    let out = Command::new(synth())
        .env("SYNTH_RECOVERY_STATS", "1")
        .args([
            "compile",
            fixture(wasm).to_str().unwrap(),
            "-o",
            &format!("/tmp/recstats_{wasm}.elf"),
            "--target",
            "cortex-m4",
            "--relocatable",
            "--all-exports",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "compile {wasm} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stderr)
        .lines()
        .filter(|l| l.contains("[recovery-stats]"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn recovery_stats_rung_classification_242() {
    // The three corpus fixtures that exercise the recovery ladder.
    let hp32 = recovery_stats("high_pressure_i32.wat");
    assert!(
        hp32.contains("rung=spill"),
        "high_pressure_i32 should hit the spill rung; got:\n{hp32}"
    );

    let hp64 = recovery_stats("high_pressure_i64.wat");
    assert!(
        hp64.contains("rung=param-backing"),
        "high_pressure_i64 should hit the param-backing rung; got:\n{hp64}"
    );

    // #474 fallback: promotion is dropped, then the promotion-off ladder spills.
    let pef = recovery_stats("promotion_exhaustion_fallback.wat");
    assert!(
        pef.contains("promotion-off"),
        "promotion_exhaustion_fallback should hit the promotion-off fallback; got:\n{pef}"
    );

    // control_step (the canonical frozen fixture, 0x00210A55) sits right at the
    // register-pressure edge — it is produced via the SPILL rung, not the base
    // attempt. Pinning this guards that its frozen bytes are the spill-rung output.
    let cs = recovery_stats("control_step.wasm");
    assert!(
        cs.contains("rung=spill") && !cs.contains("promotion-off"),
        "control_step should compile via the spill rung; got:\n{cs}"
    );

    // A representative base-rung fixture compiles on the first attempt.
    let base = recovery_stats("local_promote_i32.wat");
    assert!(
        base.contains("rung=base") && !base.contains("spill"),
        "local_promote_i32 should compile on the base attempt; got:\n{base}"
    );
}
