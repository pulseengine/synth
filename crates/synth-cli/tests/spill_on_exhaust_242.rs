//! VCR-RA-001 (#242) — allocation-time spill-on-exhaustion, the literal
//! "remove the register-exhaustion hard-fail" acceptance criterion for the
//! OPTIMIZED path.
//!
//! `spill_on_exhaust_242.wat` keeps 10 param-derived i32 values live at once,
//! exhausting the optimized path's R4-R8 scratch pool:
//!
//! * flag OFF (default): the function DECLINES to the direct selector (#496),
//!   observable as a `[recovery-stats] rung=spill` line — the RED state this
//!   test pins so the decline path stays honest.
//! * `SYNTH_SPILL_ON_EXHAUST=1`: the function stays on the optimized path
//!   (no recovery rung fires) by spilling the farthest-next-use value
//!   (Belady) to a frame slot at allocation time — the GREEN state.
//!
//! Execution equivalence vs wasmtime is gated separately by
//! `scripts/repro/spill_on_exhaust_242_differential.py` (unicorn).

use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/spill_on_exhaust_242.wat")
}

/// Compile the pressure fixture (NON-relocatable, so the optimized path is
/// eligible) and return the `[recovery-stats]` stderr lines.
fn compile(out: &str, spill_on_exhaust: bool) -> String {
    let mut cmd = Command::new(synth());
    cmd.env("SYNTH_RECOVERY_STATS", "1");
    if spill_on_exhaust {
        cmd.env("SYNTH_SPILL_ON_EXHAUST", "1");
    } else {
        cmd.env_remove("SYNTH_SPILL_ON_EXHAUST");
    }
    let out = cmd
        .args([
            "compile",
            fixture().to_str().unwrap(),
            "-o",
            out,
            "--target",
            "cortex-m4",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stderr)
        .lines()
        .filter(|l| l.contains("[recovery-stats]"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn spill_on_exhaust_red_flag_off_declines_to_direct_spill_rung() {
    // The #496 decline must keep working flag-off: pool exhaustion sends the
    // function to the direct selector, whose spill rung produces the code.
    let stats = compile("/tmp/soe_242_off.elf", false);
    assert!(
        stats.contains("rung=spill"),
        "flag-off the pressure fixture must decline to the direct selector's \
         spill rung (#496); got recovery stats:\n{stats}"
    );
}

#[test]
fn spill_on_exhaust_green_flag_on_stays_on_optimized_path() {
    // Flag-on, the optimized path spills at allocation time instead of
    // declining — no recovery rung fires at all (the ladder only runs when the
    // optimized path returns Err).
    let stats = compile("/tmp/soe_242_on.elf", true);
    assert!(
        stats.is_empty(),
        "flag-on the pressure fixture must stay on the optimized path (no \
         recovery rung); got recovery stats:\n{stats}"
    );
}
