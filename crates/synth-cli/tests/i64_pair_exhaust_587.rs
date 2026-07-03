//! #587 (VCR-RA, #242) — i64 register-PAIR exhaustion on the OPTIMIZED path,
//! the falcon regalloc remainder from #580/v0.24.0.
//!
//! `i64_pair_exhaust_587.wat` keeps five i64 values simultaneously live — one
//! more than `alloc_i64_pair`'s four even-aligned candidate pairs:
//!
//! * flag OFF (default): the function DECLINES to the direct selector (#496),
//!   observable as a `[recovery-stats]` rung line — the RED state this test
//!   pins so the decline path stays honest (loud skip, never wrong code).
//! * `SYNTH_SPILL_ON_EXHAUST=1`: the pair-aware Belady pre-step evicts a
//!   coherent PAIR (or two singles) to an 8-byte-aligned slot pair and the
//!   function stays on the optimized path (no recovery rung fires) — the
//!   GREEN state (pre-#587 this ALSO declined: the i32-only scope gate turned
//!   the lever off for any function containing i64 opcodes).
//!
//! Execution equivalence vs wasmtime is gated separately by
//! `scripts/repro/i64_pair_exhaust_587_differential.py` (unicorn).

use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/i64_pair_exhaust_587.wat")
}

/// Compile the pair-pressure fixture (NON-relocatable, so the optimized path
/// is eligible) and return the `[recovery-stats]` stderr lines.
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
fn i64_pair_exhaust_red_flag_off_declines_to_direct_selector() {
    // The #496 decline must keep working flag-off: pair exhaustion sends the
    // function to the direct selector's recovery ladder (loud, never wrong
    // code).
    let stats = compile("/tmp/pe587_off.elf", false);
    assert!(
        !stats.is_empty(),
        "flag-off the i64 pair-pressure fixture must decline to the direct \
         selector's recovery ladder (#496); got no recovery stats"
    );
}

#[test]
fn i64_pair_exhaust_green_flag_on_stays_on_optimized_path() {
    // Flag-on, the pair-aware pre-step spills at allocation time instead of
    // declining — no recovery rung fires at all (the ladder only runs when
    // the optimized path returns Err).
    let stats = compile("/tmp/pe587_on.elf", true);
    assert!(
        stats.is_empty(),
        "flag-on the i64 pair-pressure fixture must stay on the optimized \
         path (no recovery rung); got recovery stats:\n{stats}"
    );
}
