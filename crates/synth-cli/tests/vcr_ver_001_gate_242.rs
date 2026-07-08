//! VCR-VER-001 (#242) — program-gate lock: the greedy-fix reversal flag must
//! not disturb the frozen result anchors.
//!
//! The gate's second demonstration (see `scripts/repro/vcr_ver_001_gate.md`)
//! reverts the #496 register-exhaustion hard-decline behind
//! `SYNTH_SPILL_ON_EXHAUST` (#580): flag-on, a function whose optimized-path
//! allocation exhausts the R4-R8 scratch/pair pool spills at allocation time
//! (Belady) instead of declining to the direct selector. The reversal's blast
//! radius must be exactly the formerly-declining functions:
//!
//! * The three frozen result-anchor fixtures (`control_step` `0x00210A55`,
//!   `flight_seam`/`flight_seam_flat` `0x07FDF307`) decline for reasons the
//!   flag does NOT address (rung=spill via a non-exhaustion optimized-path
//!   Err; rung=base), so their DEFAULT-path bytes must be BIT-IDENTICAL with
//!   the flag on — asserted here. If this ever fails, the reversal grew a new
//!   blast radius and the gate evidence must be re-derived (differentials
//!   re-run on the new bytes) before any flip.
//! * `signed_div_const` is deliberately NOT pinned: it IS flag-sensitive
//!   (its rung=base decline is recovered into an optimized-path compile at
//!   34→76 B, execution-verified) — the measured reason the default-on flip
//!   is held. Pinning its sensitivity would be a speculative tripwire; the
//!   sensitivity is documented in the gate note instead.
//!
//! Execution equivalence of the changed (unpinned) pressure-fixture bytes is
//! gated by `scripts/repro/spill_on_exhaust_242_differential.py`,
//! `i64_pair_exhaust_587_differential.py`, `i64_spill_pool_587_differential.py`,
//! `spill_rung_581_differential.py` and `r12_spill_496_differential.py`.

use std::process::Command;

use object::{Object, ObjectSection};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro")
        .join(name)
}

/// Compile `wasm` on the DEFAULT path (no `--relocatable` — the optimized
/// path is eligible, the one the #496 decline and its reversal act on) and
/// return the `.text` bytes.
fn default_path_text(wasm: &str, spill_on_exhaust: bool) -> Vec<u8> {
    let elf = format!(
        "/tmp/vcr_ver_001_{}_{wasm}.elf",
        if spill_on_exhaust { "on" } else { "off" }
    );
    let mut cmd = Command::new(synth());
    if spill_on_exhaust {
        cmd.env("SYNTH_SPILL_ON_EXHAUST", "1");
    } else {
        cmd.env_remove("SYNTH_SPILL_ON_EXHAUST");
    }
    let out = cmd
        .args([
            "compile",
            fixture(wasm).to_str().unwrap(),
            "-o",
            &elf,
            "--target",
            "cortex-m4",
            "--all-exports",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "synth compile failed for {wasm}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bin = std::fs::read(&elf).expect("read ELF");
    let obj = object::File::parse(&*bin).expect("parse ELF");
    obj.section_by_name(".text")
        .expect(".text")
        .data()
        .expect("section data")
        .to_vec()
}

#[test]
fn vcr_ver_001_reversal_flag_leaves_frozen_anchors_byte_identical() {
    for wasm in [
        "control_step.wasm",
        "flight_seam.wasm",
        "flight_seam_flat.wasm",
    ] {
        let off = default_path_text(wasm, false);
        let on = default_path_text(wasm, true);
        assert_eq!(
            off, on,
            "{wasm}: SYNTH_SPILL_ON_EXHAUST changed a frozen result anchor's \
             default-path bytes — the VCR-VER-001 reversal's blast radius grew \
             beyond the formerly-declining functions; re-derive the gate \
             evidence (scripts/repro/vcr_ver_001_gate.md) before any flip"
        );
    }
}
