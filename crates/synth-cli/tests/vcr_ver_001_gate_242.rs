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

// #977 RQ-59-FRESHNESS: nothing here parses an artifact until the artifact is
// proven to be THIS invocation's output — see `artifact_guard`. A stale read
// in a flip gate does not fail, it re-confirms last run's golden as this
// run's evidence.
mod artifact_guard;

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
    // #977: unique per call + remove-first + status/exists/non-empty guards —
    // a stale ELF at a fixed /tmp path must never be parsed as this run's.
    let elf = artifact_guard::unique_artifact(
        &format!(
            "vcr_ver_001_{}_{wasm}",
            if spill_on_exhaust { "on" } else { "off" }
        ),
        "elf",
    );
    let mut cmd = Command::new(synth());
    if spill_on_exhaust {
        cmd.env("SYNTH_SPILL_ON_EXHAUST", "1");
    } else {
        cmd.env_remove("SYNTH_SPILL_ON_EXHAUST");
    }
    cmd.args([
        "compile",
        fixture(wasm).to_str().unwrap(),
        "-o",
        elf.to_str().unwrap(),
        "--target",
        "cortex-m4",
        "--all-exports",
    ]);
    let bin = artifact_guard::compile_bytes_or_panic(
        &mut cmd,
        &elf,
        &format!("{wasm} (spill_on_exhaust={spill_on_exhaust})"),
    );
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
