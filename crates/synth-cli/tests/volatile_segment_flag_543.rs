//! #543 Phase 1 — `--volatile-segment <base>:<len>` CLI flag: acceptance,
//! rejection, and INERTNESS.
//!
//! Phase 1 was FLAG + PLUMBING + TRACEABILITY — the marked DMA-window ranges
//! are parsed into `CompileConfig.volatile_segments` and threaded to codegen.
//! Phase 2 (LANDED — `volatile_segment_phase2_543.rs`) is the codegen back-off:
//! the #468 base-CSE excludes accesses inside a marked range from its fold set
//! and const-CSE declines wholesale while any range is marked.
//!
//! Since the base-CSE lever flip (#468, default-ON), the DEFAULT
//! configuration genuinely CONSUMES the ranges — marking a range can change
//! the emitted bytes (that is the Phase-2 contract working, locked in
//! `volatile_segment_phase2_543.rs`). The inertness claim locked HERE is
//! therefore the OPT-OUT form: with the levers disabled (`SYNTH_BASE_CSE=0`,
//! `SYNTH_CONST_CSE` unset — const-CSE is still opt-in), compiling WITH
//! `--volatile-segment` must produce byte-identical `.text` to compiling
//! WITHOUT it (the ranges are consumed vacuously). Value-level parsing
//! correctness (base/len, malformed → error) is unit-tested in
//! `main.rs::tests` (`volatile_segment_*_543`).
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

/// Compile a fixture on the optimized ARM path (self-contained image — the path
/// where const-CSE and the #468 base-CSE live). `envs` supplies lever flags
/// (e.g. the `SYNTH_BASE_CSE=0` opt-out); both lever vars are first removed so
/// a stray value in the test environment can't skew a gate. `extra` supplies
/// any additional CLI args (e.g. `--volatile-segment ...`). Returns the
/// `.text` bytes on success or the process exit/stderr on failure.
fn compile_text(
    fixture_name: &str,
    out_tag: &str,
    envs: &[(&str, &str)],
    extra: &[&str],
) -> Result<Vec<u8>, String> {
    let path = fixture(fixture_name);
    let elf = format!("/tmp/volseg543_{out_tag}.elf");
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
    if !out.status.success() {
        return Err(format!(
            "exit={:?} stderr={}",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let bytes = std::fs::read(&elf).expect("read elf");
    let obj = object::File::parse(&*bytes).expect("parse elf");
    let text = obj
        .section_by_name(".text")
        .expect("fixture must have a .text section")
        .data()
        .expect("read .text")
        .to_vec();
    Ok(text)
}

const FIXTURE: &str = "base_cse_branch.wat";

/// The flag is ACCEPTED end-to-end, singly and repeatably (>1 range), on both
/// hex and decimal forms.
#[test]
fn volatile_segment_flag_accepted_543() {
    compile_text(
        FIXTURE,
        "accept_single",
        &[],
        &["--volatile-segment", "0x20001000:4096"],
    )
    .expect("single --volatile-segment must be accepted");
    compile_text(
        FIXTURE,
        "accept_repeat",
        &[],
        &[
            "--volatile-segment",
            "0x20001000:4096",
            "--volatile-segment",
            "536875008:256",
        ],
    )
    .expect("repeated --volatile-segment must be accepted");
}

/// Malformed input is REJECTED with a non-zero exit (not silently dropped).
#[test]
fn volatile_segment_flag_rejects_garbage_543() {
    let err = compile_text(FIXTURE, "reject", &[], &["--volatile-segment", "garbage"])
        .expect_err("`--volatile-segment garbage` must fail");
    assert!(
        err.contains("volatile-segment"),
        "error should name the offending flag, got: {err}"
    );
}

/// INERTNESS on the LEVERS-OPTED-OUT configuration: with `SYNTH_BASE_CSE=0`
/// (base-CSE is default-ON since the lever flip) and const-CSE unset (still
/// opt-in), compiling WITH the flag is `.text`-byte-identical to compiling
/// WITHOUT it — the ranges are consumed vacuously when no address-caching
/// lever is active. The byte-CHANGING behavior on the shipped default (and
/// under `SYNTH_CONST_CSE=1`) is locked in `volatile_segment_phase2_543.rs`.
#[test]
fn volatile_segment_flag_is_byte_inert_543() {
    const BASE_CSE_OFF: (&str, &str) = ("SYNTH_BASE_CSE", "0");
    let without = compile_text(FIXTURE, "inert_without", &[BASE_CSE_OFF], &[])
        .expect("baseline compile (no flag) must succeed");
    let with = compile_text(
        FIXTURE,
        "inert_with",
        &[BASE_CSE_OFF],
        &["--volatile-segment", "0x20001000:4096"],
    )
    .expect("compile with flag must succeed");
    assert_eq!(
        without, with,
        "#543: --volatile-segment changed the emitted .text with every \
         address-caching lever disabled (SYNTH_BASE_CSE=0, const-CSE unset) \
         — the back-off must only fire through an active lever"
    );
}
