//! #543 Phase 1 — `--volatile-segment <base>:<len>` CLI flag: acceptance,
//! rejection, and INERTNESS.
//!
//! Phase 1 is FLAG + PLUMBING + TRACEABILITY only — the marked DMA-window ranges
//! are parsed into `CompileConfig.volatile_segments` and threaded to codegen, but
//! NOT yet consumed by any pass. The codegen back-off (const-CSE + the #468
//! base-CSE declining inside a marked range) is the gated Phase 2.
//!
//! The load-bearing Phase-1 claim is therefore INERTNESS *even when the flag is
//! set*: compiling WITH `--volatile-segment` must produce byte-identical `.text`
//! to compiling WITHOUT it. `frozen_codegen_bytes.rs` only proves the flag-OFF
//! bytes are unchanged (trivially true for an empty default); this test proves
//! the stronger promise. Value-level parsing correctness (base/len, malformed →
//! error) is unit-tested in `main.rs::tests` (`volatile_segment_*_543`).
//!
//! Traceability: rivet `VCR-DMA-001` (status `proposed`), gale decision
//! `DD-DMA-REGION-001`.

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
/// where const-CSE and the #468 base-CSE live, so the Phase-2 back-off will
/// eventually change these bytes). `extra` supplies any additional CLI args
/// (e.g. `--volatile-segment ...`). Returns the `.text` bytes on success or the
/// process exit/stderr on failure.
fn compile_text(fixture_name: &str, out_tag: &str, extra: &[&str]) -> Result<Vec<u8>, String> {
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
    let out = Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth");
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
        &["--volatile-segment", "0x20001000:4096"],
    )
    .expect("single --volatile-segment must be accepted");
    compile_text(
        FIXTURE,
        "accept_repeat",
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
    let err = compile_text(FIXTURE, "reject", &["--volatile-segment", "garbage"])
        .expect_err("`--volatile-segment garbage` must fail");
    assert!(
        err.contains("volatile-segment"),
        "error should name the offending flag, got: {err}"
    );
}

/// INERTNESS: compiling WITH the flag is `.text`-byte-identical to compiling
/// WITHOUT it. This is the Phase-1 frozen-safe contract — the ranges are parsed
/// and threaded but no pass consumes them yet, so no emitted byte moves.
#[test]
fn volatile_segment_flag_is_byte_inert_543() {
    let without = compile_text(FIXTURE, "inert_without", &[])
        .expect("baseline compile (no flag) must succeed");
    let with = compile_text(
        FIXTURE,
        "inert_with",
        &["--volatile-segment", "0x20001000:4096"],
    )
    .expect("compile with flag must succeed");
    assert_eq!(
        without, with,
        "#543 Phase 1 must be inert: --volatile-segment changed the emitted .text \
         (that back-off is the GATED Phase 2, not Phase 1)"
    );
}
