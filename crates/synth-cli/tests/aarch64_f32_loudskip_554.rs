//! synth#554 — `-b aarch64` must fail HONESTLY on an UNSUPPORTED float op, never
//! emit a silent miscompile.
//!
//! The honesty target MOVES as the surface closes: m3 (#787) landed the
//! non-trapping scalar floats, m4 (#538) the #709-class conversions, v0.54 L2
//! the last four scalar-float classes, and v0.55 L6 (VCR-A64-CF-001) the
//! VALUE-CARRYING f32-result `block` this test used to target. It now targets a
//! float construct that DELIBERATELY stays declined: a NON-LEAF function
//! reading an f32 PARAMETER (float params live in v0..v7, which a `bl`
//! clobbers, and this encoder has no FP store to home them with). It is fully
//! DECODED, so it reaches the aarch64 SELECTOR, which must loud-decline — the
//! strongest form of the honesty check (nothing upstream masks it).
//!
//! These tests lock: (1) the declined-float function is REJECTED with a non-zero
//! exit and an "unsupported" diagnostic; (2) a supported integer function still
//! compiles (the guard does not over-reject).
use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/aarch64_f32_unsupported_554.wat")
}

#[test]
fn aarch64_rejects_f32_function_instead_of_silent_miscompile_554() {
    let out = Command::new(synth())
        .args([
            "compile",
            fixture().to_str().unwrap(),
            "-b",
            "aarch64",
            "-n",
            "f32nonleaf",
            "-o",
            "/tmp/aarch64_f32_554.o",
        ])
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "expected a non-zero exit for a declined float construct (an f32 param \
         read in a NON-LEAF function) on -b aarch64; got success (silent \
         miscompile). stdout={} stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    let stderr = String::from_utf8_lossy(&out.stderr).to_lowercase();
    // The decline must come from the SELECTOR (nothing upstream masked it) and
    // must NAME the reason — a bare non-zero exit is not honesty.
    assert!(
        stderr.contains("aarch64 selector"),
        "the decline must come from the aarch64 selector, not an upstream \
         drop; stderr={stderr}"
    );
    assert!(
        stderr.contains("loud-declining") || stderr.contains("only void"),
        "error must name why the construct is declined; stderr={stderr}"
    );
}

#[test]
fn aarch64_still_compiles_supported_integer_function_554() {
    // The guard must not over-reject: a fully-supported milestone-1 function
    // in the SAME module still compiles.
    let out = Command::new(synth())
        .args([
            "compile",
            fixture().to_str().unwrap(),
            "-b",
            "aarch64",
            "-n",
            "i32add",
            "-o",
            "/tmp/aarch64_i32_554.o",
        ])
        .output()
        .expect("run synth");
    assert!(
        out.status.success(),
        "supported i32 function must still compile on -b aarch64; stderr={}",
        String::from_utf8_lossy(&out.stderr),
    );
}
