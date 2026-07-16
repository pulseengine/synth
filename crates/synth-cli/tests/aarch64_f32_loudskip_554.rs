//! synth#554 — `-b aarch64` must fail HONESTLY on an UNSUPPORTED float op, never
//! emit a silent miscompile.
//!
//! m3 (#787) landed the non-trapping scalar floats; m4 (#538) landed the
//! #709-class conversions (domain-guarded `i32.trunc_f32/f64_{s,u}`, FMIN/FMAX
//! min/max, copysign), so this test now targets a float op that DELIBERATELY
//! stays declined: `f64.floor` (rounding). It is DECODED (the ARM32 m7dp
//! backend lowers it), so it reaches the aarch64 SELECTOR, which must
//! loud-decline (`unsupported wasm op`) — the strongest form of the honesty
//! check (nothing upstream masks it).
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
            "f64floor",
            "-o",
            "/tmp/aarch64_f32_554.o",
        ])
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "expected a non-zero exit for a declined float op (f64.floor) on \
         -b aarch64; got success (silent miscompile). stdout={} stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    let stderr = String::from_utf8_lossy(&out.stderr).to_lowercase();
    assert!(
        stderr.contains("unsupported"),
        "error must name the unsupported operator; stderr={stderr}"
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
