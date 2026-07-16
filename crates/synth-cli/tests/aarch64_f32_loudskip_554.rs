//! synth#554 — `-b aarch64` must fail HONESTLY on an UNSUPPORTED float op, never
//! emit a silent miscompile.
//!
//! m3 (#787) landed the non-trapping scalar floats, so this test now targets a
//! float op that DELIBERATELY stays declined: `i32.trunc_f32_s`. A64 `FCVTZS`
//! SATURATES where WASM TRAPS (out-of-range input) — the #709 more-total-than-WASM
//! soundness class — so lowering it would silently return a wrong (saturated)
//! value. The backend must loud-decline (`unsupported wasm op`) instead.
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
            "f32trunc",
            "-o",
            "/tmp/aarch64_f32_554.o",
        ])
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "expected a non-zero exit for a declined float op (i32.trunc_f32_s) on \
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
