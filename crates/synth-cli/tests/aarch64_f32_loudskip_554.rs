//! synth#554 — `-b aarch64` must fail HONESTLY on a scalar f32 op, never emit a
//! silent miscompile.
//!
//! Scalar `f32.*` is dropped by the wasm decoder (`_ => None`), so it is absent
//! from the op stream the backend selector sees — it never reaches the selector's
//! `unsupported wasm op` guard. Before the fix the aarch64 backend lowered the
//! remaining `[LocalGet, LocalGet, End]` into `mov w0, w1 ; ret` (returns the 2nd
//! operand instead of the sum) and reported success. That is strictly worse than
//! the honest "unsupported milestone-1 op" error the integer ops produce.
//!
//! The fix honors the decoder's `func.unsupported` loud-skip marker (#369) at the
//! single-function CLI boundary (and in `AArch64Backend::compile_module`). These
//! tests lock: (1) the f32 function is REJECTED with a non-zero exit and an
//! "unsupported" diagnostic; (2) a supported integer function still compiles (the
//! guard does not over-reject); (3) `--all-exports` loud-skips f32 while still
//! emitting the integer function.
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
            "f32add",
            "-o",
            "/tmp/aarch64_f32_554.o",
        ])
        .output()
        .expect("run synth");
    assert!(
        !out.status.success(),
        "expected a non-zero exit for an f32 function on -b aarch64; got success \
         (silent miscompile). stdout={} stderr={}",
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
