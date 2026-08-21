//! #80 P3 async intrinsic honest-degradation gate (CLI end-to-end).
//!
//! Synth lowers exactly ONE async intrinsic op — `error-context.drop` (a
//! scalar handle op) — and LOUD-DECLINES the rest by name, INCLUDING the other
//! error-context ops (`.new`/`.debug-message`) which carry a linmem message
//! pointer. This test exercises the real `synth compile` binary:
//!
//! - the LOWERED family (`error-context.drop`) compiles to a relocatable ELF
//!   whose symtab carries the field-name as an UNDEFINED symbol — the AAPCS
//!   `BL` call site the host linker resolves against kiln-builtins (the
//!   "executes vs reference" ABI contract, checked via symtab per the
//!   read-symtab-not-disasm lesson);
//! - each DECLINED family (`stream`, `future`, `waitable-set`, `task`) makes
//!   the compile FAIL with a machine reason naming the family.

use std::path::{Path, PathBuf};
use std::process::Command;

// #977 RQ-59-FRESHNESS: nothing here parses an artifact until the artifact is
// proven to be THIS invocation's output — see `artifact_guard`.
mod artifact_guard;

/// Locate the `synth` binary the way every other CLI test does.
///
/// This used to walk two parents up from `current_exe()` and append `synth`,
/// which happens to be right for the plain `target/debug/deps/<test>` layout and
/// WRONG for any other. Under `cargo llvm-cov` the test binary lives at
/// `target/llvm-cov-target/debug/build/synth-cli/<hash>/out/<test>`, so the walk
/// produced `…/<hash>/synth` — a path that does not exist — and BOTH tests in
/// this file failed for a missing binary rather than for anything they assert.
/// That kept `Code Coverage` red repo-wide while the required `Test` job (plain
/// layout) stayed green: a real gate, failing for a reason unrelated to the code.
///
/// `CARGO_BIN_EXE_<name>` is set by Cargo at compile time to the actual path of
/// the built binary, so it is correct under every target-dir layout. Same
/// mechanism as the other CLI integration tests in this directory.
fn synth_binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn fixture(name: &str) -> PathBuf {
    workspace_root()
        .join("tests")
        .join("integration")
        .join(name)
}

/// The LOWERED family compiles and emits a field-name BL call site.
#[test]
fn error_context_family_is_lowered_and_emits_field_name_symbol() {
    let wat = fixture("async_error_context.wat");
    assert!(wat.exists(), "fixture missing: {}", wat.display());
    // #977: unique per call + remove-first + status/exists/non-empty guards.
    let out = artifact_guard::unique_artifact("synth_async_ec", "o");

    let mut cmd = Command::new(synth_binary());
    cmd.args([
        "compile",
        wat.to_str().unwrap(),
        "--no-optimize",
        "--relocatable",
        "-o",
        out.to_str().unwrap(),
    ]);
    let data =
        artifact_guard::compile_bytes_or_panic(&mut cmd, &out, "error-context should compile");

    // The field-name `error-context.drop` must appear as the BL target symbol
    // in the ELF (the host-link contract). We scan the raw bytes for the
    // symbol string — the relocatable path records it as an UNDEF symbol.
    assert_eq!(&data[0..4], b"\x7fELF", "not an ELF");
    let sym = b"error-context.drop";
    assert!(
        data.windows(sym.len()).any(|w| w == sym),
        "field-name BL target 'error-context.drop' must be in the ELF symbol \
         table (the AAPCS call site the host linker resolves)"
    );
}

/// Every DECLINED family fails the compile with a named machine reason.
#[test]
fn declined_families_reject_loudly() {
    // (fixture, family substring the diagnostic must name)
    let cases = [
        ("async_stream_declined.wat", "stream"),
        ("async_future_declined.wat", "future"),
        ("async_waitable_declined.wat", "waitable"),
        ("async_task_declined.wat", "task"),
        // SOUNDNESS: error-context.new carries a linmem message pointer — it is
        // NOT the scalar op error-context.drop, so it is declined (buffer class).
        ("async_error_context_new_declined.wat", "buffer"),
    ];
    for (fixture_name, family) in cases {
        let wat = fixture(fixture_name);
        assert!(wat.exists(), "fixture missing: {}", wat.display());
        let out = std::env::temp_dir().join(format!("synth_async_decl_{family}.o"));

        let result = Command::new(synth_binary())
            .args([
                "compile",
                wat.to_str().unwrap(),
                "--no-optimize",
                "-o",
                out.to_str().unwrap(),
            ])
            .output()
            .expect("run synth");

        assert!(
            !result.status.success(),
            "{fixture_name}: declined family must FAIL the compile"
        );
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(
            stderr.contains("#80 async-intrinsic decline"),
            "{fixture_name}: decline must carry the #80 machine reason; got: {stderr}"
        );
        assert!(
            stderr.contains(family),
            "{fixture_name}: decline must name the '{family}' family; got: {stderr}"
        );
    }
}
