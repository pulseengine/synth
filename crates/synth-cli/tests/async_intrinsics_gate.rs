//! #80 P3 async intrinsic honest-degradation gate (CLI end-to-end).
//!
//! Synth lowers exactly ONE async intrinsic family — `error-context` — and
//! LOUD-DECLINES the rest by name. This test exercises the real `synth compile`
//! binary:
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

fn synth_binary() -> PathBuf {
    let mut path = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    path.push("synth");
    path
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
    let out = std::env::temp_dir().join("synth_async_ec.o");

    let result = Command::new(synth_binary())
        .args([
            "compile",
            wat.to_str().unwrap(),
            "--no-optimize",
            "--relocatable",
            "-o",
            out.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");

    assert!(
        result.status.success(),
        "error-context should compile; stderr={}",
        String::from_utf8_lossy(&result.stderr)
    );

    // The field-name `error-context.drop` must appear as the BL target symbol
    // in the ELF (the host-link contract). We scan the raw bytes for the
    // symbol string — the relocatable path records it as an UNDEF symbol.
    let data = std::fs::read(&out).unwrap();
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
