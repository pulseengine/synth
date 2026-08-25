//! RQ-59-DATASEG (#1041) — the ARM relocatable path must REFUSE a module
//! whose active data segments it does not materialize.
//!
//! Pre-fix behaviour (the filed bug): `--relocatable` on a Thumb-2 target
//! accepted a module carrying an active data segment, emitted NONE of the
//! initializer bytes, emitted no data symbol, printed no warning, and exited
//! 0 — every static initialized by a data segment then reads whatever the
//! target memory happens to contain (0xFF on unwritten flash). That is the
//! one behaviour the honest-frontier rule exists to prevent: a loud decline
//! costs a build failure; a silent drop costs a wrong answer at runtime,
//! arbitrarily far from its cause (gale#278's `state(0) == 255`).
//!
//! The refusal mirrors the aarch64 backend's #851 guard (same class, same
//! shape). The assertion here is deliberately about the REFUSAL — a clean
//! non-zero exit plus a reason string naming the data segments — NOT about
//! the absence of the bytes in the object, which was already true on the
//! broken behaviour and would make this test vacuously green.
//!
//! Shipping the data on this path (RISC-V-style records placed by a linker
//! script and copied at reset) is v0.60 capability work (VCR-REACH-002),
//! not this fix.

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Write an inline wat to a temp file and return its path.
fn wat_file(name: &str, wat: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("synth_dataseg_1041_tests");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join(name);
    std::fs::write(&p, wat).expect("write wat");
    p
}

fn compile(input: &std::path::Path, extra: &[&str]) -> std::process::Output {
    let out = std::env::temp_dir()
        .join("synth_dataseg_1041_tests")
        .join(format!(
            "{}_{}.o",
            input.file_stem().unwrap().to_str().unwrap(),
            extra.join("").replace(['-', '/', ' '], "")
        ));
    let mut args = vec![
        "compile",
        input.to_str().unwrap(),
        "--all-exports",
        "-o",
        out.to_str().unwrap(),
    ];
    args.extend_from_slice(extra);
    Command::new(synth())
        .args(&args)
        .output()
        .expect("run synth")
}

fn stderr(out: &std::process::Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

/// A refusal must be loud AND precise: non-zero exit + a reason naming the
/// data segments (the multi_memory_406 house rule).
fn assert_refused(out: &std::process::Output, must_mention: &[&str], ctx: &str) {
    assert!(
        !out.status.success(),
        "{ctx}: expected a loud refusal, got success (exit 0 is the #1041 \
         silent-drop bug).\nstderr: {}",
        stderr(out)
    );
    let err = stderr(out);
    for needle in must_mention {
        assert!(
            err.contains(needle),
            "{ctx}: refusal does not mention '{needle}'.\nstderr: {err}"
        );
    }
}

/// The 4-byte filed repro: an active const-offset data segment on memory 0,
/// compiled `--relocatable` for a Thumb-2 target. Must refuse loudly.
#[test]
fn active_dataseg_on_relocatable_refuses_loudly() {
    let f = wat_file(
        "active_dataseg.wat",
        r#"(module
      (memory 1)
      (data (i32.const 0) "\01\02\03\04")
      (func (export "get") (result i32) i32.const 0 i32.load8_u))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["active data segment", "#1041"],
        "active data segment on --relocatable",
    );
}

/// Same class on the A32 (cortex-r5) relocatable path — the guard is
/// per-path, not per-encoding.
#[test]
fn active_dataseg_on_a32_relocatable_refuses_loudly() {
    let f = wat_file(
        "active_dataseg_a32.wat",
        r#"(module
      (memory 1)
      (data (i32.const 0) "\01\02\03\04")
      (func (export "get") (result i32) i32.const 0 i32.load8_u))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-r5"]);
    assert_refused(
        &out,
        &["active data segment", "#1041"],
        "active data segment on cortex-r5 --relocatable",
    );
}

/// An external import forces ET_REL even WITHOUT `--relocatable` — the same
/// builder runs, so the same silent drop happened there. Must refuse too.
#[test]
fn active_dataseg_on_import_forced_etrel_refuses_loudly() {
    let f = wat_file(
        "active_dataseg_import.wat",
        r#"(module
      (import "env" "ext" (func $ext (param i32) (result i32)))
      (memory 1)
      (data (i32.const 0) "\01\02\03\04")
      (func (export "get") (result i32)
        i32.const 0 i32.load8_u call $ext))"#,
    );
    let out = compile(&f, &["--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["active data segment", "#1041"],
        "active data segment on import-forced ET_REL",
    );
}

/// A memory-0 segment whose offset is NOT a compile-time constant was
/// legacy-dropped at decode (#851 records the reason); the ARM relocatable
/// path must consult that record and refuse — the aarch64 guard's mirror.
#[test]
fn nonconst_offset_dataseg_on_relocatable_refuses_loudly() {
    let f = wat_file(
        "nonconst_dataseg.wat",
        r#"(module
      (import "env" "base" (global $base i32))
      (memory 1)
      (data (global.get $base) "\01\02\03\04")
      (func (export "get") (result i32) i32.const 0 i32.load8_u))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["non-constant offset", "#1041"],
        "non-const-offset data segment on --relocatable",
    );
}

/// Green control against over-refusal: the SAME module minus the data
/// segment still compiles to a relocatable object with exit 0.
#[test]
fn dataless_module_on_relocatable_still_compiles() {
    let f = wat_file(
        "dataless.wat",
        r#"(module
      (memory 1)
      (func (export "get") (result i32) i32.const 0 i32.load8_u))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert!(
        out.status.success(),
        "dataless --relocatable module must still compile.\nstderr: {}",
        stderr(&out)
    );
}
