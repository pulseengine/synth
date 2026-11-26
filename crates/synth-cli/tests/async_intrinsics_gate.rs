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

// ---------------------------------------------------------------------------
// P3-BUILTINS I1 (pulseengine/meld#693): DEAD legacy `pulseengine:async`
// imports are accepted; LIVE ones keep the #80 decline, unchanged.
//
// meld's fused output still imports `pulseengine:async::stream_new` /
// `stream_write` with zero references. The shapes below are that import pair
// (same signatures as the meld#692 fixture) under five module bodies: one with
// no reference (accepted) and one per way a module can reference a function
// (called, elem segment, `ref.func`, re-exported), each of which must refuse
// with the classifier's exact wording.
// ---------------------------------------------------------------------------

const LEGACY_IMPORTS: &str = r#"
  (import "pulseengine:async" "stream_new" (func $stream_new (result i64)))
  (import "pulseengine:async" "stream_write"
    (func $stream_write (param i32 i32 i32 i32) (result i32)))"#;

/// The classifier's exact decline for `stream_new`, the first legacy import.
const STREAM_NEW_DECLINE: &str = "#80 async-intrinsic decline: unknown P3-async intrinsic \
     'pulseengine:async::stream_new' — synth will not emit a call against an unspecified \
     async contract (RFC #46); recognized families: error-context (lowered), stream / \
     future / waitable-set / task (declined)";

/// The configurations the dead-import acceptance is checked under: the ARM
/// relocatable object meld's output targets, the self-contained Cortex-M
/// image, and RV32 (the #80 gate is backend-independent).
const LEGACY_CONFIGS: &[&[&str]] = &[
    &["-t", "cortex-m7", "--relocatable"],
    &["-t", "cortex-m7", "--cortex-m"],
    &["-b", "riscv", "--relocatable"],
];

fn legacy_module(body: &str) -> String {
    format!("(module{LEGACY_IMPORTS}\n{body})")
}

fn write_wat(tag: &str, src: &str) -> PathBuf {
    let p = artifact_guard::unique_artifact(tag, "wat");
    std::fs::write(&p, src).expect("write wat");
    p
}

fn legacy_compile(wat: &Path, out: &Path, flags: &[&str]) -> Command {
    let mut cmd = Command::new(synth_binary());
    cmd.args(["compile", wat.to_str().unwrap()])
        .args(flags)
        .args(["-o", out.to_str().unwrap()]);
    cmd
}

/// RED-FIRST (I1): both legacy imports unreferenced. On d8fc1b3f this refused
/// with `STREAM_NEW_DECLINE`; it must now compile, and the object must carry
/// NO symbol and NO relocation for either legacy import.
#[test]
fn dead_legacy_async_imports_are_accepted_and_emit_no_symbol() {
    use object::{Object, ObjectSection, ObjectSymbol};
    let wat = write_wat(
        "async_legacy_dead",
        &legacy_module(r#"(func (export "get") (result i32) i32.const 7)"#),
    );
    for flags in LEGACY_CONFIGS {
        let out = artifact_guard::unique_artifact("async_legacy_dead", "o");
        let mut cmd = legacy_compile(&wat, &out, flags);
        let data = artifact_guard::compile_bytes_or_panic(
            &mut cmd,
            &out,
            "a module whose pulseengine:async imports are all unreferenced must compile",
        );
        let obj = object::File::parse(&*data).expect("parse object");
        let names: Vec<String> = obj
            .symbols()
            .filter_map(|s| s.name().ok().map(str::to_string))
            .collect();
        assert!(
            names.iter().any(|n| n == "get"),
            "{flags:?}: export `get` missing; symbols: {names:?}"
        );
        for legacy in ["stream_new", "stream_write"] {
            assert!(
                !names.iter().any(|n| n.contains(legacy)),
                "{flags:?}: dead import `{legacy}` must emit no symbol; symbols: {names:?}"
            );
        }
        let relocs: usize = obj.sections().map(|s| s.relocations().count()).sum();
        assert_eq!(
            relocs, 0,
            "{flags:?}: a module with no live import needs no relocation"
        );
    }
}

/// Every LIVE shape must refuse with the classifier's exact #80 wording and
/// write no object.
fn assert_live_legacy_refused(tag: &str, body: &str) {
    let wat = write_wat(tag, &legacy_module(body));
    for flags in LEGACY_CONFIGS {
        let out = artifact_guard::unique_artifact(tag, "o");
        let o = legacy_compile(&wat, &out, flags)
            .output()
            .expect("run synth");
        let stderr = String::from_utf8_lossy(&o.stderr);
        assert!(
            !o.status.success(),
            "{tag} {flags:?}: a LIVE legacy import must refuse; stderr:\n{stderr}"
        );
        assert!(
            stderr.contains(STREAM_NEW_DECLINE),
            "{tag} {flags:?}: refusal must be the unchanged #80 decline; stderr:\n{stderr}"
        );
        assert!(
            !out.exists(),
            "{tag} {flags:?}: refused but wrote an object"
        );
    }
}

/// NEGATIVE (a): the legacy import is CALLED.
#[test]
fn called_legacy_async_import_keeps_the_80_decline() {
    assert_live_legacy_refused(
        "async_legacy_called",
        r#"(func (export "get") (result i32) call $stream_new i32.wrap_i64)"#,
    );
}

/// NEGATIVE (b): the legacy import sits in a TABLE via an active elem segment
/// (the meld#692 shape for `[async-lower]` built-ins, reached by
/// `call_indirect`).
#[test]
fn table_placed_legacy_async_import_keeps_the_80_decline() {
    assert_live_legacy_refused(
        "async_legacy_elem",
        r#"(table 1 1 funcref)
           (elem (i32.const 0) $stream_new)
           (func (export "get") (result i32) i32.const 7)"#,
    );
}

/// NEGATIVE (c): the legacy import is referenced by `ref.func`.
#[test]
fn ref_func_legacy_async_import_keeps_the_80_decline() {
    assert_live_legacy_refused(
        "async_legacy_ref_func",
        r#"(elem declare func $stream_new)
           (func (export "get") (result i32) ref.func $stream_new ref.is_null)"#,
    );
}

/// NEGATIVE (d): the legacy import is RE-EXPORTED.
#[test]
fn reexported_legacy_async_import_keeps_the_80_decline() {
    assert_live_legacy_refused(
        "async_legacy_reexport",
        r#"(export "sn" (func $stream_new))
           (func (export "get") (result i32) i32.const 7)"#,
    );
}
