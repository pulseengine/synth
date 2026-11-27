//! P3-BUILTINS I0 (Refs #1786, Refs #1046): `--embedder-runs-start`.
//!
//! #1046 refuses a module whose `(start ...)` function no synth output
//! invokes. It had no escape hatch, because the start function's code was not
//! in the relocatable object: there was nothing an embedder could call. Every
//! meld fused module declares a start function (`(start N)`, where N is also
//! exported as `_initialize`), so every one of them stopped there.
//!
//! The flag puts the code in the object and gives it a name: the start
//! function is a root of the compiled closure and is defined as the GLOBAL
//! `STT_FUNC` symbol `__synth_start`, and the embedder contract
//! (docs/embedder-abi-relocatable-arm.md) says the embedder calls it exactly
//! once, after setting R11/R10/R9 and before any export runs. That is the
//! instantiation step WASM Core §4.5.5 describes, moved to the side of the
//! contract that already owns R11/R10/R9, data segments and globals.
//!
//! This file pins the compile-side halves: the meld#692 fixture compiles with
//! the flag in both modes and refuses, with the unchanged #1046 wording,
//! without it; the symbol is where the start function is; and every place the
//! flag cannot be honoured refuses it. The EXECUTION half (calling
//! `__synth_start` then an export, against kiln, which runs the start function
//! at instantiation) is `crates/synth-oracle/tests/embedder_runs_start_oracle.rs`.

mod artifact_guard;

use std::path::{Path, PathBuf};
use std::process::Command;

use object::{Object, ObjectSymbol, SymbolKind};

fn synth_binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

/// The pulseengine/meld#692 fixture, meld 6aede1a
/// `fuse --memory multi --no-attestation --reproducible --emit-import-map`.
/// It declares `(start 5)`; function 5 is exported as `_initialize`.
fn meld692_fused() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("meld692_fused.wasm")
}

const MELD692_SHA256: &str = "1ef9b47047561655cca51e5b3c1bbdc261ee5a8059b9441151c6175d1590ad86";

/// The #1046 repro: a start function that stores 42, NOT exported.
const START_WAT: &str = r#"(module
  (memory 1)
  (func $init (i32.const 0) (i32.const 42) i32.store)
  (start $init)
  (func (export "get") (result i32) i32.const 0 i32.load))"#;

/// The two #1046 wordings the fixture hits without the flag, byte for byte.
const REFUSAL_1046_RELOCATABLE: &str = "module declares a start function (function index 5), \
     but no synth backend invokes it — the (start ...) section's instantiation-time \
     initialization (WASM Core §4.5.5: it runs before any export is callable) would \
     silently never run, and every export would read state the start function was \
     supposed to establish; refusing (#1046). Start-function invocation is a documented \
     capability follow-on; until it lands, remove the (start ...) section and perform \
     the initialization through an export your embedder calls first.";
const REFUSAL_1046_ET_REL: &str = "module declares a start function (function index 5), but \
     this compile produced a relocatable object (imported functions are host-linked) and no \
     startup runs in it — the (start ...) instantiation-time initialization (WASM Core \
     §4.5.5) would silently never run; refusing (#1046). The self-contained Cortex-M image \
     invokes the start function from its Reset_Handler; on the host-linked contract the \
     embedder must call it first, which this object does not yet expose.";

const FLAG: &str = "--embedder-runs-start";

fn write_wat(tag: &str, src: &str) -> PathBuf {
    let p = artifact_guard::unique_artifact(tag, "wat");
    std::fs::write(&p, src).expect("write wat");
    p
}

fn run(input: &Path, flags: &[&str], out: &Path) -> std::process::Output {
    Command::new(synth_binary())
        .arg("compile")
        .arg(input)
        .args(flags)
        .arg("-o")
        .arg(out)
        .output()
        .expect("run synth")
}

fn compile_ok(input: &Path, flags: &[&str], tag: &str) -> Vec<u8> {
    let out = artifact_guard::unique_artifact(tag, "o");
    let mut cmd = Command::new(synth_binary());
    cmd.arg("compile")
        .arg(input)
        .args(flags)
        .arg("-o")
        .arg(&out);
    artifact_guard::compile_bytes_or_panic(&mut cmd, &out, &format!("{flags:?} must compile"))
}

/// Refused: non-zero exit, no object written, and every needle in stderr.
fn assert_refused(input: &Path, flags: &[&str], needles: &[&str], tag: &str) {
    let out = artifact_guard::unique_artifact(tag, "o");
    let o = run(input, flags, &out);
    let err = String::from_utf8_lossy(&o.stderr);
    assert!(
        !o.status.success(),
        "{tag} {flags:?}: expected a refusal, got exit 0\nstderr: {err}"
    );
    assert!(
        !out.exists(),
        "{tag} {flags:?}: a refusal must not write an object"
    );
    for n in needles {
        assert!(
            err.contains(n),
            "{tag} {flags:?}: stderr lacks {n:?}\nstderr: {err}"
        );
    }
}

/// `(value, size, global)` of a `.text` function symbol.
fn func_sym(data: &[u8], name: &str) -> Option<(u64, u64, bool)> {
    let obj = object::File::parse(data).expect("parse object");
    obj.symbols()
        .filter(|s| s.kind() == SymbolKind::Text && s.name() == Ok(name))
        .map(|s| (s.address(), s.size(), s.is_global()))
        .max_by_key(|s| s.2)
}

fn is_et_rel(data: &[u8]) -> bool {
    object::File::parse(data).expect("parse object").kind() == object::ObjectKind::Relocatable
}

const FUSED_MODES: &[&[&str]] = &[
    &["-t", "cortex-m7", "--relocatable"],
    // A module that calls a function import is a relocatable object without
    // the flag too (#1696), so `--cortex-m` takes the same contract.
    &["-t", "cortex-m7", "--cortex-m"],
];

#[test]
fn meld692_fixture_is_the_pinned_bytes() {
    use sha2::{Digest, Sha256};
    let bytes = std::fs::read(meld692_fused()).expect("read fixture");
    let hex: String = Sha256::digest(&bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(hex, MELD692_SHA256);
}

/// RED-FIRST: on cc36ff38 the flag does not exist (clap rejects it) and the
/// fixture refuses with #1046 in both modes. With I0 it compiles, the object
/// is ET_REL, and `__synth_start` is a GLOBAL function at the address and size
/// of function 5 (exported as `_initialize`).
#[test]
fn meld692_fused_compiles_with_the_flag_and_defines_synth_start() {
    let input = meld692_fused();
    for mode in FUSED_MODES {
        let mut flags = mode.to_vec();
        flags.push(FLAG);
        let data = compile_ok(&input, &flags, "ers_meld692");
        assert!(is_et_rel(&data), "{flags:?}: expected an ET_REL object");
        let start = func_sym(&data, "__synth_start")
            .unwrap_or_else(|| panic!("{flags:?}: no `__synth_start` symbol"));
        assert!(start.2, "{flags:?}: `__synth_start` must be GLOBAL");
        let init = func_sym(&data, "_initialize")
            .unwrap_or_else(|| panic!("{flags:?}: no `_initialize` symbol"));
        assert_eq!(
            (start.0, start.1),
            (init.0, init.1),
            "{flags:?}: `__synth_start` must be function 5 (`_initialize`)"
        );
        // The other exports are unchanged by the flag.
        for e in ["0", "test:x/api#get"] {
            assert!(
                func_sym(&data, e).is_some_and(|s| s.2),
                "{flags:?}: export `{e}` missing"
            );
        }
    }
}

/// Without the flag nothing changes: the same two #1046 refusals, word for
/// word, exit 1, no object.
#[test]
fn meld692_fused_without_the_flag_keeps_the_1046_refusals() {
    let input = meld692_fused();
    assert_refused(
        &input,
        FUSED_MODES[0],
        &[REFUSAL_1046_RELOCATABLE],
        "ers_meld692_noflag_reloc",
    );
    assert_refused(
        &input,
        FUSED_MODES[1],
        &[REFUSAL_1046_ET_REL],
        "ers_meld692_noflag_cm",
    );
}

/// A start function that is NOT exported: its only other name is the
/// file-local `func_0` label, and the flag adds the GLOBAL `__synth_start` at
/// the same address. Also on A32 (cortex-r5), which shares the ARM
/// relocatable writer and this contract.
#[test]
fn unexported_start_gets_a_global_synth_start() {
    let wat = write_wat("ers_unexported", START_WAT);
    for target in ["cortex-m4", "cortex-m7", "cortex-r5"] {
        let data = compile_ok(
            &wat,
            &["-t", target, "--relocatable", FLAG],
            "ers_unexported",
        );
        let start = func_sym(&data, "__synth_start")
            .unwrap_or_else(|| panic!("{target}: no `__synth_start` symbol"));
        assert!(start.2, "{target}: `__synth_start` must be GLOBAL");
        let label = func_sym(&data, "func_0").expect("func_0 label");
        assert!(!label.2, "{target}: `func_0` stays file-local (#656)");
        assert_eq!((start.0, start.1), (label.0, label.1), "{target}");
        assert!(func_sym(&data, "get").is_some_and(|s| s.2), "{target}");
    }
    // And without the flag, the unchanged #1046 refusal.
    assert_refused(
        &wat,
        &["-t", "cortex-m4", "--relocatable"],
        &[
            "module declares a start function (function index 0)",
            "#1046",
        ],
        "ers_unexported_noflag",
    );
}

/// The self-contained Cortex-M image already invokes the start function from
/// its Reset_Handler (#1017). The flag would mean nothing there, so it is
/// refused; without it the image still compiles.
#[test]
fn flag_is_refused_on_a_self_contained_image() {
    let wat = write_wat("ers_selfcontained", START_WAT);
    assert_refused(
        &wat,
        &["-t", "cortex-m4", FLAG],
        &[FLAG, "self-contained", "Reset_Handler"],
        "ers_sc_m4",
    );
    // A32 self-contained: no startup invokes it either, and the flag cannot
    // add one. Refused with the same message.
    assert_refused(
        &wat,
        &["-t", "cortex-r5", FLAG],
        &[FLAG, "self-contained"],
        "ers_sc_r5",
    );
    // Control: the flagless self-contained image is unchanged (compiles).
    compile_ok(&wat, &["-t", "cortex-m4"], "ers_sc_m4_noflag");
}

/// No start section: the flag would define nothing for the embedder to call.
/// Refused, so an embedder written against the contract never links an
/// object that silently lacks the symbol it calls.
#[test]
fn flag_is_refused_without_a_start_section() {
    let wat = write_wat(
        "ers_nostart",
        r#"(module (memory 1) (func (export "get") (result i32) i32.const 0 i32.load))"#,
    );
    assert_refused(
        &wat,
        &["-t", "cortex-m4", "--relocatable", FLAG],
        &[FLAG, "no start function"],
        "ers_nostart",
    );
}

/// An imported start function has no body in this object.
#[test]
fn flag_is_refused_for_an_imported_start_function() {
    let wat = write_wat(
        "ers_imported",
        r#"(module
  (import "env" "init" (func $init))
  (memory 1)
  (start $init)
  (func (export "get") (result i32) i32.const 0 i32.load))"#,
    );
    assert_refused(
        &wat,
        &["-t", "cortex-m4", "--relocatable", FLAG],
        &[FLAG, "imported"],
        "ers_imported",
    );
}

/// RV32 and AArch64 objects are relocatable too, but their contracts (the
/// generated `synth riscv-runtime` startup; docs/embedder-abi-relocatable-aarch64.md)
/// say nothing about a start symbol. Refused there, so behaviour stays
/// exactly the #1046 refusal it was.
#[test]
fn flag_is_refused_off_the_arm_backend() {
    let wat = write_wat("ers_offarm", START_WAT);
    assert_refused(
        &wat,
        &["-b", "riscv", "--relocatable", FLAG],
        &[FLAG, "riscv"],
        "ers_rv32",
    );
    assert_refused(
        &wat,
        &["-b", "aarch64", FLAG],
        &[FLAG, "aarch64"],
        "ers_a64",
    );
    // Control: without the flag both keep the #1046 refusal.
    for flags in [
        &["-b", "riscv", "--relocatable"][..],
        &["-b", "aarch64"][..],
    ] {
        assert_refused(
            &wat,
            flags,
            &["module declares a start function", "#1046"],
            "ers_offarm_noflag",
        );
    }
}

/// The single-function path compiles one root; the start function is not
/// part of it. Refused with and without `--relocatable`.
#[test]
fn flag_is_refused_on_the_single_function_path() {
    let wat = write_wat("ers_single", START_WAT);
    for flags in [
        &["-t", "cortex-m4", "--func-name", "get", FLAG][..],
        &[
            "-t",
            "cortex-m4",
            "--func-name",
            "get",
            "--relocatable",
            FLAG,
        ][..],
    ] {
        assert_refused(&wat, flags, &[FLAG, "single-function"], "ers_single");
    }
}

/// A start function the backend declines (here a SIMD load, #680) would ship
/// an object without the `__synth_start` the embedder is obliged to call.
/// Refused, and `--allow-skipped-exports` does not waive it: that flag
/// accepts a missing entry point, never a missing instantiation step.
#[test]
fn a_declined_start_function_is_refused_even_with_allow_skipped_exports() {
    let wat = write_wat(
        "ers_declined",
        r#"(module
  (memory 1)
  (func $init (drop (v128.load (i32.const 0))))
  (start $init)
  (func (export "get") (result i32) i32.const 0 i32.load))"#,
    );
    for extra in [&[][..], &["--allow-skipped-exports"][..]] {
        let mut flags = vec!["-t", "cortex-m4", "--relocatable", FLAG];
        flags.extend_from_slice(extra);
        assert_refused(
            &wat,
            &flags,
            &[FLAG, "was not compiled", "__synth_start"],
            "ers_declined",
        );
    }
}
