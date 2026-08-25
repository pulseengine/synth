//! RQ-59-STARTFN (#1046) — every synth backend must REFUSE a module that
//! declares a `(start ...)` function, because none of them invokes it.
//!
//! Pre-fix behaviour (the filed bug): the decoder has NO
//! `Payload::StartSection` arm at all — the section falls through the
//! catch-all and is discarded outright. All three backends (ARM Thumb-2/A32,
//! RISC-V, AArch64) then compile the module, exit 0, and print no warning;
//! the start function is not even IN the object (reachability only walks
//! exports). wasmtime runs the start function at instantiation (WASM Core
//! §4.5.5) — `get() == 42` on the filed repro — while synth-compiled code
//! reads memory the start function was supposed to initialize and returns 0.
//! Third silent drop of the same shape in one session (#1041 data segments,
//! #1046 this, #1048 i64-shift operand).
//!
//! THE ASSERTION SHAPE IS THE POINT: this test asserts a clean NON-ZERO exit
//! plus a reason string NAMING THE START SECTION. It deliberately does NOT
//! assert "the start function was not called" — that was already true on the
//! broken behaviour and would make this test vacuously green. Every existing
//! test asserted what synth DOES; nothing asserted what it silently DIDN'T.
//!
//! Start-function INVOCATION (the self-contained Reset_Handler calling it
//! before any export, or an exported init hook on the relocatable contract)
//! is a capability question and explicitly NOT this fix (#1046 note (b)).

use std::path::PathBuf;
use std::process::Command;

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// Write an inline wat to a temp file and return its path.
fn wat_file(name: &str, wat: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("synth_start_1046_tests");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join(name);
    std::fs::write(&p, wat).expect("write wat");
    p
}

fn compile(input: &std::path::Path, extra: &[&str]) -> std::process::Output {
    let out = std::env::temp_dir()
        .join("synth_start_1046_tests")
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
/// start section (the multi_memory_406 house rule; the #851/#1041 shape).
fn assert_refused(out: &std::process::Output, must_mention: &[&str], ctx: &str) {
    assert!(
        !out.status.success(),
        "{ctx}: expected a loud refusal, got success (exit 0 is the #1046 \
         silent-drop bug — the (start ...) section was discarded and the \
         module compiled as if its instantiation-time init did not exist).\n\
         stderr: {}",
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

/// The filed #1046 repro: a start function that writes linear memory before
/// any export runs (wasmtime: get() == 42; pre-fix synth object: 0).
const START_WAT: &str = r#"(module
  (memory 1)
  (func $init (i32.const 0) (i32.const 42) i32.store)
  (start $init)
  (func (export "get") (result i32) i32.const 0 i32.load))"#;

/// ARM Thumb-2 `--relocatable` — the filed repro's primary path.
#[test]
fn start_on_arm_relocatable_refuses_loudly() {
    let f = wat_file("start_arm_reloc.wat", START_WAT);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) on ARM --relocatable",
    );
}

/// ARM self-contained Cortex-M image (no --relocatable) — the image has a
/// Reset_Handler that COULD call the start function one day; until it does,
/// it must refuse, not silently skip the init.
#[test]
fn start_on_arm_selfcontained_refuses_loudly() {
    let f = wat_file("start_arm_sc.wat", START_WAT);
    let out = compile(&f, &["--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) on ARM self-contained",
    );
}

/// A32 (cortex-r5) — the refusal is per-module, not per-encoding.
#[test]
fn start_on_a32_relocatable_refuses_loudly() {
    let f = wat_file("start_a32.wat", START_WAT);
    let out = compile(&f, &["--relocatable", "--target", "cortex-r5"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) on cortex-r5 --relocatable",
    );
}

/// RISC-V RV32IMAC.
#[test]
fn start_on_riscv_refuses_loudly() {
    let f = wat_file("start_rv32.wat", START_WAT);
    let out = compile(&f, &["-b", "riscv", "--target", "rv32imac"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) on RISC-V rv32imac",
    );
}

/// AArch64 host-native.
#[test]
fn start_on_aarch64_refuses_loudly() {
    let f = wat_file("start_a64.wat", START_WAT);
    let out = compile(&f, &["-b", "aarch64"]);
    assert_refused(&out, &["start function", "#1046"], "(start) on aarch64");
}

/// A start function that is ALSO exported must still refuse: nothing invokes
/// it at instantiation time, so exports called before the embedder happens to
/// call it still observe uninitialized state. (An explicit-init capability
/// story is #1046 note (b), not this fix.)
#[test]
fn exported_start_function_still_refuses() {
    let f = wat_file(
        "start_exported.wat",
        r#"(module
  (memory 1)
  (func $init (export "init") (i32.const 0) (i32.const 42) i32.store)
  (start $init)
  (func (export "get") (result i32) i32.const 0 i32.load))"#,
    );
    let out = compile(&f, &["--relocatable", "--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) naming an exported function",
    );
}

/// The single-function compile path (no --all-exports) decodes the module
/// too — the same silent drop lived there. Must refuse as well.
#[test]
fn start_on_single_function_path_refuses_loudly() {
    let f = wat_file("start_single.wat", START_WAT);
    let out_path = std::env::temp_dir()
        .join("synth_start_1046_tests")
        .join("start_single_fn.o");
    let out = Command::new(synth())
        .args([
            "compile",
            f.to_str().unwrap(),
            "--func-name",
            "get",
            "--relocatable",
            "--target",
            "cortex-m4",
            "-o",
            out_path.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) on the single-function path",
    );
}

/// NON-VACUITY CONTROL: the identical module WITHOUT the (start) declaration
/// must still compile on every backend the refusal covers — the guard keys on
/// the start section, not on the module shape around it.
#[test]
fn start_free_module_still_compiles_everywhere() {
    let f = wat_file(
        "no_start.wat",
        r#"(module
  (memory 1)
  (func $init (i32.const 0) (i32.const 42) i32.store)
  (func (export "get") (result i32) i32.const 0 i32.load))"#,
    );
    for (ctx, extra) in [
        (
            "ARM --relocatable",
            &["--relocatable", "--target", "cortex-m4"][..],
        ),
        ("ARM self-contained", &["--target", "cortex-m4"][..]),
        ("RISC-V", &["-b", "riscv", "--target", "rv32imac"][..]),
        ("aarch64", &["-b", "aarch64"][..]),
    ] {
        let out = compile(&f, extra);
        assert!(
            out.status.success(),
            "{ctx}: start-free control module must compile (exit 0), got \
             failure.\nstderr: {}",
            stderr(&out)
        );
    }
}
