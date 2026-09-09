//! RQ-59-STARTFN (#1046) — every synth backend must REFUSE a module that
//! declares a `(start ...)` function, because none of them invokes it —
//! EXCEPT, since RQ-65-MVPCORE (#1017, v0.65), the self-contained ARM
//! Cortex-M image, whose Reset_Handler now invokes it (see
//! `start_on_arm_selfcontained_is_invoked_from_reset_handler` below); every
//! other path keeps the refusal and this file pins both halves.
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
//! Start-function INVOCATION was a capability question explicitly NOT the
//! #1046 fix (note (b)). The self-contained Reset_Handler half landed in
//! v0.65 (a `BL` after the data copy and the R9 table, before the entry
//! `BLX r0`; execution-gated by the selector-parity oracle over start.wast);
//! the exported init hook on the relocatable contract has not, so
//! `--relocatable`, an ET_REL degradation via imports, an IMPORTED start
//! function, the single-function path, A32, RISC-V and AArch64 still refuse.

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

/// ARM self-contained Cortex-M image (no --relocatable) — RQ-65-MVPCORE
/// (#1017), the #1046 capability follow-on: the image's Reset_Handler IS the
/// instantiation step, and it now invokes the start function (a `BL` after
/// the data copy and the R9 table, before the entry `BLX r0`). The compile
/// must succeed and the startup must carry that call; the EXECUTION proof —
/// `get` observing what `$init` stored — is the selector-parity oracle over
/// start.wast (`scripts/repro/selector_parity_197_differential.py`, which
/// boots this very startup under unicorn and was red on the compiler that
/// refused start modules). This test pins the SHAPE so a regression to the
/// refusal, or a startup that stops calling, fails without the emulator.
#[test]
fn start_on_arm_selfcontained_is_invoked_from_reset_handler() {
    let f = wat_file("start_arm_sc.wat", START_WAT);
    let out = compile(&f, &["--target", "cortex-m4"]);
    assert!(
        out.status.success(),
        "(start) on ARM self-contained must compile (#1017):\n{}",
        stderr(&out)
    );
    let elf = std::env::temp_dir()
        .join("synth_start_1046_tests")
        .join("start_arm_sc_targetcortexm4.o");
    let dis = Command::new(synth())
        .args(["disasm", elf.to_str().unwrap()])
        .output()
        .expect("run synth disasm");
    let text =
        String::from_utf8_lossy(&dis.stdout).to_string() + &String::from_utf8_lossy(&dis.stderr);
    let reset = text
        .find("<Reset_Handler>:")
        .expect("disasm names Reset_Handler");
    let after = text[reset..]
        .find("<Default_Handler>:")
        .map(|i| reset + i)
        .unwrap_or(text.len());
    let startup = &text[reset..after];
    // `$init` is function index 0 and is NOT exported, so it ships as `func_0`;
    // the startup's BL must target it, and it must sit BEFORE the entry BLX.
    let bl = startup
        .find("bl\t")
        .or_else(|| startup.find("bl "))
        .unwrap_or_else(|| panic!("Reset_Handler carries no BL to the start function:\n{startup}"));
    let blx = startup
        .find("blx\tr0")
        .or_else(|| startup.find("blx r0"))
        .unwrap_or_else(|| panic!("Reset_Handler carries no entry BLX r0:\n{startup}"));
    assert!(
        bl < blx,
        "the start BL must precede the entry BLX r0 (instantiation before any export):\n{startup}"
    );
    assert!(
        startup[bl..blx].contains("func_0"),
        "the start BL must target func_0 (the (start $init) body):\n{startup}"
    );
    assert!(
        text.contains("<func_0>:"),
        "the start function body must be in the image (closure seeded with it):\n{text}"
    );
}

/// A start function that is IMPORTED has no body in the image — the
/// self-contained path must still refuse (nothing to BL).
#[test]
fn imported_start_on_arm_selfcontained_still_refuses() {
    let f = wat_file(
        "start_arm_sc_imported.wat",
        r#"(module
  (import "env" "init" (func $init))
  (memory 1)
  (start $init)
  (func (export "get") (result i32) i32.const 0 i32.load))"#,
    );
    let out = compile(&f, &["--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start $imported) on ARM self-contained",
    );
}

/// A module whose OTHER imports degrade the self-contained compile to a
/// host-linked ET_REL object has no Reset_Handler — the accepted start would
/// silently never run, so it must refuse after compilation, where that is
/// known.
#[test]
fn start_with_imports_degrading_to_relocatable_still_refuses() {
    let f = wat_file(
        "start_arm_sc_degraded.wat",
        r#"(module
  (import "env" "host" (func $host (param i32)))
  (memory 1)
  (func $init (i32.const 0) (i32.const 42) i32.store)
  (start $init)
  (func (export "get") (result i32) (call $host (i32.const 1)) i32.const 0 i32.load))"#,
    );
    let out = compile(&f, &["--target", "cortex-m4"]);
    assert_refused(
        &out,
        &["start function", "#1046"],
        "(start) with host imports on --target cortex-m4 (ET_REL degradation)",
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
