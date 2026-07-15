//! #406 (VCR-MEM-002 phase 1) — multi-memory capability matrix.
//!
//! N wasm linear memories lower to N DISTINCT native base regions on the ARM
//! `--relocatable` path: memory 0 keeps the runtime R11 base (single-memory
//! lowering untouched — the frozen byte gate pins that), memory k > 0 is
//! addressed via its own `__synth_wasm_data_<k>` symbol at the base of a
//! per-memory `.synth.wasm_mem_<k>` reservation section.
//!
//! Everything OUTSIDE that lane must decline LOUDLY (typed, precise), never
//! silently alias every memory onto one base (the pre-#406 bug):
//!
//! | shape                                  | verdict                        |
//! |----------------------------------------|--------------------------------|
//! | 2 memories, ARM `--relocatable`        | GREEN (execution differential) |
//! | 3 memories, ARM `--relocatable`        | GREEN (generic over K)         |
//! | multi-memory, no `--relocatable`       | refuse (one R11 base)          |
//! | multi-memory, self-contained --cortex-m| refuse (same)                  |
//! | multi-memory × `--native-pointer-abi`  | refuse (static region is mem-0)|
//! | multi-memory × `--shadow-stack-size`   | refuse (shrinks mem-0 geometry)|
//! | multi-memory on riscv / aarch64        | refuse (no per-memory base)    |
//! | cross-/non-default memory.copy/fill    | loud-skip naming the op        |
//! | i64/f32 access on memory k > 0         | loud-skip (i32 family only)    |
//! | non-const data-segment offset on mem k | refuse at decode               |
//!
//! Execution ground truth: `scripts/repro/multi_memory_406_differential.py`
//! (unicorn two-region mapping vs wasmtime multi-memory).

use std::path::PathBuf;
use std::process::Command;

use object::{Object, ObjectSection, ObjectSymbol, SectionKind};

fn synth() -> &'static str {
    env!("CARGO_BIN_EXE_synth")
}

/// The differential's fixture — 2 memories, init data on memory 1.
fn two_mem_fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("scripts/repro/mem406_multi_memory.wat")
}

/// Write an inline wat to a temp file and return its path.
fn wat_file(name: &str, wat: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("synth_mem406_tests");
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join(name);
    std::fs::write(&p, wat).expect("write wat");
    p
}

fn compile(input: &std::path::Path, extra: &[&str]) -> std::process::Output {
    let out = std::env::temp_dir()
        .join("synth_mem406_tests")
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

/// A refusal must be loud AND precise: nonzero exit + names multi-memory/#406.
fn assert_refused(out: &std::process::Output, must_mention: &[&str], ctx: &str) {
    assert!(
        !out.status.success(),
        "{ctx}: expected a loud refusal, got success.\nstderr: {}",
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

// ---------------------------------------------------------------------------
// GREEN lane
// ---------------------------------------------------------------------------

/// 2 memories on ARM --relocatable: per-memory region + symbol, init data
/// placed. (Execution equivalence is the python differential's job.)
#[test]
fn two_memories_relocatable_green() {
    let out = compile(
        &two_mem_fixture(),
        &["--relocatable", "--target", "cortex-m3"],
    );
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let bytes = std::fs::read(
        std::env::temp_dir()
            .join("synth_mem406_tests/mem406_multi_memory_relocatabletargetcortexm3.o"),
    )
    .expect("read object");
    let obj = object::File::parse(&*bytes).expect("parse ELF");

    // Memory 1's region: PROGBITS (has an init segment), exactly 3 pages,
    // segment bytes placed at offset 16.
    let mem1 = obj
        .section_by_name(".synth.wasm_mem_1")
        .expect("memory 1 reservation section");
    assert_eq!(mem1.size(), 3 * 65536, "3 declared pages");
    let data = mem1.data().expect("progbits data");
    assert_eq!(
        &data[16..24],
        b"\xaa\xbb\xcc\xdd\x11\x22\x33\x44",
        "init segment placed at its offset"
    );

    // Its base symbol is DEFINED and points at that section.
    let sym = obj
        .symbols()
        .find(|s| s.name() == Ok("__synth_wasm_data_1"))
        .expect("__synth_wasm_data_1 defined");
    assert!(!sym.is_undefined(), "must be a defined region base");
    assert_eq!(sym.address(), 0, "base of the section");

    // Memory 0 keeps the historical addressing: NO __synth_wasm_data_0 alias.
    assert!(
        !obj.symbols().any(|s| s.name() == Ok("__synth_wasm_data_0")),
        "memory 0 keeps the R11/legacy contract — no _0 symbol"
    );
}

/// 3 memories: generic over K — memory 1 (pure zero-init) ships NOBITS,
/// memory 2 (init segment) ships PROGBITS, each under its own symbol.
#[test]
fn three_memories_relocatable_green() {
    let wat = r#"(module
      (memory $a 1 1)
      (memory $b 2 2)
      (memory $c 1 1)
      (data (memory $c) (i32.const 8) "\01\02\03\04")
      (func (export "xfer") (param $p i32) (result i32)
        (i32.store $b (local.get $p) (i32.load $c offset=8 (local.get $p)))
        (i32.load $b (local.get $p))))"#;
    let f = wat_file("three_mem.wat", wat);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m3"]);
    assert!(out.status.success(), "stderr: {}", stderr(&out));
    let bytes = std::fs::read(
        std::env::temp_dir().join("synth_mem406_tests/three_mem_relocatabletargetcortexm3.o"),
    )
    .expect("read object");
    let obj = object::File::parse(&*bytes).expect("parse ELF");

    let mem1 = obj
        .section_by_name(".synth.wasm_mem_1")
        .expect("mem 1 region");
    assert_eq!(mem1.size(), 2 * 65536);
    assert_eq!(
        mem1.kind(),
        SectionKind::UninitializedData,
        "zero-init memory ships NOBITS (no flash cost)"
    );
    let mem2 = obj
        .section_by_name(".synth.wasm_mem_2")
        .expect("mem 2 region");
    assert_eq!(mem2.size(), 65536);
    assert_eq!(&mem2.data().expect("progbits")[8..12], b"\x01\x02\x03\x04");

    for name in ["__synth_wasm_data_1", "__synth_wasm_data_2"] {
        assert!(
            obj.symbols()
                .any(|s| s.name() == Ok(name) && !s.is_undefined()),
            "{name} must be defined"
        );
    }
}

// ---------------------------------------------------------------------------
// Decline matrix
// ---------------------------------------------------------------------------

/// No --relocatable ⇒ one runtime base (R11) ⇒ refuse the whole module.
#[test]
fn multi_memory_without_relocatable_refuses() {
    let out = compile(&two_mem_fixture(), &["--target", "cortex-m3"]);
    assert_refused(
        &out,
        &["multi-memory", "#406", "--relocatable"],
        "plain object path",
    );
}

/// Self-contained --cortex-m image: same single-base refusal.
#[test]
fn multi_memory_self_contained_cortex_m_refuses() {
    let out = compile(&two_mem_fixture(), &["--cortex-m"]);
    assert_refused(&out, &["multi-memory", "#406"], "self-contained --cortex-m");
}

/// --native-pointer-abi: the static-region classification is memory-0-only.
#[test]
fn multi_memory_native_pointer_abi_refuses() {
    let out = compile(
        &two_mem_fixture(),
        &[
            "--relocatable",
            "--native-pointer-abi",
            "--target",
            "cortex-m3",
        ],
    );
    assert_refused(
        &out,
        &["multi-memory", "#406", "--native-pointer-abi"],
        "native-pointer ABI",
    );
}

/// --shadow-stack-size shrinks MEMORY 0's reservation geometry — undefined
/// for a multi-memory module in phase 1.
#[test]
fn multi_memory_shadow_stack_refuses() {
    let out = compile(
        &two_mem_fixture(),
        &[
            "--relocatable",
            "--native-pointer-abi",
            "--shadow-stack-size",
            "2048",
            "--target",
            "cortex-m3",
        ],
    );
    // The native-pointer-abi gate may fire first — either way it must be a
    // loud multi-memory refusal, and the flag combo must never compile.
    assert_refused(&out, &["multi-memory", "#406"], "--shadow-stack-size combo");
}

/// riscv / aarch64: no per-memory base lowering — refuse the module.
#[test]
fn multi_memory_riscv_refuses() {
    let out = compile(&two_mem_fixture(), &["-b", "riscv", "--relocatable"]);
    assert_refused(&out, &["multi-memory", "#406", "riscv"], "riscv backend");
}

#[test]
fn multi_memory_aarch64_refuses() {
    let out = compile(&two_mem_fixture(), &["-b", "aarch64", "--relocatable"]);
    assert_refused(
        &out,
        &["multi-memory", "#406", "aarch64"],
        "aarch64 backend",
    );
}

/// Cross-memory memory.copy has no phase-1 lowering: the function loud-skips
/// naming the op, and a module with only that export fails (never a silent
/// memory-0 copy).
#[test]
fn cross_memory_copy_loud_skips() {
    let wat = r#"(module
      (memory $a 1 1)
      (memory $b 1 1)
      (func (export "xcopy") (param $d i32) (param $s i32) (param $n i32)
        (memory.copy $b $a (local.get $d) (local.get $s) (local.get $n))))"#;
    let f = wat_file("cross_copy.wat", wat);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m3"]);
    assert_refused(&out, &["memory.copy", "#406"], "cross-memory memory.copy");
}

/// memory.fill on a non-default memory: same loud-skip contract.
#[test]
fn non_default_memory_fill_loud_skips() {
    let wat = r#"(module
      (memory $a 1 1)
      (memory $b 1 1)
      (func (export "fill1") (param $d i32) (param $v i32) (param $n i32)
        (memory.fill $b (local.get $d) (local.get $v) (local.get $n))))"#;
    let f = wat_file("fill1.wat", wat);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m3"]);
    assert_refused(&out, &["memory.fill", "#406"], "non-default memory.fill");
}

/// Phase-1 scope is the i32 access family: an i64 access on memory k > 0
/// loud-skips its function (never aliases or truncates).
#[test]
fn wide_access_on_non_default_memory_loud_skips() {
    let wat = r#"(module
      (memory $a 1 1)
      (memory $b 1 1)
      (func (export "w") (param $p i32) (result i64)
        (i64.load $b (local.get $p))))"#;
    let f = wat_file("wide1.wat", wat);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m3"]);
    assert_refused(&out, &["#406"], "i64 access on memory 1");
    assert!(
        stderr(&out).contains("i32 load/store family"),
        "must name the phase-1 scope.\nstderr: {}",
        stderr(&out)
    );
}

/// An active data segment on memory k > 0 with a NON-constant offset cannot
/// be placed at compile time — refuse at decode, never ship memory k
/// uninitialized.
#[test]
fn non_const_segment_offset_on_memory_k_refuses() {
    let wat = r#"(module
      (import "env" "off" (global $off i32))
      (memory $a 1 1)
      (memory $b 1 1)
      (data (memory $b) (global.get $off) "\aa\bb")
      (func (export "f") (param $p i32) (result i32)
        (i32.load $b (local.get $p))))"#;
    let f = wat_file("nonconst_seg.wat", wat);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m3"]);
    assert_refused(
        &out,
        &["multi-memory", "#406", "non-constant offset"],
        "non-const segment offset",
    );
}

/// A segment overflowing memory k's declared size would trap at
/// instantiation — refuse rather than truncate.
#[test]
fn segment_overflowing_memory_k_refuses() {
    let wat = r#"(module
      (memory $a 1 1)
      (memory $b 1 1)
      (data (memory $b) (i32.const 65532) "\01\02\03\04\05\06\07\08")
      (func (export "f") (param $p i32) (result i32)
        (i32.load $b (local.get $p))))"#;
    let f = wat_file("overflow_seg.wat", wat);
    let out = compile(&f, &["--relocatable", "--target", "cortex-m3"]);
    assert_refused(
        &out,
        &["multi-memory", "#406", "overflows"],
        "overflowing segment",
    );
}
