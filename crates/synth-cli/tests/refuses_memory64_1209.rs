//! RQ-89-MEM64 (#1209) — a 64-bit-indexed memory is refused on every backend,
//! whether the module DEFINES it or IMPORTS it.
//!
//! The defined case has been refused since v0.66 (`refuse_memory64_module`,
//! RQ-66-BOTHWRONG) but had no cargo test of its own; the two `defined_*`
//! tests below are REGRESSION GUARDS and pass on v0.88 as well.
//!
//! The imported case is the v0.89 finding. The decoder discarded an imported
//! memory's type, so `(import "env" "mem" (memory i64 1))` never reached the
//! refusal. Measured on v0.88.0 (0161dee1): the imported shapes compiled rc=0
//! on 13 of 21 backend legs. A booted self-contained Cortex-M image read 0
//! from an `(i64.const 16)` data segment that wasmtime reads as 42 (both
//! selectors; the i32-memory twin reads 42). Under `--safety-bounds software`,
//! a store to i64 address `0x1_0000_0008` landed at offset 8 instead of
//! trapping, on all four ARM legs.
//!
//! RED-FIRST: on the v0.88.0 binary every `imported_*` test below fails, either
//! because the compile succeeds or because the error names something else.
//! `imported_i32_memory_still_compiles` passes on both. It is the negative
//! control that stops this from turning into "refuse imported memories".

use std::process::Command;

const DEFINED_DATA: &str = r#"(module
  (memory i64 1)
  (data (i64.const 16) "\2a\00\00\00")
  (func (export "get") (result i32) (i32.load (i64.const 16))))"#;

const DEFINED_NO_DATA: &str = r#"(module
  (memory i64 1)
  (func (export "ld") (param i64) (result i32) (i32.load (local.get 0))))"#;

const IMPORTED_DATA: &str = r#"(module
  (import "env" "mem" (memory i64 1))
  (data (i64.const 16) "\2a\00\00\00")
  (func (export "get") (result i32) (i32.load (i64.const 16))))"#;

const IMPORTED_NO_DATA: &str = r#"(module
  (import "env" "mem" (memory i64 1))
  (func (export "stld") (param i64 i32) (result i32)
    (i32.store (local.get 0) (local.get 1))
    (i32.load (i64.const 8))))"#;

const IMPORTED_I32: &str = r#"(module
  (import "env" "mem" (memory 1))
  (func (export "ld") (param i32) (result i32) (i32.load (local.get 0))))"#;

/// Every backend leg that accepts an imported memory at all. RV32 and AArch64
/// refuse some of these shapes for unrelated reasons on v0.88; the refusal
/// must fire FIRST and name memory64 on all of them.
const LEGS: &[(&str, &[&str])] = &[
    ("cm4-self", &["--cortex-m", "-t", "cortex-m4"]),
    (
        "cm4-self-noopt",
        &["--cortex-m", "-t", "cortex-m4", "--no-optimize"],
    ),
    ("cm4-reloc", &["-t", "cortex-m4", "--relocatable"]),
    (
        "cm4-reloc-sw",
        &[
            "-t",
            "cortex-m4",
            "--relocatable",
            "--safety-bounds",
            "software",
        ],
    ),
    ("r5", &["-t", "cortex-r5"]),
    ("rv32", &["-b", "riscv"]),
    ("rv32-reloc", &["-b", "riscv", "--relocatable"]),
    ("aarch64", &["-b", "aarch64"]),
];

fn run(tag: &str, wat: &str, flags: &[&str]) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("synth-mem64-1209-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let src = dir.join(format!("{tag}.wat"));
    std::fs::write(&src, wat).expect("write fixture");
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(&src)
        .arg("--all-exports")
        .arg("-o")
        .arg(dir.join(format!("{tag}.o")))
        .args(flags)
        .output()
        .expect("synth runs");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

/// `needle` is `"declares memory 0"` or `"imports memory 0"`. The diagnostic
/// must say which way the memory arrived, that it is 64-bit-indexed, and cite
/// #1209.
fn assert_refused_everywhere(case: &str, wat: &str, needle: &str) {
    let mut failures = Vec::new();
    for (leg, flags) in LEGS {
        let tag = format!("{case}-{leg}");
        let (ok, text) = run(&tag, wat, flags);
        let named = text.contains(&format!("{needle} as 64-bit-indexed"))
            && text.contains("memory64")
            && text.contains("#1209");
        if ok || !named {
            failures.push(format!(
                "{leg}: rc_ok={ok}, memory64 refusal named={named}\n{}",
                text.lines().rev().take(3).collect::<Vec<_>>().join("\n")
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{case}: memory64 was not refused loudly on {} of {} legs:\n{}",
        failures.len(),
        LEGS.len(),
        failures.join("\n---\n")
    );
}

#[test]
fn defined_memory64_with_i64_data_segment_refused_1209() {
    assert_refused_everywhere("defined-data", DEFINED_DATA, "declares memory 0");
}

#[test]
fn defined_memory64_without_data_refused_1209() {
    assert_refused_everywhere("defined-nodata", DEFINED_NO_DATA, "declares memory 0");
}

#[test]
fn imported_memory64_with_i64_data_segment_refused_1209() {
    assert_refused_everywhere("imported-data", IMPORTED_DATA, "imports memory 0");
}

#[test]
fn imported_memory64_without_data_refused_1209() {
    assert_refused_everywhere("imported-nodata", IMPORTED_NO_DATA, "imports memory 0");
}

/// Negative control. An imported 32-bit memory is the ordinary embedder shape
/// and must keep compiling on the ARM legs. Without this test the refusal could
/// widen to every import and still pass the tests above.
#[test]
fn imported_i32_memory_still_compiles() {
    for (leg, flags) in &LEGS[..5] {
        let (ok, text) = run(&format!("imported-i32-{leg}"), IMPORTED_I32, flags);
        assert!(
            ok,
            "{leg}: an imported i32 memory must still compile:\n{text}"
        );
        assert!(
            !text.contains("64-bit-indexed"),
            "{leg}: the memory64 refusal fired on an i32 memory:\n{text}"
        );
    }
}
