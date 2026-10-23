//! RQ-89-MEM64 (#1582) — an imported memory 0 beside any other memory is
//! refused everywhere except ARM `--relocatable`.
//!
//! The #406 multi-memory gate counted only DEFINED memories, so
//! `(import "env" "m0" (memory 1 1)) (memory 2 2)` looked like one memory and
//! memory 0 took the defined memory 1's size. Measured on v0.88 against
//! wasmtime: `memory.size 0` returned 2 instead of 1 on self-contained
//! Cortex-M, on RV32, on AArch64, and on the single-function path. Under bounds
//! checking (ARM `--safety-bounds software`, the AArch64 default), accesses in
//! [64 KiB, 128 KiB) returned data where wasmtime traps.
//!
//! RED-FIRST: on the v0.88 binary `imported_plus_defined_refused_1582` fails on
//! every leg (rc=0). The control tests pass on both binaries, so the refusal
//! cannot widen to imported-only, defined-only, two-defined or the relocatable
//! path without turning one of them red.

use std::process::Command;

const IMPORTED_PLUS_DEFINED: &str = r#"(module
  (import "env" "m0" (memory 1 1))
  (memory 2 2)
  (func (export "size0") (result i32) (memory.size 0))
  (func (export "peek0") (param i32) (result i32) (i32.load8_u 0 (local.get 0))))"#;

const IMPORTED_ONLY: &str = r#"(module
  (import "env" "m0" (memory 1 1))
  (func (export "size0") (result i32) (memory.size 0))
  (func (export "peek0") (param i32) (result i32) (i32.load8_u 0 (local.get 0))))"#;

const DEFINED_ONLY: &str = r#"(module
  (memory 1 1)
  (func (export "size0") (result i32) (memory.size 0))
  (func (export "peek0") (param i32) (result i32) (i32.load8_u 0 (local.get 0))))"#;

const TWO_DEFINED: &str = r#"(module
  (memory 1 1)
  (memory 2 2)
  (func (export "size0") (result i32) (memory.size 0))
  (func (export "peek0") (param i32) (result i32) (i32.load8_u 0 (local.get 0))))"#;

/// The paths that size memory 0 from the module. ARM `--relocatable` is
/// deliberately absent; the embedder supplies memory 0's size there.
const SIZED_LEGS: &[(&str, &[&str])] = &[
    (
        "cm4-self",
        &["--all-exports", "--cortex-m", "-t", "cortex-m4"],
    ),
    (
        "cm4-self-sw",
        &[
            "--all-exports",
            "--cortex-m",
            "-t",
            "cortex-m4",
            "--safety-bounds",
            "software",
        ],
    ),
    ("rv32", &["--all-exports", "-b", "riscv"]),
    ("aarch64", &["--all-exports", "-b", "aarch64"]),
    (
        "single-fn-cm4",
        &["-n", "size0", "--cortex-m", "-t", "cortex-m4"],
    ),
    ("single-fn-rv32", &["-n", "size0", "-b", "riscv"]),
    ("single-fn-aarch64", &["-n", "size0", "-b", "aarch64"]),
];

const RELOCATABLE: &[&str] = &["--all-exports", "-t", "cortex-m4", "--relocatable"];

fn run(tag: &str, wat: &str, flags: &[&str]) -> (bool, String) {
    let dir = std::env::temp_dir().join(format!("synth-memidx-1582-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let src = dir.join(format!("{tag}.wat"));
    std::fs::write(&src, wat).expect("write fixture");
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(&src)
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

#[test]
fn imported_plus_defined_refused_1582() {
    let mut failures = Vec::new();
    for (leg, flags) in SIZED_LEGS {
        let (ok, text) = run(&format!("mixed-{leg}"), IMPORTED_PLUS_DEFINED, flags);
        let named = text.contains("#1582") && text.contains("`env`.`m0`");
        if ok || !named {
            failures.push(format!(
                "{leg}: rc_ok={ok}, #1582 refusal naming the import={named}\n{}",
                text.lines().rev().take(3).collect::<Vec<_>>().join("\n")
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "imported memory 0 + defined memory 1 was not refused on {} of {} legs:\n{}",
        failures.len(),
        SIZED_LEGS.len(),
        failures.join("\n---\n")
    );
}

/// Unchanged: the embedder supplies memory 0's size on ARM --relocatable, which
/// was measured correct (`memory.size 0` = 1).
#[test]
fn imported_plus_defined_still_compiles_relocatable() {
    let (ok, text) = run("mixed-reloc", IMPORTED_PLUS_DEFINED, RELOCATABLE);
    assert!(ok, "the ARM --relocatable leg must be unchanged:\n{text}");
}

#[test]
fn single_memory_controls_still_compile() {
    for (name, wat) in [
        ("imported-only", IMPORTED_ONLY),
        ("defined-only", DEFINED_ONLY),
    ] {
        for (leg, flags) in SIZED_LEGS {
            let (ok, text) = run(&format!("{name}-{leg}"), wat, flags);
            assert!(ok, "{name} on {leg} must still compile:\n{text}");
            assert!(
                !text.contains("#1582"),
                "{name} on {leg}: the #1582 refusal fired on a single memory:\n{text}"
            );
        }
    }
}

/// Two DEFINED memories keep their existing #406 refusal on the self-contained
/// path, not the new one.
#[test]
fn two_defined_memories_keep_the_406_refusal() {
    let (ok, text) = run("two-defined-self", TWO_DEFINED, SIZED_LEGS[0].1);
    assert!(!ok, "two defined memories compiled self-contained:\n{text}");
    assert!(
        text.contains("multi-memory (#406)") && !text.contains("#1582"),
        "two defined memories must keep the #406 diagnostic:\n{text}"
    );
    let (ok, text) = run("two-defined-reloc", TWO_DEFINED, RELOCATABLE);
    assert!(
        ok,
        "two defined memories on --relocatable must still compile:\n{text}"
    );
}
