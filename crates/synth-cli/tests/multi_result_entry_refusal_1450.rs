//! #1450 — a multi-result function that is an ENTRY POINT is refused.
//!
//! Measured on main 6641efec, every compile below exited 0:
//!
//! ```wat
//! (func (export "two") (param i32) (result i32 i32)
//!   local.get 0 i32.const 3 i32.mul
//!   local.get 0 i32.const 5 i32.mul)
//! ```
//!
//! With x = 7 wasm returns (21, 35). cortex-m4 (the default image and
//! `--relocatable`) returned `r0 = 35`; RV32 ended in `mv a0, t3` (x*5, the
//! first result left in t2); AArch64 ended in `mov x0, x10` (x*5, the first
//! result discarded); cortex-m7dp `(result f32 f32)` returned the second
//! result in `s0`. No backend defines a multi-value return convention, so
//! there is nothing for those bytes to be right against, and the object is
//! now refused.
//!
//! What is refused: a function with more than one result that is exported,
//! that is in a table and gets compiled, or that a single-function compile
//! names. What is NOT: a multi-result function that is unexported and
//! uncalled (it is not emitted), and one that sits in a table nothing
//! dispatches through (same). An in-module CALL of one is refused at the call
//! site by an older rule (RQ-91-MVDROP on ARM, #871 on RV32, #851 on
//! AArch64), which this test does not re-pin.
//!
//! Exit codes and synth's own stderr only — never disassembly text, which is
//! host-dependent. That the single-result control also EXECUTES correctly is
//! `crates/synth-oracle/tests/multi_result_export_1450_oracle.rs`.

use std::path::PathBuf;
use std::process::{Command, Output};

const NEEDLE: &str = "MULTI-RESULT function";
const ISSUE: &str = "#1450";

/// The issue's integer shape.
const EXPORTED_I32_PAIR: &str = r#"(module
  (func (export "two") (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul))
"#;

/// The issue's float shape (cortex-m7dp).
const EXPORTED_F32_PAIR: &str = r#"(module
  (func (export "two") (param f32) (result f32 f32)
    local.get 0 f32.const 2 f32.mul
    local.get 0 f32.const 3 f32.mul))
"#;

/// PAIRED CONTROL: the same two computations, one result each.
const SINGLE_RESULTS: &str = r#"(module
  (func (export "first") (param i32) (result i32) local.get 0 i32.const 3 i32.mul)
  (func (export "second") (param i32) (result i32) local.get 0 i32.const 5 i32.mul))
"#;

/// The multi-result function is unexported and uncalled.
const UNEXPORTED_UNCALLED: &str = r#"(module
  (func $two (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul)
  (func (export "one") (param i32) (result i32) local.get 0 i32.const 3 i32.mul))
"#;

/// In a table, but no function dispatches through the table, so it is not
/// compiled.
const IN_TABLE_NO_DISPATCH: &str = r#"(module
  (table 1 funcref)
  (elem (i32.const 0) $two)
  (func $two (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul)
  (func (export "one") (param i32) (result i32) local.get 0 i32.const 3 i32.mul))
"#;

/// In a table that an export dispatches through: the table's functions are
/// compiled. The dispatch type is the SINGLE-result one, so the call site's
/// own multi-result refusal does not fire and the refusal seen is this one.
const IN_TABLE_WITH_DISPATCH: &str = r#"(module
  (type $s (func (param i32) (result i32)))
  (table 2 funcref)
  (elem (i32.const 0) $two $one)
  (func $two (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul)
  (func $one (param i32) (result i32) local.get 0 i32.const 3 i32.mul)
  (func (export "disp") (param i32) (result i32)
    local.get 0 i32.const 1 call_indirect (type $s)))
"#;

struct Leg {
    name: &'static str,
    flags: &'static [&'static str],
}

/// Every backend and output kind the issue and its triage measured, plus A32.
const LEGS: &[Leg] = &[
    Leg {
        name: "cortex-m4 default image",
        flags: &["--target", "cortex-m4"],
    },
    Leg {
        name: "cortex-m4 relocatable",
        flags: &["--target", "cortex-m4", "--relocatable"],
    },
    Leg {
        name: "cortex-m4 relocatable all-exports",
        flags: &["--target", "cortex-m4", "--relocatable", "--all-exports"],
    },
    Leg {
        name: "cortex-r5 (A32) relocatable",
        flags: &["--target", "cortex-r5", "--relocatable", "--all-exports"],
    },
    Leg {
        name: "rv32imac relocatable",
        flags: &["-b", "riscv", "--target", "riscv32imac", "--relocatable"],
    },
    Leg {
        name: "aarch64 relocatable",
        flags: &["-b", "aarch64", "--relocatable"],
    },
];

fn run(tag: &str, wat: &str, flags: &[&str]) -> (Output, PathBuf) {
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("synth-1450-{}-{n}-{tag}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let src = dir.join("m.wat");
    std::fs::write(&src, wat).expect("write wat");
    let obj = dir.join("m.o");
    let out = Command::new(env!("CARGO_BIN_EXE_synth"))
        .arg("compile")
        .arg(&src)
        .args(flags)
        .arg("-o")
        .arg(&obj)
        .output()
        .expect("run synth compile");
    (out, obj)
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

fn assert_refused(what: &str, o: &Output, obj: &std::path::Path) {
    let e = stderr(o);
    assert!(
        !o.status.success(),
        "{what}: exit 0 — the multi-result entry point was compiled:\n{e}"
    );
    assert!(e.contains(NEEDLE), "{what}: no `{NEEDLE}` in:\n{e}");
    assert!(e.contains(ISSUE), "{what}: no `{ISSUE}` in:\n{e}");
    assert!(!obj.exists(), "{what}: refused, yet an object was written");
}

fn assert_compiles_quietly(what: &str, o: &Output, obj: &std::path::Path) {
    let e = stderr(o);
    assert!(o.status.success(), "{what}: refused:\n{e}");
    assert!(
        !e.contains(NEEDLE),
        "{what}: compiled, but named the refusal:\n{e}"
    );
    assert!(obj.exists(), "{what}: exit 0 with no object");
}

#[test]
fn exported_i32_pair_is_refused_on_every_backend() {
    for leg in LEGS {
        let (o, obj) = run("exp", EXPORTED_I32_PAIR, leg.flags);
        assert_refused(leg.name, &o, &obj);
        assert!(
            stderr(&o).contains("returns 2 results"),
            "{}: the result count is not named:\n{}",
            leg.name,
            stderr(&o)
        );
    }
}

#[test]
fn exported_f32_pair_is_refused_on_cortex_m7dp() {
    for flags in [
        &["--target", "cortex-m7dp"][..],
        &["--target", "cortex-m7dp", "--relocatable"][..],
    ] {
        let (o, obj) = run("f32", EXPORTED_F32_PAIR, flags);
        assert_refused(&format!("cortex-m7dp {flags:?}"), &o, &obj);
    }
}

/// The single-function path: the function a compile names is its entry point
/// whether it is selected by name or by index, and whether or not the module
/// exports it.
#[test]
fn a_named_multi_result_function_is_refused_on_the_single_function_path() {
    for (what, wat, flags) in [
        (
            "arm --func-name",
            EXPORTED_I32_PAIR,
            &["--target", "cortex-m4", "--func-name", "two"][..],
        ),
        (
            "riscv --func-name",
            EXPORTED_I32_PAIR,
            &[
                "-b",
                "riscv",
                "--target",
                "riscv32imac",
                "--func-name",
                "two",
            ][..],
        ),
        (
            "aarch64 --func-name",
            EXPORTED_I32_PAIR,
            &["-b", "aarch64", "--func-name", "two"][..],
        ),
        (
            "arm --func-index of an UNEXPORTED function",
            UNEXPORTED_UNCALLED,
            &["--target", "cortex-m4", "--func-index", "0"][..],
        ),
    ] {
        let (o, obj) = run("single", wat, flags);
        assert_refused(what, &o, &obj);
    }
}

/// PAIRED CONTROL: one result each, same bodies, same legs — compiles.
#[test]
fn control_single_result_exports_compile_on_every_backend() {
    for leg in LEGS {
        let (o, obj) = run("ctl", SINGLE_RESULTS, leg.flags);
        assert_compiles_quietly(leg.name, &o, &obj);
    }
}

/// The refusal is not widened: a multi-result function nothing outside the
/// module can reach is not emitted, and its module compiles.
#[test]
fn unexported_uncalled_multi_result_function_still_compiles() {
    for leg in LEGS {
        for (tag, wat) in [
            ("unexp", UNEXPORTED_UNCALLED),
            ("tabnod", IN_TABLE_NO_DISPATCH),
        ] {
            let (o, obj) = run(tag, wat, leg.flags);
            assert_compiles_quietly(&format!("{} / {tag}", leg.name), &o, &obj);
        }
    }
}

/// Address-taken AND compiled: an export dispatches through the table, so the
/// table's functions are emitted. ARM (Thumb-2, A32) and AArch64 lower
/// `call_indirect` and compiled this on 6641efec; RV32 already declined it,
/// for the dispatching export's `call_indirect`, and still names #1450 for
/// the table function it skips first.
#[test]
fn a_compiled_table_function_with_two_results_is_refused() {
    for leg in LEGS {
        let (o, obj) = run("tabci", IN_TABLE_WITH_DISPATCH, leg.flags);
        assert_refused(leg.name, &o, &obj);
        assert!(
            stderr(&o).contains("in a table (address-taken)"),
            "{}: the reason is not `address-taken`:\n{}",
            leg.name,
            stderr(&o)
        );
    }
}

/// `--allow-skipped-exports` is the sweep callers' opt-in to a partial
/// object. It still never ships the multi-result export: the symbol is
/// absent and the skip names #1450.
#[test]
fn allow_skipped_exports_omits_the_multi_result_export() {
    const MIXED: &str = r#"(module
  (func (export "two") (param i32) (result i32 i32)
    local.get 0 i32.const 3 i32.mul
    local.get 0 i32.const 5 i32.mul)
  (func (export "one") (param i32) (result i32) local.get 0 i32.const 3 i32.mul))
"#;
    for leg in LEGS.iter().filter(|l| l.flags.contains(&"--relocatable")) {
        let (o, obj) = run("mixed", MIXED, leg.flags);
        assert_refused(leg.name, &o, &obj);

        let mut flags = leg.flags.to_vec();
        flags.push("--allow-skipped-exports");
        let (o, obj) = run("mixed-allow", MIXED, &flags);
        let e = stderr(&o);
        assert!(o.status.success(), "{}: {e}", leg.name);
        assert!(e.contains(NEEDLE) && e.contains(ISSUE), "{}: {e}", leg.name);
        let bytes = std::fs::read(&obj).expect("partial object");
        let has = |name: &[u8]| {
            let mut n = vec![0u8];
            n.extend_from_slice(name);
            n.push(0);
            bytes.windows(n.len()).any(|w| w == n.as_slice())
        };
        assert!(has(b"one"), "{}: `one` is not in the object", leg.name);
        assert!(!has(b"two"), "{}: `two` is in the object", leg.name);
    }
}
