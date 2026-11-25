//! #929 (CRITICAL) — a 64-bit call argument must never be marshalled as one
//! 32-bit word. Refs #1785: a DIRECT call now marshals it per AAPCS; the
//! residual that cannot be marshalled still DECLINES.
//!
//! Measured on v0.55.0, executed under qemu against wasmtime:
//!
//! ```wat
//! (func $g (param i64 i32) (result i32) (local.get 1))
//! (func (export "f") (param i32 i32) (result i32)
//!   (call $g (i64.const 1234605616436508552) (local.get 0)))
//! ```
//!
//! | | `f(7)` | `f(42)` |
//! |---|---|---|
//! | wasmtime | 7 | 42 |
//! | thumb-2  | **287454020** | **287454020** |
//!
//! `287454020` = `0x11223344` = the i64's HIGH half, returned regardless of the
//! actual argument. `synth compile` exited 0 with no warning. v0.57 turned
//! that into a loud decline of every i64 argument (#929).
//!
//! # v0.92 (Refs #1785): the direct call is marshalled
//!
//! `call_arg_marshal` lays a direct call's core arguments out with
//! `aapcs_param_layout` over the callee's DECLARED widths — the walk synth's
//! own callee prologue homes params with: an i64 takes the next even register
//! pair (an odd NCRN is skipped and never back-filled), low word in the lower
//! register; one that does not fit goes to an 8-aligned stack slot, and every
//! later argument follows it. The execution oracle is
//! `crates/synth-oracle/tests/i64_call_args_1785.rs` (local and import
//! callees, register and stack shapes, against kiln).
//!
//! # What still declines, and why
//!
//! `call_indirect`: no per-TYPE param-width table reaches the selector, so
//! every argument of an indirect call is declared narrow and a 64-bit operand
//! is refused by the width check (#929), never marshalled as one word.

use std::path::PathBuf;
use std::process::Command;

fn synth() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_synth"))
}

fn compile(tag: &str, wat: &str) -> (bool, String, String) {
    let dir = std::env::temp_dir().join(format!("synth-929-{tag}"));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let src = dir.join("m.wat");
    std::fs::write(&src, wat).expect("write wat");
    let obj = dir.join("m.o");
    let out = Command::new(synth())
        .args([
            "compile",
            src.to_str().unwrap(),
            "-b",
            "arm",
            "-t",
            "cortex-m3",
            "--all-exports",
            "--relocatable",
            // #952: in the decline fixture `f` is the sole export and is
            // exactly the function #929 declines — since v0.57 that exits
            // non-zero by default. The test wants the decline (and its
            // diagnostic) with the compile still reporting success, which is
            // the opt-in `--allow-skipped-exports` case. A no-op where nothing
            // is skipped.
            "--allow-skipped-exports",
            "-o",
            obj.to_str().unwrap(),
        ])
        .output()
        .expect("run synth");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).to_string(),
        String::from_utf8_lossy(&out.stderr).to_string(),
    )
}

const I64_FIRST: &str = r#"(module
  (func $g (param i64 i32) (result i32) (local.get 1))
  (func (export "f") (param i32 i32) (result i32)
    (call $g (i64.const 1234605616436508552) (local.get 0))))
"#;

const I64_LAST: &str = r#"(module
  (func $g (param i32 i64) (result i32) (local.get 0))
  (func (export "f") (param i32 i32) (result i32)
    (call $g (local.get 0) (i64.const 1234605616436508552))))
"#;

/// An i64 argument of a `call_indirect`: no width table, so it must decline.
const I64_INDIRECT: &str = r#"(module
  (type $t (func (param i64) (result i32)))
  (table 1 funcref)
  (elem (i32.const 0) $g)
  (func $g (type $t) (i32.wrap_i64 (local.get 0)))
  (func (export "f") (result i32)
    (call_indirect (type $t) (i64.const 5) (i32.const 0))))
"#;

const I32_ONLY: &str = r#"(module
  (func $g (param i32 i32) (result i32) (local.get 1))
  (func (export "f") (param i32 i32) (result i32)
    (call $g (local.get 0) (local.get 1))))
"#;

fn assert_emitted(tag: &str, wat: &str) {
    let (ok, _out, err) = compile(tag, wat);
    assert!(ok, "{tag}: the compile must succeed: {err}");
    assert!(
        !err.contains("#929") && !err.contains("skipped"),
        "{tag}: a direct call with an i64 argument is marshalled per AAPCS \
         since #1785 and its caller must be EMITTED: {err}"
    );
}

/// gale's exact repro: the i64 in R0:R1, the i32 in R2. Executed by
/// `i64_call_args_1785.rs`; here only that the caller is emitted.
#[test]
fn i64_first_argument_is_marshalled_1785() {
    assert_emitted("first", I64_FIRST);
}

/// The i64-LAST shape: AAPCS skips R1 and puts the pair in R2:R3.
#[test]
fn i64_last_argument_is_marshalled_1785() {
    assert_emitted("last", I64_LAST);
}

/// The residual: an i64 argument of an indirect call is refused by name, and
/// the caller is OMITTED (emitting it at all would be the #929 miscompile).
#[test]
fn i64_indirect_call_argument_is_still_declined() {
    let (ok, _out, err) = compile("indirect", I64_INDIRECT);
    assert!(ok, "the compile itself should still succeed: {err}");
    assert!(
        err.contains("#929") && err.contains("skipping function 'f'"),
        "the indirect caller must be declined, naming #929: {err}"
    );
}

/// NON-VACUITY: an all-i32 call must still compile and emit its caller.
#[test]
fn i32_only_call_still_compiles_and_is_emitted() {
    assert_emitted("i32", I32_ONLY);
}
