//! #929 (CRITICAL) — a 64-bit call argument in a register position must DECLINE,
//! not miscompile.
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
//! actual argument. `synth compile` exited 0 with no warning.
//!
//! # Root cause, and why the refusal covers the whole class
//!
//! `emit_arg_moves` maps one argument to one register (`arg_srcs[i]` ->
//! `ARG_REGS[i]`). AAPCS gives a 64-bit argument an EVEN-ALIGNED register PAIR,
//! so the high half was never placed and every later argument shifted down.
//!
//! Its docstring has always said it cannot do this — *"i64/f64 arguments —
//! which AAPCS passes in register pairs — are NOT marshalled"* — and it
//! marshalled them anyway. A documented non-capability with nothing enforcing
//! it is not a limitation; it is a silent miscompile.
//!
//! The refusal covers EVERY i64 register argument, not just the "not last"
//! shape the issue measured. For `(i32, i64)` AAPCS places the i64 in `r2:r3`
//! while synth puts its low half in `r1`: that shape looked correct only
//! because the callee under test returned the i32, so the wrong i64 was never
//! read. Refusing the class is the honest boundary.
//!
//! FOLLOW-UP: real AAPCS pair marshalling. The #928 conformance gate declines
//! 118 assertions as `i64-pair` — that is precisely this capability, and it is
//! the acceptance oracle already in place.

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
            // #952: `f` is the sole export in the two decline fixtures below,
            // and it is exactly the function #929 declines — since v0.57 that
            // exits non-zero by default. These tests want the decline (and
            // its diagnostic) with the compile still reporting success, which
            // is the opt-in `--allow-skipped-exports` case. A no-op on
            // I32_ONLY, where nothing is skipped.
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

const I32_ONLY: &str = r#"(module
  (func $g (param i32 i32) (result i32) (local.get 1))
  (func (export "f") (param i32 i32) (result i32)
    (call $g (local.get 0) (local.get 1))))
"#;

/// gale's exact repro: the function must NOT be emitted, and the reason must
/// name #929. Emitting it at all is the miscompile.
#[test]
fn i64_first_argument_is_declined_not_miscompiled() {
    let (ok, _out, err) = compile("first", I64_FIRST);
    assert!(ok, "the compile itself should still succeed: {err}");
    assert!(
        err.contains("#929"),
        "the decline must name #929 so a consumer can act on it: {err}"
    );
    assert!(
        err.contains("skipped") && err.contains("'f'")
            || err.contains("f\n")
            || err.contains(": f"),
        "the caller must be OMITTED from the object, not emitted with wrong \
         argument marshalling: {err}"
    );
}

/// The i64-LAST shape is refused too. It is not a regression: AAPCS places that
/// i64 in r2:r3 while synth put its low half in r1, so the i64 parameter was
/// already wrong — it merely went unnoticed because the callee returned the
/// i32. This test exists so that fact is recorded rather than rediscovered.
#[test]
fn i64_last_argument_is_also_declined_because_it_was_never_right() {
    let (ok, _out, err) = compile("last", I64_LAST);
    assert!(ok, "the compile itself should still succeed: {err}");
    assert!(
        err.contains("#929"),
        "an i64 in ANY register argument position is mis-marshalled and must be \
         declined; passing here would mean the class is only partly refused: {err}"
    );
}

/// NON-VACUITY, and the regression guard: an all-i32 call must still compile
/// and emit its caller. Without this, a refusal that swallowed every call would
/// pass the two tests above.
#[test]
fn i32_only_call_still_compiles_and_is_emitted() {
    let (ok, _out, err) = compile("i32", I32_ONLY);
    assert!(ok, "an all-i32 call must compile: {err}");
    assert!(
        !err.contains("#929"),
        "the #929 refusal must not fire for i32 arguments — that would be a \
         refusal of everything, which passes the decline tests vacuously: {err}"
    );
    assert!(
        !err.contains("skipped"),
        "the all-i32 caller must be EMITTED, not skipped: {err}"
    );
}
