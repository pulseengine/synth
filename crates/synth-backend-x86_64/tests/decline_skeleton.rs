//! Every shape lanes X1-X4 do not lower is an `Err` that NAMES its cause, and
//! no object is produced. RQ-91-X86SKEL, RQ-91-X86ALU, RQ-91-X86FRAME (#1741).
//! The CLI half (non-zero exit, no file written) is
//! `crates/synth-cli/tests/x86_64_skeleton_1741.rs`.
//!
//! MOVED TO LOWERED in lanes X3-X4, and so no longer here: `local.set`,
//! `local.tee`, a non-parameter local, a value stack deeper than the
//! temporaries (it spills), `div`/`rem` and `clz`/`ctz`/`popcnt`. Their
//! execution oracle is `crates/synth-oracle/tests/x86_64_frame_div_kiln_oracle.rs`.

use synth_backend_x86_64::compile_wasm;

fn err(src: &str) -> String {
    let wasm = wat::parse_str(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    match compile_wasm(&wasm) {
        Ok(_) => panic!("lowered, but the x86_64 backend must decline:\n{src}"),
        Err(e) => e.to_string(),
    }
}

/// `(case, module, a substring the refusal must contain)`.
const CASES: &[(&str, &str, &str)] = &[
    (
        "unreachable",
        r#"(module (func (export "f") (result i32) unreachable))"#,
        "Unreachable",
    ),
    (
        "loop",
        r#"(module (func (export "f") (param i32) (result i32)
             loop (result i32) local.get 0 end))"#,
        "Loop",
    ),
    (
        "if",
        r#"(module (func (export "f") (param i32) (result i32)
             local.get 0 if (result i32) i32.const 1 else i32.const 2 end))"#,
        "If",
    ),
    (
        "f32.add",
        r#"(module (func (export "f") (param f32 f32) (result f32)
             local.get 0 local.get 1 f32.add))"#,
        "f32",
    ),
    (
        "call",
        r#"(module
             (func $g (param i32) (result i32) local.get 0)
             (func (export "f") (param i32) (result i32) local.get 0 call $g))"#,
        "Call",
    ),
    (
        "i32.load (memory)",
        r#"(module (memory 1) (func (export "f") (param i32) (result i32)
             local.get 0 i32.load))"#,
        "linear memory",
    ),
    (
        "7 params",
        r#"(module (func (export "f") (param i32 i32 i32 i32 i32 i32 i32) (result i32)
             local.get 6))"#,
        "7 parameters",
    ),
    // Lane X3: locals are lowered, but only i32/i64 ones, and only while
    // the frame fits one page (no stack probe is emitted).
    (
        "f32 local",
        r#"(module (func (export "f") (param i32) (result i32) (local f32)
             local.get 0))"#,
        "f32 parameter, result or local",
    ),
    (
        "funcref local",
        r#"(module (func (export "f") (result i32) (local funcref)
             i32.const 0))"#,
        "funcref",
    ),
    (
        "f64 param",
        r#"(module (func (export "f") (param f64) (result f64) local.get 0))"#,
        "f64",
    ),
    (
        "v128 param",
        r#"(module (func (export "f") (param v128) (result i32) i32.const 0))"#,
        "v128",
    ),
    (
        "externref identity",
        r#"(module (func (export "f") (param externref) (result externref) local.get 0))"#,
        "externref",
    ),
    (
        "multi-value",
        r#"(module (func (export "f") (param i32 i32) (result i32 i32)
             local.get 0 local.get 1))"#,
        "multi-value",
    ),
    (
        "dead code after return",
        r#"(module (func (export "f") (param i32 i32) (result i32)
             local.get 0 return local.get 1))"#,
        "follows `return`",
    ),
    (
        "import",
        r#"(module (import "env" "g" (func $g)) (func (export "f")))"#,
        "import section",
    ),
    (
        "global",
        r#"(module (global i32 (i32.const 0)) (func (export "f")))"#,
        "globals",
    ),
    (
        "table",
        r#"(module (table 1 funcref) (func (export "f")))"#,
        "table",
    ),
    (
        "start",
        r#"(module (func $s) (start $s) (func (export "f")))"#,
        "start function",
    ),
    (
        "block",
        r#"(module (func (export "f") (param i32) (result i32)
             block (result i32) local.get 0 end))"#,
        "Block",
    ),
    (
        "no export",
        r#"(module (func (param i32) (result i32) local.get 0))"#,
        "no exported functions",
    ),
    (
        "export named like its own label",
        r#"(module (func (export "func_0") (param i32) (result i32) local.get 0))"#,
        "same name as its own object-local label `func_0`",
    ),
    (
        "unsupported helper",
        r#"(module
             (func (param i32) (result i32) local.get 0 unreachable)
             (func (export "f") (param i32) (result i32) local.get 0))"#,
        "Unreachable",
    ),
];

#[test]
fn every_unlowered_shape_is_refused_by_name() {
    let mut n = 0;
    for (case, src, needle) in CASES {
        let e = err(src);
        assert!(
            e.contains(needle),
            "{case}: refusal does not name `{needle}`: {e}"
        );
        n += 1;
    }
    assert_eq!(n, CASES.len());
}

#[test]
fn invalid_wasm_is_refused_before_lowering() {
    let e = err(
        r#"(module (func $g (result i32) (local.get 0) drop i32.const 0)
             (func (export "f") (result i32) call $g))"#,
    );
    assert!(e.contains("invalid wasm"), "{e}");
}

/// A frame above one page is refused by name, at exactly the limit: 512
/// eight-byte slots fit, the 513th does not.
#[test]
fn a_frame_above_one_page_is_refused_at_the_limit() {
    let module = |n: usize| {
        format!(
            r#"(module (func (export "f") (result i64) (local {}) local.get 0))"#,
            vec!["i64"; n].join(" ")
        )
    };
    let ok = wat::parse_str(module(512)).unwrap();
    compile_wasm(&ok).expect("512 locals fit the 4096-byte frame");
    let e = err(&module(513));
    assert!(e.contains("4104 bytes") && e.contains("stack probe"), "{e}");
}

/// The one exception to "everything else is refused": the shared decoder drops
/// `nop` before the selector sees it, so a body with `nop` compiles (as
/// nothing). Pinned so the exception stays stated (REVIEW_13 F4).
#[test]
fn nop_is_dropped_by_the_decoder_and_compiles() {
    let compile = |body: &str| {
        let wasm = wat::parse_str(format!(
            r#"(module (func (export "f") (param i32) (result i32) {body}))"#
        ))
        .unwrap();
        compile_wasm(&wasm).expect("nop is dropped at decode, not refused")
    };
    let with = compile("nop local.get 0 nop");
    let without = compile("local.get 0");
    assert_eq!(with.functions[0].insts, without.functions[0].insts);
    assert_eq!(with.elf, without.elf);
}

/// The cross case stays accepted: `func_1` exported from function 0 beside a
/// real function 1 names a different body, so it is a GLOBAL alias of
/// function 0 and function 1 keeps its LOCAL label.
#[test]
fn an_export_named_like_another_functions_label_is_kept() {
    let wasm = wat::parse_str(
        r#"(module
             (func (export "func_1") (param i32) (result i32) local.get 0)
             (func (param i32) (result i32) local.get 0))"#,
    )
    .unwrap();
    let obj = compile_wasm(&wasm).unwrap();
    assert_eq!(obj.functions[0].symbols, vec!["func_0", "func_1"]);
    assert_eq!(obj.functions[1].symbols, vec!["func_1"]);
}
