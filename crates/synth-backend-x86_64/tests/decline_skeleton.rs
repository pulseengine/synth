//! Every shape lanes X1-X2 do not lower is an `Err` that NAMES its cause, and
//! no object is produced. RQ-91-X86SKEL, RQ-91-X86ALU (#1741). The CLI half (non-zero exit, no
//! file written) is `crates/synth-cli/tests/x86_64_skeleton_1741.rs`.

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
    // Division and remainder: x86 `div`/`idiv` FAULT (#DE) on a zero divisor
    // and on INT_MIN / -1, where wasm traps on the first and `rem_s` returns
    // 0. Declined by name until the guards exist (lane X4), never lowered as
    // a bare `idiv`.
    (
        "i32.div_s",
        r#"(module (func (export "f") (param i32 i32) (result i32)
             local.get 0 local.get 1 i32.div_s))"#,
        "I32DivS",
    ),
    (
        "i32.div_u",
        r#"(module (func (export "f") (param i32 i32) (result i32)
             local.get 0 local.get 1 i32.div_u))"#,
        "I32DivU",
    ),
    (
        "i32.rem_s",
        r#"(module (func (export "f") (param i32 i32) (result i32)
             local.get 0 local.get 1 i32.rem_s))"#,
        "I32RemS",
    ),
    (
        "i32.rem_u",
        r#"(module (func (export "f") (param i32 i32) (result i32)
             local.get 0 local.get 1 i32.rem_u))"#,
        "I32RemU",
    ),
    (
        "i64.div_s",
        r#"(module (func (export "f") (param i64 i64) (result i64)
             local.get 0 local.get 1 i64.div_s))"#,
        "I64DivS",
    ),
    (
        "i64.div_u",
        r#"(module (func (export "f") (param i64 i64) (result i64)
             local.get 0 local.get 1 i64.div_u))"#,
        "I64DivU",
    ),
    (
        "i64.rem_s",
        r#"(module (func (export "f") (param i64 i64) (result i64)
             local.get 0 local.get 1 i64.rem_s))"#,
        "I64RemS",
    ),
    (
        "i64.rem_u",
        r#"(module (func (export "f") (param i64 i64) (result i64)
             local.get 0 local.get 1 i64.rem_u))"#,
        "I64RemU",
    ),
    // The bit counts: `lzcnt`/`tzcnt`/`popcnt` are above the baseline ISA.
    (
        "i32.clz",
        r#"(module (func (export "f") (param i32) (result i32) local.get 0 i32.clz))"#,
        "I32Clz",
    ),
    (
        "i32.ctz",
        r#"(module (func (export "f") (param i32) (result i32) local.get 0 i32.ctz))"#,
        "I32Ctz",
    ),
    (
        "i64.popcnt",
        r#"(module (func (export "f") (param i64) (result i64) local.get 0 i64.popcnt))"#,
        "I64Popcnt",
    ),
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
        "local.tee",
        r#"(module (func (export "f") (param i32) (result i32)
             local.get 0 local.tee 0))"#,
        "LocalTee",
    ),
    (
        "four temporaries in use at once",
        r#"(module (func (export "f") (result i32)
             i32.const 1 i32.const 2 i32.const 3 i32.const 4
             i32.add i32.add i32.add))"#,
        "more than 3 temporaries",
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
    (
        "local.set",
        r#"(module (func (export "f") (param i32) (result i32)
             local.get 0 local.set 0 local.get 0))"#,
        "LocalSet",
    ),
    (
        "non-param local",
        r#"(module (func (export "f") (param i32) (result i32) (local i32)
             local.get 1))"#,
        "non-parameter local",
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
             (func (param i32) (result i32) local.get 0 i32.popcnt)
             (func (export "f") (param i32) (result i32) local.get 0))"#,
        "I32Popcnt",
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

/// The one exception to "everything else is refused": the shared decoder drops
/// `nop` before the selector sees it, so a body with `nop` compiles (as
/// nothing). Pinned so the exception stays stated (REVIEW_13 F4).
#[test]
fn nop_is_dropped_by_the_decoder_and_compiles() {
    let wasm = wat::parse_str(
        r#"(module (func (export "f") (param i32) (result i32) nop local.get 0 nop))"#,
    )
    .unwrap();
    let obj = compile_wasm(&wasm).expect("nop is dropped at decode, not refused");
    assert_eq!(obj.functions[0].insts.len(), 2, "mov + ret, no nop");
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
