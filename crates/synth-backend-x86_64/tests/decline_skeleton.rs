//! Every shape lane X1 does not lower is an `Err` that NAMES its cause, and no
//! object is produced. RQ-91-X86SKEL (#1741). The CLI half (non-zero exit, no
//! file written) is `crates/synth-cli/tests/x86_64_skeleton_1741.rs`.

use synth_backend_x86_64::compile_wasm;

fn err(src: &str) -> String {
    let wasm = wat::parse_str(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    match compile_wasm(&wasm) {
        Ok(_) => panic!("lowered, but lane X1 must decline:\n{src}"),
        Err(e) => e.to_string(),
    }
}

/// `(case, module, a substring the refusal must contain)`.
const CASES: &[(&str, &str, &str)] = &[
    (
        "i32.sub",
        r#"(module (func (export "f") (param i32 i32) (result i32)
             local.get 0 local.get 1 i32.sub))"#,
        "I32Sub",
    ),
    (
        "i32.const",
        r#"(module (func (export "f") (result i32) i32.const 7))"#,
        "I32Const",
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
        "i64 param",
        r#"(module (func (export "f") (param i64) (result i64) local.get 0))"#,
        "i64",
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
        "unsupported helper",
        r#"(module
             (func (param i32) (result i32) local.get 0 i32.eqz)
             (func (export "f") (param i32) (result i32) local.get 0))"#,
        "I32Eqz",
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
