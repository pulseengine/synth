//! #1093 — the ARM backend declines a PARAMETER-taking block type at its
//! single choke point (`compile_wasm_to_arm`), covering BOTH codegen paths
//! (the optimized route and the #197 `--relocatable` direct route) with one
//! check. Red-first: on v0.60.0 this op stream PANICKED
//! ("`at` split index (is 2) should be <= len (is 1)", exit 101) on every ARM
//! invocation path; the else-less variant compiled and was silently WRONG on
//! the false path. Mechanism + measured matrix:
//! `synth_core::find_param_block_type` (the aarch64 VCR-A64-CF-001 refusal
//! ported).

use synth_backend::ArmBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::{TargetSpec, WasmOp};

fn config(block_arity: Vec<(u8, u8)>, relocatable: bool) -> CompileConfig {
    CompileConfig {
        target: TargetSpec::cortex_m4(),
        relocatable,
        current_func_block_arity: block_arity,
        ..CompileConfig::default()
    }
}

fn params_if_ops() -> Vec<WasmOp> {
    use WasmOp::*;
    // (i32.const 1) (i32.const 2)
    // (if (param i32 i32) (result i32) (local.get 0)
    //   (then i32.add) (else i32.sub))
    vec![
        I32Const(1),
        I32Const(2),
        LocalGet(0),
        If,
        I32Add,
        Else,
        I32Sub,
        End,
        End,
    ]
}

/// RQ-64-MVLOWER increment 2 (#1093): the #1093 repro LOWERS on
/// `--relocatable` (the configuration the #1097 oracle executes — its
/// LOWERED if/arm leg) and still declines, by name and never a panic, on the
/// self-contained image path, which no oracle leg executes.
#[test]
fn arm_declines_param_if_on_the_self_contained_path_and_lowers_it_relocatable_1093() {
    let backend = ArmBackend::new();
    let err = backend
        .compile_function("params", &params_if_ops(), &config(vec![(2, 1)], false))
        .expect_err("a parameter-taking block type must decline loudly, never panic")
        .to_string();
    assert!(
        err.contains("PARAMETER-taking block type")
            && err.contains("if #0 has type (2, 1)")
            && err.contains("self-contained image path"),
        "decline must name the class/construct/arity/path; got: {err}"
    );
    backend
        .compile_function("params", &params_if_ops(), &config(vec![(2, 1)], true))
        .expect("the #1093 if (param i32 i32) (result i32) + else repro lowers on --relocatable");
}

/// RQ-64-MVLOWER increment 1 (#1093): the choke point relaxes `block
/// (param ..)` ONLY on `--relocatable` — the configuration the #1097 oracle
/// executes (its LOWERED block/arm leg) — and keeps the full decline on the
/// self-contained image path, which no oracle leg executes. `if (param ..)`
/// stays declined on the self-contained path too.
#[test]
fn arm_lowers_param_block_only_on_the_relocatable_path_rq64() {
    use WasmOp::*;
    // (i32.const 7) (block (param i32) (result i32) (local.get 0) (br_if 0)
    //   (i32.const 42) (i32.add)) — the #1097 `bpb` shape.
    let bpb = vec![
        I32Const(7),
        Block,
        LocalGet(0),
        BrIf(0),
        I32Const(42),
        I32Add,
        End,
        End,
    ];
    let backend = ArmBackend::new();
    backend
        .compile_function("bpb", &bpb, &config(vec![(1, 1)], true))
        .expect("block (param i32) (result i32) lowers on --relocatable (RQ-64-MVLOWER)");
    let err = backend
        .compile_function("bpb", &bpb, &config(vec![(1, 1)], false))
        .expect_err("the self-contained image path has no oracle leg and keeps the decline")
        .to_string();
    assert!(
        err.contains("PARAMETER-taking block type")
            && err.contains("block #0 has type (1, 1)")
            && err.contains("self-contained image path"),
        "got: {err}"
    );
}

#[test]
fn arm_keeps_the_void_reading_without_a_side_table_1093() {
    // The same guard must never fire for the legacy all-void reading (empty
    // side-table, hand-built op streams) on a well-formed void stream.
    use WasmOp::*;
    let ops = vec![
        LocalGet(0),
        If,
        I32Const(1),
        Drop,
        Else,
        I32Const(2),
        Drop,
        End,
        End,
    ];
    let backend = ArmBackend::new();
    backend
        .compile_function("void_if", &ops, &config(Vec::new(), true))
        .expect("void if/else with no side-table must keep compiling");
}
