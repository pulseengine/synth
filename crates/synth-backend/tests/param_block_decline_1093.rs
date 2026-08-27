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

#[test]
fn arm_declines_param_if_on_both_paths_1093() {
    let backend = ArmBackend::new();
    for relocatable in [false, true] {
        let err = backend
            .compile_function(
                "params",
                &params_if_ops(),
                &config(vec![(2, 1)], relocatable),
            )
            .expect_err("a parameter-taking block type must decline loudly, never panic")
            .to_string();
        assert!(
            err.contains("PARAMETER-taking block type") && err.contains("if #0 has type (2, 1)"),
            "relocatable={relocatable}: decline must name the class/construct/arity; got: {err}"
        );
    }
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
