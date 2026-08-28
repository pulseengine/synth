//! #1093 — the RV32 backend declines a PARAMETER-taking block type before
//! selection. Red-first: on v0.60.0 (contradicting the issue's own table,
//! which said rv32 declines cleanly) this op stream PANICKED at
//! `lower_else`'s `split_off(entry)` — "`at` split index (is 2) should be <=
//! len (is 1)", exit 101 — and the branch-edge `block`/`loop (param ..)`
//! shapes compiled with silently WRONG join values (unicorn vs wasmtime:
//! `bpb(1)` → 10, want 15; `lpb(3)` → 2, want 3). Mechanism + measured
//! matrix: `synth_core::find_param_block_type` (the aarch64 VCR-A64-CF-001
//! refusal ported).

use synth_backend_riscv::RiscVBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::{TargetSpec, WasmOp};

fn config(block_arity: Vec<(u8, u8)>) -> CompileConfig {
    CompileConfig {
        target: TargetSpec::riscv32imac(),
        current_func_block_arity: block_arity,
        ..CompileConfig::default()
    }
}

#[test]
fn rv32_declines_param_if_not_panics_1093() {
    use WasmOp::*;
    let ops = vec![
        I32Const(1),
        I32Const(2),
        LocalGet(0),
        If,
        I32Add,
        Else,
        I32Sub,
        End,
        End,
    ];
    let err = RiscVBackend::new()
        .compile_function("params", &ops, &config(vec![(2, 1)]))
        .expect_err("a parameter-taking block type must decline loudly, never panic")
        .to_string();
    assert!(
        err.contains("PARAMETER-taking block type") && err.contains("if #0 has type (2, 1)"),
        "decline must name the class/construct/arity; got: {err}"
    );
}

#[test]
fn rv32_declines_param_loop_the_silent_direction_1093() {
    use WasmOp::*;
    // The measured SILENT miscompile: (i32.const 0) (loop (param i32)
    // (result i32) ... br_if 0 ...) returned 2 for lpb(3), want 3. The class
    // guard converts it to a named decline.
    let ops = vec![
        I32Const(0),
        Loop,
        I32Const(1),
        I32Add,
        LocalGet(0),
        BrIf(0),
        End,
        End,
    ];
    let err = RiscVBackend::new()
        .compile_function("lpb", &ops, &config(vec![(1, 1)]))
        .expect_err("a parameter-taking loop type must decline loudly")
        .to_string();
    assert!(err.contains("loop #0 has type (1, 1)"), "got: {err}");
}

#[test]
fn rv32_keeps_the_void_reading_without_a_side_table_1093() {
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
    RiscVBackend::new()
        .compile_function("void_if", &ops, &config(Vec::new()))
        .expect("void if/else with no side-table must keep compiling");
}
