//! Refs #1762: the RV32 selector takes a never-written local's width from
//! its DECLARATION.
//!
//! `(param i32) (result i64) (local i64) local.get 1` has no store into the
//! local, so the dataflow inference (which learns a width from a store) laid
//! it out as a 4-byte slot. The body then zeroed one word, loaded one word
//! into a0 and returned with a1 never written. The executed comparison is
//! `crates/synth-oracle/tests/zero_init_wide_local_1762.rs`; this is the
//! same fact on the default `cargo test --workspace` build, read off the
//! lowered ops.

use synth_backend_riscv::{
    Reg, RiscVOp, RvGlobalsCtx, SelectorOptions, select_with_block_arity,
    select_with_declared_locals,
};
use synth_core::backend::{Backend, CompileConfig};
use synth_core::target::TargetSpec;
use synth_core::wasm_op::WasmOp;

/// `local.get 1` of the one non-param local, `declared` giving its width.
fn lower(declared: &[bool]) -> Vec<RiscVOp> {
    select_with_declared_locals(
        &[WasmOp::LocalGet(1), WasmOp::End],
        1,
        SelectorOptions::wasm_compliant(),
        &[],
        &[],
        &[],
        &[],
        &RvGlobalsCtx::default(),
        &[false],
        &[],
        declared,
    )
    .expect("selects")
    .ops
}

fn zero_stores(ops: &[RiscVOp]) -> Vec<i32> {
    ops.iter()
        .filter_map(|op| match op {
            RiscVOp::Sw {
                rs1: Reg::SP,
                rs2: Reg::ZERO,
                imm,
            } => Some(*imm),
            _ => None,
        })
        .collect()
}

fn writes(ops: &[RiscVOp], reg: Reg) -> bool {
    ops.iter()
        .any(|op| matches!(op, RiscVOp::Addi { rd, .. } if *rd == reg))
}

#[test]
fn a_declared_wide_local_gets_both_words() {
    let wide = lower(&[true]);
    assert_eq!(
        zero_stores(&wide),
        [0, 4],
        "both words of the slot are zeroed"
    );
    assert!(writes(&wide, Reg::A0), "low word reaches a0");
    assert!(writes(&wide, Reg::A1), "high word reaches a1");

    // A local declared 32-bit, and an op stream with no declaration table,
    // keep the one-word lowering.
    for narrow in [lower(&[false]), lower(&[])] {
        assert_eq!(zero_stores(&narrow), [0]);
        assert!(writes(&narrow, Reg::A0));
        assert!(!writes(&narrow, Reg::A1));
    }
    // The older entry point passes no table.
    let legacy = select_with_block_arity(
        &[WasmOp::LocalGet(1), WasmOp::End],
        1,
        SelectorOptions::wasm_compliant(),
        &[],
        &[],
        &[],
        &[],
        &RvGlobalsCtx::default(),
        &[false],
        &[],
    )
    .expect("selects")
    .ops;
    assert_eq!(legacy, lower(&[]));
}

/// The backend derives the table from BOTH decoder tables: a declared i64
/// and a declared f64 (width 8 in `current_func_declared_float_locals`) are
/// wide; an f32 (width 4) and an i32 are not.
#[test]
fn the_backend_reads_i64_and_f64_declarations() {
    let code = |i64s: &[bool], floats: &[u8]| -> Vec<u8> {
        let cfg = CompileConfig {
            target: TargetSpec::riscv32imac(),
            current_func_param_count: Some(1),
            current_func_declared_i64_locals: i64s.to_vec(),
            current_func_declared_float_locals: floats.to_vec(),
            ..CompileConfig::default()
        };
        synth_backend_riscv::RiscVBackend::new()
            .compile_function("f", &[WasmOp::LocalGet(1), WasmOp::End], &cfg)
            .expect("compiles")
            .code
    };
    let narrow = code(&[false], &[0]);
    let wide = code(&[true], &[0]);
    assert_ne!(wide, narrow);
    assert_eq!(code(&[false], &[8]), wide, "a declared f64 local is wide");
    assert_eq!(
        code(&[], &[8]),
        wide,
        "the tables need not be the same length"
    );
    assert_eq!(code(&[true], &[]), wide);
    assert_eq!(code(&[false], &[4]), narrow, "a declared f32 local is not");
    assert_eq!(code(&[], &[]), narrow);
}
