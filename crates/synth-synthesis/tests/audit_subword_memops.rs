//! Audit: sub-word memory ops, globals, and memory.size/grow must lower
//! through the optimizer path without unmapped-vreg panics.
//!
//! Pre-PR: these ops fell through `wasm_to_ir`'s `_ => Opcode::Nop` arm,
//! consumed an inst_id slot, but produced no `vreg_to_arm` mapping. The
//! defensive panic in `get_arm_reg` (PR #101) surfaces this as a compiler
//! crash for downstream consumers; pre-defensive-panic the code silently
//! returned R0, clobbering AAPCS params.

use synth_synthesis::{OptimizerBridge, WasmOp};

fn compile(wasm: &[WasmOp], num_params: usize) {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge.optimize_full(wasm).expect("optimize_full");
    // ir_to_arm is the panic site for unmapped-vreg consumers.
    let _arm = bridge.ir_to_arm(&ir, num_params);
}

#[test]
fn subword_i32_load8_u_then_drop() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Load8U {
            offset: 0,
            align: 0,
        },
        WasmOp::Drop,
    ];
    compile(&wasm, 0);
}

#[test]
fn subword_i32_load8_s_into_arith() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Load8S {
            offset: 0,
            align: 0,
        },
        WasmOp::I32Const(1),
        WasmOp::I32Add,
        WasmOp::Drop,
    ];
    compile(&wasm, 0);
}

#[test]
fn subword_i32_load16_u_then_drop() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Load16U {
            offset: 0,
            align: 0,
        },
        WasmOp::Drop,
    ];
    compile(&wasm, 0);
}

#[test]
fn subword_i32_load16_s_into_arith() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Load16S {
            offset: 0,
            align: 0,
        },
        WasmOp::I32Const(1),
        WasmOp::I32Add,
        WasmOp::Drop,
    ];
    compile(&wasm, 0);
}

#[test]
fn subword_i32_store8() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Const(0xff),
        WasmOp::I32Store8 {
            offset: 0,
            align: 0,
        },
    ];
    compile(&wasm, 0);
}

#[test]
fn subword_i32_store16() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Const(0xffff),
        WasmOp::I32Store16 {
            offset: 0,
            align: 0,
        },
    ];
    compile(&wasm, 0);
}

#[test]
fn global_get_then_drop() {
    let wasm = vec![WasmOp::GlobalGet(0), WasmOp::Drop];
    compile(&wasm, 0);
}

#[test]
fn global_get_into_arith() {
    let wasm = vec![
        WasmOp::GlobalGet(0),
        WasmOp::I32Const(1),
        WasmOp::I32Add,
        WasmOp::Drop,
    ];
    compile(&wasm, 0);
}

#[test]
fn global_set() {
    let wasm = vec![WasmOp::I32Const(42), WasmOp::GlobalSet(0)];
    compile(&wasm, 0);
}

#[test]
fn memory_size_then_drop() {
    let wasm = vec![WasmOp::MemorySize(0), WasmOp::Drop];
    compile(&wasm, 0);
}

#[test]
fn memory_size_into_arith() {
    let wasm = vec![
        WasmOp::MemorySize(0),
        WasmOp::I32Const(1),
        WasmOp::I32Add,
        WasmOp::Drop,
    ];
    compile(&wasm, 0);
}

#[test]
fn memory_grow_then_drop() {
    let wasm = vec![WasmOp::I32Const(1), WasmOp::MemoryGrow(0), WasmOp::Drop];
    compile(&wasm, 0);
}
