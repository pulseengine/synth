//! Audit: i64 sub-word load handlers in `select_with_stack` previously
//! hardcoded the destination pair to R0:R1, clobbering AAPCS params 0 and 1
//! on every `i64.load8_u`/etc. — even with 2+ live params.

use synth_synthesis::{ArmInstruction, ArmOp, InstructionSelector, Reg, WasmOp};

fn compile_no_optimize(wasm_ops: &[WasmOp], num_params: u32) -> Vec<ArmInstruction> {
    let mut sel = InstructionSelector::new(vec![]);
    sel.select_with_stack(wasm_ops, num_params)
        .expect("select_with_stack")
}

fn writes(op: &ArmOp) -> Vec<Reg> {
    match op {
        ArmOp::Mov { rd, .. }
        | ArmOp::Asr { rd, .. }
        | ArmOp::Movw { rd, .. }
        | ArmOp::Movt { rd, .. }
        | ArmOp::Add { rd, .. }
        | ArmOp::Sub { rd, .. }
        | ArmOp::Ldr { rd, .. }
        | ArmOp::Ldrb { rd, .. }
        | ArmOp::Ldrsb { rd, .. }
        | ArmOp::Ldrh { rd, .. }
        | ArmOp::Ldrsh { rd, .. } => vec![*rd],
        _ => Vec::new(),
    }
}

fn first_local_get(wasm: &[WasmOp], p: u32) -> Option<usize> {
    wasm.iter().enumerate().find_map(|(i, op)| match op {
        WasmOp::LocalGet(idx) if *idx == p => Some(i),
        _ => None,
    })
}

fn assert_no_clobber(wasm: &[WasmOp], num_params: u32, label: &str) {
    let arm = compile_no_optimize(wasm, num_params);
    for p in 0..num_params.min(4) {
        let first_read = match first_local_get(wasm, p) {
            Some(i) => i,
            None => continue,
        };
        let param_reg = match p {
            0 => Reg::R0,
            1 => Reg::R1,
            2 => Reg::R2,
            3 => Reg::R3,
            _ => continue,
        };
        for instr in &arm {
            let line = match instr.source_line {
                Some(l) => l,
                None => continue,
            };
            if line >= first_read {
                break;
            }
            for w in writes(&instr.op) {
                assert_ne!(
                    w, param_reg,
                    "[{label}] AAPCS clobber: ARM instr at wasm line {line} writes \
                     param reg {param_reg:?} before LocalGet({p}) at line {first_read}. \
                     Op: {:?}",
                    instr.op
                );
            }
        }
    }
}

#[test]
fn i64_load8u_no_clobber_2_params() {
    // i64.load8_u with 2 params: addr from I32Const so neither param is the
    // load address. The dst pair must not be R0:R1 (params).
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I64Load8U {
            offset: 0,
            align: 0,
        },
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
    ];
    assert_no_clobber(&wasm, 2, "i64.load8_u");
}

#[test]
fn i64_load16s_no_clobber_2_params() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I64Load16S {
            offset: 0,
            align: 0,
        },
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
    ];
    assert_no_clobber(&wasm, 2, "i64.load16_s");
}

#[test]
fn i64_load32u_no_clobber_2_params() {
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I64Load32U {
            offset: 0,
            align: 0,
        },
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
    ];
    assert_no_clobber(&wasm, 2, "i64.load32_u");
}
