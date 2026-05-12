//! Audit: the optimizer path (`optimize_full + ir_to_arm`) must not write
//! AAPCS param registers before they're read by `LocalGet`.
//!
//! Issue #103 covered `select_with_stack`'s i64 ops; this audit covers the
//! optimizer path, where the corresponding bug class is `Opcode::*`
//! handlers hardcoding `rd: Reg::R3` (or any of R0..R3). Found via the
//! systematic audit triggered by PR #100's fuzz harness.

use synth_synthesis::{ArmOp, OptimizerBridge, Reg, WasmOp};

fn compile_optimized(wasm_ops: &[WasmOp], num_params: usize) -> Vec<ArmOp> {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge.optimize_full(wasm_ops).expect("optimize_full");
    bridge.ir_to_arm(&ir, num_params)
}

fn writes(op: &ArmOp) -> Vec<Reg> {
    match op {
        ArmOp::Add { rd, .. }
        | ArmOp::Sub { rd, .. }
        | ArmOp::Adds { rd, .. }
        | ArmOp::Adc { rd, .. }
        | ArmOp::Subs { rd, .. }
        | ArmOp::Sbc { rd, .. }
        | ArmOp::And { rd, .. }
        | ArmOp::Orr { rd, .. }
        | ArmOp::Eor { rd, .. }
        | ArmOp::Mov { rd, .. }
        | ArmOp::Mvn { rd, .. }
        | ArmOp::Movw { rd, .. }
        | ArmOp::Movt { rd, .. }
        | ArmOp::Lsl { rd, .. }
        | ArmOp::Lsr { rd, .. }
        | ArmOp::Asr { rd, .. }
        | ArmOp::Ror { rd, .. }
        | ArmOp::LslReg { rd, .. }
        | ArmOp::LsrReg { rd, .. }
        | ArmOp::AsrReg { rd, .. }
        | ArmOp::RorReg { rd, .. }
        | ArmOp::Rsb { rd, .. }
        | ArmOp::Mul { rd, .. }
        | ArmOp::Sdiv { rd, .. }
        | ArmOp::Udiv { rd, .. }
        | ArmOp::Mls { rd, .. }
        | ArmOp::Clz { rd, .. }
        | ArmOp::Rbit { rd, .. }
        | ArmOp::Popcnt { rd, .. }
        | ArmOp::Sxtb { rd, .. }
        | ArmOp::Sxth { rd, .. }
        | ArmOp::Ldr { rd, .. }
        | ArmOp::Ldrb { rd, .. }
        | ArmOp::Ldrsb { rd, .. }
        | ArmOp::Ldrh { rd, .. }
        | ArmOp::Ldrsh { rd, .. } => vec![*rd],
        _ => Vec::new(),
    }
}

/// Compile `wasm_ops` through the optimizer and assert that no
/// instruction emitted up to the first MOV-to-R0 (epilogue) writes to
/// any AAPCS param register. (Without source-line info we use a
/// conservative proxy: scan the ARM output; the optimizer-emitted
/// epilogue is the trailing `Mov R0, ...; Pop` pair, so we check
/// everything before the LAST Mov-to-R0.)
fn assert_no_clobber_before_epilogue(arm: &[ArmOp], num_params: usize, label: &str) {
    let param_regs: Vec<Reg> = (0..num_params.min(4))
        .map(|i| match i {
            0 => Reg::R0,
            1 => Reg::R1,
            2 => Reg::R2,
            3 => Reg::R3,
            _ => unreachable!(),
        })
        .collect();

    // Find the index of the last result-Mov to R0 / R0:R1 — everything
    // before that is "body". We define the epilogue as: from the last
    // `Mov { rd: R0, .. }` to the end. If there's no Mov-to-R0, treat
    // the entire stream as body.
    let mut last_mov_r0_idx: Option<usize> = None;
    for (i, op) in arm.iter().enumerate() {
        if let ArmOp::Mov { rd: Reg::R0, .. } = op {
            last_mov_r0_idx = Some(i);
        }
    }
    let body_end = last_mov_r0_idx.unwrap_or(arm.len());

    for op in &arm[..body_end] {
        for w in writes(op) {
            if param_regs.contains(&w) {
                panic!(
                    "[{label}] AAPCS clobber in optimized path: op writes \
                     param reg {w:?}. Op: {op:?}. Full sequence: {:#?}",
                    arm
                );
            }
        }
    }
}

#[test]
fn optimized_i32_add_4params_does_not_clobber_r3() {
    // 4 params (R0..R3 live). Compute `local.get 0 + local.get 1` (uses
    // R0 + R1, result via Add). The Add's dest must NOT be R3 (or any
    // other param reg). Pre-fix, Opcode::Add hardcoded `rd = Reg::R3`,
    // clobbering the 4th param even though it wasn't an input.
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::I32Add,
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "i32_add_4params");
}

#[test]
fn optimized_i32_sub_4params_does_not_clobber_r3() {
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::I32Sub,
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "i32_sub_4params");
}

#[test]
fn optimized_i32_mul_4params_does_not_clobber_r3() {
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::I32Mul,
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "i32_mul_4params");
}

#[test]
fn optimized_i32_load_4params_does_not_clobber_r3() {
    // The MemLoad handler also used to hardcode `rd = Reg::R3`.
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::I32Load {
            offset: 0,
            align: 0,
        },
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "i32_load_4params");
}

#[test]
fn optimized_i32_load8u_4params_does_not_clobber_r3() {
    let wasm = vec![
        WasmOp::LocalGet(0),
        WasmOp::I32Load8U {
            offset: 0,
            align: 0,
        },
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "i32_load8u_4params");
}

#[test]
fn optimized_global_get_4params_does_not_clobber_r3() {
    let wasm = vec![
        WasmOp::GlobalGet(0),
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "global_get_4params");
}

#[test]
fn optimized_memory_size_4params_does_not_clobber_r3() {
    let wasm = vec![
        WasmOp::MemorySize(0),
        WasmOp::LocalGet(2),
        WasmOp::Drop,
        WasmOp::LocalGet(3),
        WasmOp::Drop,
        WasmOp::Drop,
    ];
    let arm = compile_optimized(&wasm, 4);
    assert_no_clobber_before_epilogue(&arm, 4, "memory_size_4params");
}
