//! Try to reproduce the AAPCS clobber fuzz crash from PR #100.
//!
//! Crash signature:
//!   ARM instr at wasm line 1 writes param reg R1 before LocalGet(1) at line 5.
//!   Op: Mov { rd: R1, op2: Reg(R2) }
//!   Sequence: [Push, I64Const{rdlo:R2,rdhi:R3,value:0}, Mov{rd:R1,op2:Reg(R2)}, Pop]
//!
//! Test a range of plausible wasm sequences and assert no AAPCS clobber.

use synth_synthesis::{ArmOp, InstructionSelector, Reg, WasmOp};

/// Helper: extract source line numbers and Mov destinations.
fn run(wasm: &[WasmOp], num_params: u32) -> Vec<synth_synthesis::ArmInstruction> {
    let mut s = InstructionSelector::new(vec![]);
    s.select_with_stack(wasm, num_params)
        .expect("should compile")
}

fn first_local_get(wasm: &[WasmOp], p: u32) -> Option<usize> {
    wasm.iter().enumerate().find_map(|(i, op)| match op {
        WasmOp::LocalGet(idx) if *idx == p => Some(i),
        _ => None,
    })
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
        ArmOp::Movt { rd, .. } => vec![*rd],
        ArmOp::I64Const { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        ArmOp::I64Ldr { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        ArmOp::I64ExtendI32U { rdlo, rdhi, .. } | ArmOp::I64ExtendI32S { rdlo, rdhi, .. } => {
            vec![*rdlo, *rdhi]
        }
        ArmOp::I64Extend8S { rdlo, rdhi, .. }
        | ArmOp::I64Extend16S { rdlo, rdhi, .. }
        | ArmOp::I64Extend32S { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        ArmOp::I32WrapI64 { rd, .. } => vec![*rd],
        ArmOp::I64Mul { rd_lo, rd_hi, .. }
        | ArmOp::I64Shl { rd_lo, rd_hi, .. }
        | ArmOp::I64ShrU { rd_lo, rd_hi, .. }
        | ArmOp::I64ShrS { rd_lo, rd_hi, .. } => vec![*rd_lo, *rd_hi],
        _ => Vec::new(),
    }
}

fn check_no_clobber(wasm: &[WasmOp], num_params: u32, label: &str) {
    let instrs = run(wasm, num_params);
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
        for ai in &instrs {
            let line = match ai.source_line {
                Some(l) => l,
                None => continue,
            };
            if line >= first_read {
                break;
            }
            for w in writes(&ai.op) {
                assert_ne!(
                    w, param_reg,
                    "[{label}] AAPCS clobber: ARM instr at wasm line {line} writes \
                     param reg {param_reg:?} before LocalGet({p}) at line {first_read}. \
                     Op: {:?}. Sequence: {:#?}",
                    ai.op, instrs
                );
            }
        }
    }
}

/// Reproduce the harness invariant: build a sequence with `LocalGet(p)` for
/// each param, but place them AFTER an i64 op, so anything that touches
/// a param-region register pre-LocalGet is a clobber.
#[test]
fn aapcs_i64_const_drop_localgets_2_params() {
    let wasm = vec![
        WasmOp::I64Const(0),
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
    ];
    check_no_clobber(&wasm, 2, "i64const-drop-localgets");
}

#[test]
fn aapcs_i64_extend_then_localgets_2_params() {
    let wasm = vec![
        WasmOp::I32Const(7),
        WasmOp::I64ExtendI32U,
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
    ];
    check_no_clobber(&wasm, 2, "i64extend-then-localgets");
}

#[test]
fn aapcs_i64_const_localset0_localgets_2_params() {
    // LocalSet to a param slot would overwrite the param. Even so, the
    // assertion is about writes that occur BEFORE the first LocalGet of
    // each param — these should not clobber.
    let wasm = vec![
        WasmOp::I64Const(0xAABBCCDD),
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
    ];
    check_no_clobber(&wasm, 2, "i64const-large");
}

#[test]
fn aapcs_i64_arith_then_localgets_3_params() {
    let wasm = vec![
        WasmOp::I64Const(1),
        WasmOp::I64Const(2),
        WasmOp::I64Add,
        WasmOp::Drop,
        WasmOp::LocalGet(0),
        WasmOp::Drop,
        WasmOp::LocalGet(1),
        WasmOp::Drop,
        WasmOp::LocalGet(2),
        WasmOp::Drop,
    ];
    check_no_clobber(&wasm, 3, "i64-add-3params");
}

/// Reproduce specifically the fuzz-finding shape:
/// `[Push, I64Const{rdlo:R2,rdhi:R3,value:0}, Mov{rd:R1,op2:Reg(R2)}, Pop]`
/// with a middle op that emits a Mov to a low register.
#[test]
fn aapcs_i64_const_then_some_op_2_params() {
    // Try several middle ops that emit something
    for middle in [
        WasmOp::I32Const(0),
        WasmOp::I64Eqz,
        WasmOp::I64Clz,
        WasmOp::I64Ctz,
        WasmOp::I64Popcnt,
    ] {
        let wasm = vec![
            WasmOp::I64Const(0),
            middle.clone(),
            WasmOp::Drop,
            WasmOp::LocalGet(0),
            WasmOp::Drop,
            WasmOp::LocalGet(1),
            WasmOp::Drop,
        ];
        check_no_clobber(&wasm, 2, &format!("i64const-{middle:?}"));
    }
}
