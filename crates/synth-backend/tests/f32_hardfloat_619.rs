//! GI-FPU-002 (#619/#369) phase-1: scalar f32 hard-float reachability on the
//! direct (`select_with_stack`) selector.
//!
//! Locks the pieces the Python execution differential
//! (`scripts/repro/f32_vfp_619_differential.py`) validates end-to-end, but that
//! CI can gate without unicorn/wasmtime:
//!   * f32 params are homed in AAPCS-VFP argument S-registers (S0, S1, …), and
//!     `f32.add` routes through the real VFP value stack (not the old blind
//!     round-robin `select_default`);
//!   * a non-FPU target honest-rejects f32 (never a soft-float miscompile);
//!   * `f32.convert_i32_s` encodes to the SIGNED VCVT (the previously-swapped
//!     signed/unsigned constant is fixed).

use synth_backend::ArmEncoder;
use synth_core::target::FPUPrecision;
use synth_synthesis::{ArmOp, InstructionSelector, Reg, RuleDatabase, VfpReg, WasmOp};

fn m4f_selector() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut s = InstructionSelector::new(db.rules().to_vec());
    s.set_target(Some(FPUPrecision::Single), "cortex-m4f");
    s
}

#[test]
fn f32_params_home_in_s0_s1_and_add_uses_vfp_stack() {
    // (param f32 f32) f32.add — the differential's `fadd`.
    let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Add];
    let mut sel = m4f_selector();
    sel.set_params_f32(vec![true, true]);
    let instrs = sel
        .select_with_stack(&ops, 2)
        .expect("f32.add must compile on cortex-m4f via the VFP value stack");

    // The add must be a real VADD.F32 whose operands are the two AAPCS-VFP
    // param homes S0 (param 0) and S1 (param 1) — proving the value stack, not
    // the blind round-robin allocator, chose the registers.
    let add = instrs
        .iter()
        .find_map(|i| match &i.op {
            ArmOp::F32Add { sd, sn, sm } => Some((*sd, *sn, *sm)),
            _ => None,
        })
        .expect("must emit an ArmOp::F32Add");
    let (_sd, sn, sm) = add;
    assert!(
        (sn == VfpReg::S0 && sm == VfpReg::S1) || (sn == VfpReg::S1 && sm == VfpReg::S0),
        "f32.add operands must be the param homes S0/S1, got sn={sn:?} sm={sm:?}"
    );
}

#[test]
fn f32_honest_rejects_on_non_fpu_target() {
    let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::F32Add];
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec()); // no FPU (cortex-m3 default)
    sel.set_params_f32(vec![true, true]);
    let err = sel
        .select_with_stack(&ops, 2)
        .expect_err("f32 must be rejected on a non-FPU target");
    let msg = format!("{err}");
    assert!(
        msg.contains("GI-FPU-002") && msg.to_lowercase().contains("fpu"),
        "reject message must name the FPU requirement: {msg}"
    );
}

#[test]
fn f32_convert_i32_s_encodes_signed_vcvt() {
    // The signed convert must be VCVT.F32.S32 (op bit set): base 0xEEB80AC0,
    // whose Thumb-2 second halfword is 0x0AC0. The unsigned convert is 0x0A40.
    let enc = ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Single));
    let signed = enc
        .encode(&ArmOp::F32ConvertI32S {
            sd: VfpReg::S0,
            rm: Reg::R0,
        })
        .expect("encode F32ConvertI32S");
    let unsigned = enc
        .encode(&ArmOp::F32ConvertI32U {
            sd: VfpReg::S0,
            rm: Reg::R0,
        })
        .expect("encode F32ConvertI32U");
    assert_ne!(
        signed, unsigned,
        "signed and unsigned f32 convert must differ (they were swapped/aliased)"
    );
    // VCVT is the second instruction (after VMOV Sd, Rm); its low halfword-pair
    // is the 4 trailing bytes. Signed = ...0AC0, unsigned = ...0A40 (LE).
    assert_eq!(
        &signed[6..8],
        &[0xC0, 0x0A],
        "F32ConvertI32S must be VCVT.F32.S32 (0x0AC0), got {:02x?}",
        &signed[6..8]
    );
    assert_eq!(
        &unsigned[6..8],
        &[0x40, 0x0A],
        "F32ConvertI32U must be VCVT.F32.U32 (0x0A40), got {:02x?}",
        &unsigned[6..8]
    );
}
