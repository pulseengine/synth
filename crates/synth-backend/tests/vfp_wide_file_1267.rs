//! RQ-67-VFPREACH (#1267) — the AAPCS callee-saved VFP half, S16-S31 / D8-D15.
//!
//! WHY THIS TEST EXISTS IN THIS FORM. The wide-file rung is the LAST rung of
//! the recovery ladder, reached only after every other escape ended in
//! `GI-FPU-002`. Measured on this tree, NOTHING REACHES IT: the two shipped
//! pressure fixtures are fully rescued on `cortex-m7dp` by the #881 spill rung
//! (7 functions) and the #1069 frame-home rung (4 functions), and two
//! deliberately-constructed shapes — 14 f64 live on the operand stack, and 12
//! f64 locals live across calls — were rescued by those same rungs too.
//!
//! So the rung cannot be demonstrated by compiling a corpus module. The honest
//! alternative is to drive the flag DIRECTLY and assert the emitted stream,
//! which is what this file does: reached-by-test rather than unreached.
//!
//! CORRECTED BY RQ-73-FALCONFIXTURE (v0.73, #1318). The paragraph above used to
//! end: "The one known module that defeats both existing rungs is the
//! reporter's flight tick (#1267), which is NOT OBTAINABLE FROM ANY PUBLISHED
//! ARTIFACT." Both halves of that were false, and it was the stated reason
//! nobody looked again:
//!
//!   * It IS obtainable. #1318's `errors.zip` attachment contains `opt.wasm`
//!     and `fused.wasm` themselves, not only logs.
//!   * NOTHING REACHES IT is false for that module. Measured at v0.72.0 with
//!     `SYNTH_RECOVERY_STATS=1` over its 17 functions (9 compile at base, 1 is
//!     rescued by a rung, 7 exhaust):
//!
//!         rung                          reached  rescued
//!         vfp-spill                        3        0
//!         vfp-frame-locals                 3        1
//!         vfp-frame-locals+pool-grow       1        0
//!         vfp-wide-file                    2        0
//!
//! So this rung is reached TWICE by a real module and rescues neither call.
//! The file's design is still right — driving the flag directly is the only way
//! to assert the emitted stream — but its justification must not claim the
//! module cannot be had. `scripts/repro/falcon_opt_1318.wat` now commits the
//! reduced shape behind 6 of those 7 declines.
//!
//! WHAT IS ASSERTED, and each is a property that fails SILENTLY if wrong:
//!   1. the save/restore pair is emitted at all;
//!   2. the VPUSH lands AFTER the core `push` and BEFORE the frame `sub sp`,
//!      because it moves SP by 64 bytes and the #881 spill slots are addressed
//!      `[sp,#off]` against the frame that `sub` allocates;
//!   3. every return is preceded by the VPOP;
//!   4. a function with stack-passed params is REFUSED, not mis-compiled —
//!      incoming stack args are addressed `frame_size + 24 + nsaa_k` where 24
//!      hardcodes the prologue size (#1273), so a 64-byte VPUSH would shift
//!      them silently;
//!   5. with the flag OFF the stream contains neither op — the byte-identity
//!      property the whole lane rests on.

use synth_core::target::FPUPrecision;
use synth_synthesis::{ArmOp, InstructionSelector, Reg, RuleDatabase, WasmOp};

fn m7dp_selector() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut s = InstructionSelector::new(db.rules().to_vec());
    s.set_target(Some(FPUPrecision::Double), "cortex-m7dp");
    s.set_params_f32(vec![true]);
    s.set_ret_float(true, false);
    s
}

/// `n` f32 values homed in locals — the #1069 shape, enough to need real
/// register work without depending on any particular rescue rung.
fn live_f32_ops(n: u32) -> Vec<WasmOp> {
    let mut ops = Vec::new();
    for k in 1..=n {
        ops.push(WasmOp::LocalGet(0));
        ops.push(WasmOp::F32Const(k as f32 + 0.5));
        ops.push(WasmOp::F32Mul);
        ops.push(WasmOp::LocalSet(k));
    }
    ops.push(WasmOp::LocalGet(1));
    for k in 2..=n {
        ops.push(WasmOp::LocalGet(k));
        ops.push(WasmOp::F32Add);
    }
    ops
}

fn index_of(instrs: &[synth_synthesis::ArmInstruction], want: &ArmOp) -> Option<usize> {
    instrs.iter().position(|i| &i.op == want)
}

#[test]
fn wide_file_off_emits_neither_op_1267() {
    // The byte-identity property, asserted rather than assumed: with the flag
    // off, the callee-saved VFP half is untouched.
    let mut sel = m7dp_selector();
    sel.set_vfp_spill_on_exhaustion(true);
    let instrs = sel
        .select_with_stack(&live_f32_ops(8), 1)
        .expect("must compile");
    assert!(
        index_of(&instrs, &ArmOp::VPushCalleeSavedVfp).is_none(),
        "flag OFF must not save the callee-saved VFP half"
    );
    assert!(
        index_of(&instrs, &ArmOp::VPopCalleeSavedVfp).is_none(),
        "flag OFF must not restore the callee-saved VFP half"
    );
}

#[test]
fn wide_file_on_saves_and_restores_1267() {
    let mut sel = m7dp_selector();
    sel.set_vfp_spill_on_exhaustion(true);
    sel.set_vfp_wide_file(true);
    let instrs = sel
        .select_with_stack(&live_f32_ops(8), 1)
        .expect("must compile");
    assert!(
        index_of(&instrs, &ArmOp::VPushCalleeSavedVfp).is_some(),
        "flag ON must save d8-d15: the callee owes the caller those registers"
    );
    let pops = instrs
        .iter()
        .filter(|i| matches!(i.op, ArmOp::VPopCalleeSavedVfp))
        .count();
    let rets = instrs
        .iter()
        .filter(|i| matches!(&i.op, ArmOp::Pop { regs } if regs.contains(&Reg::PC)))
        .count();
    assert!(rets > 0, "fixture must actually return");
    assert_eq!(
        pops, rets,
        "every return must be preceded by a restore; a missing one is the exact \
         failure this lane exists to prevent"
    );
}

#[test]
fn vpush_precedes_the_frame_sub_1267() {
    // THE PLACEMENT PROPERTY. VPUSH moves SP by 64 bytes. The #881 spill slots
    // are `[sp,#off]` against the frame the `sub sp` allocates, so the save
    // MUST precede that sub — after it, every spill offset would shift and the
    // code would read the wrong stack slots without faulting.
    let mut sel = m7dp_selector();
    sel.set_vfp_spill_on_exhaustion(true);
    sel.set_vfp_wide_file(true);
    let instrs = sel
        .select_with_stack(&live_f32_ops(10), 1)
        .expect("must compile");

    let vpush = index_of(&instrs, &ArmOp::VPushCalleeSavedVfp).expect("save must be emitted");
    let core_push = instrs
        .iter()
        .position(|i| matches!(&i.op, ArmOp::Push { regs } if regs.contains(&Reg::LR)))
        .expect("core prologue push must exist");
    assert!(
        core_push < vpush,
        "the VFP save must follow the core push (AAPCS prologue order)"
    );
    if let Some(frame_sub) = instrs
        .iter()
        .position(|i| matches!(&i.op, ArmOp::Sub { rd: Reg::SP, .. }))
    {
        assert!(
            vpush < frame_sub,
            "the VFP save must PRECEDE the frame sub: it moves SP by 64 bytes and \
             the spill slots are addressed against the frame that sub allocates"
        );
    }
}

#[test]
fn stack_passed_params_are_refused_not_miscompiled_1267() {
    // #1273: incoming stack args are addressed `frame_size + 24 + nsaa_k`,
    // where 24 hardcodes the prologue's pushed-register bytes. A 64-byte VPUSH
    // makes that arithmetic read from the wrong place, silently. Until #1273
    // derives the offset from the emitted prologue, the rung must DECLINE —
    // which is what the function already did before the rung existed, so the
    // refusal costs no reach.
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_target(Some(FPUPrecision::Double), "cortex-m7dp");
    // 20 f32 params. NOTE THE ABI, which an earlier version of this test got
    // wrong: under hard-float AAPCS-VFP, f32 ARGUMENTS are passed in S0-S15 —
    // the VFP argument registers — not in r0-r3. So eight f32 params never
    // reach the stack at all. Sixteen fill the VFP argument registers; the
    // rest spill to the stack, which is what makes `param_layout.stack`
    // non-empty and drives the refusal under test.
    sel.set_params_f32(vec![true; 20]);
    sel.set_ret_float(true, false);
    sel.set_vfp_spill_on_exhaustion(true);
    sel.set_vfp_wide_file(true);

    let mut ops = vec![WasmOp::LocalGet(0)];
    for k in 1..20 {
        ops.push(WasmOp::LocalGet(k));
        ops.push(WasmOp::F32Add);
    }
    let err = sel.select_with_stack(&ops, 20);
    assert!(
        err.is_err(),
        "a stack-passed-param function must be REFUSED under the wide rung, got Ok"
    );
    let msg = format!("{:?}", err.unwrap_err());
    assert!(
        msg.contains("stack-passed") || msg.contains("1273"),
        "the refusal must name its reason so it is diagnosable, got: {msg}"
    );
}
