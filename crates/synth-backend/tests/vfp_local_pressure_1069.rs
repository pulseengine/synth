//! #1069 (RQ-60-VFPPRESSURE increment 2) — VFP pressure from HOMED LOCALS.
//!
//! jess's discriminating measurement (fixture credit: jess): 60
//! simultaneously-live f32 on the OPERAND STACK compile (the #881 spill rung
//! rescues them), but 14 f32 in HOMED LOCALS do not — a home S-register is
//! pinned for the function's extent and the #881 victim search explicitly
//! skips homes. The 13->14 wall is home residence, not register-file
//! capacity.
//!
//! The fix (rung-only, `vfp_spill_on_exhaustion`): a fresh non-param f32/f64
//! local whose home grant would pin a register above the S7/D3 cap — or whose
//! allocation fails — is FRAME-homed from birth: `local.set` stores to a
//! permanent [SP,#slot], `local.get` loads into a fresh temp. Dominance of
//! every load over its store is inherited from wasm's own def-use semantics
//! (the store IS the def), which is why residence-at-birth is sound where a
//! mid-function eviction of a register home would not be.
//!
//! What this file pins:
//!   * live13 — jess's NEGATIVE CONTROL compiles on the BASE path (no rung),
//!     so its bytes are untouched by construction;
//!   * live14/live16 — red pinned as the base-path exhaustion Err, green via
//!     the backend's full retry ladder (`compile_function`);
//!   * live24 — needs MORE permanent slots than the default 8-slot pool: it
//!     compiles only if the #1069 slot-exhaustion message still triggers the
//!     #587-style pool-grow retry. THE SUBSTRING IS CONTROL FLOW (the #881
//!     lesson): this test fails if the message and the backend's matcher
//!     drift apart;
//!   * live8d — the f64/D-file twin on cortex-m7dp;
//!   * under the rung, no pinned f32 local home sits above S7 (the transient
//!     temp territory S8..S15 the pressure guard needs stays reclaimable).
//!
//! Execution truth (unicorn vs wasmtime, bit-exact) lives in
//! `scripts/repro/vfp_local_pressure_1069_differential.py`.

use synth_backend::ArmBackend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::target::{FPUPrecision, TargetSpec};
use synth_synthesis::instruction_selector::VFP_FRAME_HOME_SLOT_EXHAUSTION;
use synth_synthesis::{ArmOp, InstructionSelector, Reg, RuleDatabase, VfpReg, WasmOp};

/// The fixture shape (same as scripts/repro/vfp_local_pressure_1069.wat):
/// `(param f32) (local f32 x n)` — every local derived from the param, all
/// consumed in one product tree.
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
        ops.push(WasmOp::F32Mul);
    }
    ops.push(WasmOp::End);
    ops
}

fn live_f64_ops(n: u32) -> Vec<WasmOp> {
    let mut ops = Vec::new();
    for k in 1..=n {
        ops.push(WasmOp::LocalGet(0));
        ops.push(WasmOp::F64Const(k as f64 + 0.5));
        ops.push(WasmOp::F64Mul);
        ops.push(WasmOp::LocalSet(k));
    }
    ops.push(WasmOp::LocalGet(1));
    for k in 2..=n {
        ops.push(WasmOp::LocalGet(k));
        ops.push(WasmOp::F64Mul);
    }
    ops.push(WasmOp::End);
    ops
}

fn m7dp_selector(f64_param: bool) -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut s = InstructionSelector::new(db.rules().to_vec());
    s.set_target(Some(FPUPrecision::Double), "cortex-m7dp");
    if f64_param {
        s.set_params_f64(vec![true]);
        s.set_ret_float(false, true);
    } else {
        s.set_params_f32(vec![true]);
        s.set_ret_float(true, false);
    }
    s
}

fn m7dp_config(f64_param: bool) -> CompileConfig {
    let mut cfg = CompileConfig {
        target: TargetSpec::cortex_m7dp(),
        relocatable: true,
        ..CompileConfig::default()
    };
    if f64_param {
        cfg.current_func_params_f64 = vec![true];
        cfg.current_func_ret_f64 = true;
    } else {
        cfg.current_func_params_f32 = vec![true];
        cfg.current_func_ret_f32 = true;
    }
    cfg
}

/// The full backend retry ladder (base -> integer rungs -> VFP rung ->
/// pool-grow inside the rung) — exactly what the CLI compile drives.
fn ladder_compile(name: &str, ops: &[WasmOp], f64_param: bool) -> Result<Vec<u8>, String> {
    let backend = ArmBackend::new();
    backend
        .compile_function(name, ops, &m7dp_config(f64_param))
        .map(|f| f.code)
        .map_err(|e| e.to_string())
}

#[test]
fn live13_negative_control_compiles_on_the_base_path() {
    // jess's negative control: 13 homed locals compile WITHOUT any rung —
    // the ladder never fires for it, so its bytes are byte-identical by
    // construction (the frozen-anchor gates hold the global version of this).
    let ops = live_f32_ops(13);
    let mut sel = m7dp_selector(false);
    sel.select_with_stack(&ops, 1)
        .expect("live13 must keep compiling on the base path (no rung)");
    ladder_compile("live13", &ops, false).expect("live13 must compile through the backend");
}

#[test]
fn live14_homed_locals_red_on_base_green_via_rung() {
    let ops = live_f32_ops(14);
    // RED pinned: the base path (no rung) still raises the honest exhaustion
    // Err — the fix lives behind the #881 rung, not in the default path.
    let mut base = m7dp_selector(false);
    let err = base
        .select_with_stack(&ops, 1)
        .expect_err("14 homed f32 locals must still exhaust the BASE path");
    assert!(
        err.to_string().contains("VFP register file exhausted"),
        "base-path Err must stay the #881 retry trigger substring: {err}"
    );
    // GREEN: the full ladder rescues it.
    ladder_compile("live14", &ops, false)
        .expect("live14 must compile via the VFP rung's frame-homed locals");
}

#[test]
fn live16_compiles_via_rung() {
    let ops = live_f32_ops(16);
    ladder_compile("live16", &ops, false).expect("live16 must compile via the VFP rung");
}

#[test]
fn rung_frame_homes_locals_and_pins_no_home_above_s7() {
    // Under the rung, the selector must (a) emit frame traffic for the
    // overflow locals (VSTR at the def, VLDR at the uses) and (b) never pin
    // a local home above S7 — S8..S15 stay reclaimable temp territory.
    let ops = live_f32_ops(14);
    let mut sel = m7dp_selector(false);
    sel.set_vfp_spill_on_exhaustion(true);
    sel.set_vfp_frame_home_locals(true);
    let instrs = sel
        .select_with_stack(&ops, 1)
        .expect("live14 must compile with the frame-home rung enabled");
    let stores = instrs
        .iter()
        .filter(|i| matches!(&i.op, ArmOp::F32Store { addr, .. } if addr.base == Reg::SP))
        .count();
    let loads = instrs
        .iter()
        .filter(|i| matches!(&i.op, ArmOp::F32Load { addr, .. } if addr.base == Reg::SP))
        .count();
    assert!(
        stores >= 6 && loads >= 6,
        "expected frame-homed local traffic (>=6 overflow locals), got \
         {stores} VSTR / {loads} VLDR to [SP,#imm]"
    );
    // (b): every local.set write-back target (the pinned homes) is at or
    // below S7. Homes are exactly the S-registers a `local.set` copies into
    // via the reinterpret round-trip (F32ReinterpretI32 { sd = home }).
    let high_homes: Vec<VfpReg> = instrs
        .iter()
        .filter_map(|i| match &i.op {
            ArmOp::F32ReinterpretI32 { sd, .. } => Some(*sd),
            _ => None,
        })
        .filter(|sd| {
            !matches!(
                sd,
                VfpReg::S0
                    | VfpReg::S1
                    | VfpReg::S2
                    | VfpReg::S3
                    | VfpReg::S4
                    | VfpReg::S5
                    | VfpReg::S6
                    | VfpReg::S7
            )
        })
        .collect();
    assert!(
        high_homes.is_empty(),
        "no pinned f32 local home may sit above S7 under the rung, got {high_homes:?}"
    );
}

/// #1426 — THE RECOVERY LADDER'S LAST RUNG HAS NO POOL-GROW RETRY, and giving it
/// one is not safe today because the wide-file path MISCOMPILES.
///
/// THE ASYMMETRY. Stages 1 and 2 of the ladder in `arm_backend.rs` each retry with
/// a GROWN slot pool when their failure is slot exhaustion. Stage 3
/// (`vfp-wide-file`, #1267) does not: it calls `full_sequence(None, ...)` and runs
/// with the DEFAULT 8-slot pool while asking the selector to frame-home locals.
/// The two halves each fix exactly what the other hits — stage 2's grown pool ends
/// in register-file exhaustion, which the wide S16..S31 file relieves; the wide
/// file ends in slot-pool exhaustion, which the grown pool relieves — and the
/// combination had never been tried. The external reporter's
/// `controller@0.10.0#step` (#1318) shows both walls in one ladder.
///
/// WHY THE OBVIOUS FIX IS NOT IN THE TREE. Adding the retry (about 20 lines,
/// the same shape as stage 2's) DOES extend reach: this shape compiles, and the
/// wall for the family moves from 60 to 66 locals — SIX locals, measured by applying
/// the retry in a probe: 60..65 compile (1956, 1992, 2028, 2064, 2100, 2136 bytes)
/// and 66 declines. An earlier version of this comment said 72, which was never
/// measured; v0.78's round-2 review derived 66 and found that the grow formula is
/// not the variable (identical outcome at the stage-2 size, at the `I64_SPILL_SLOTS_MAX`
/// cap of 120, and with the cap lifted to 400). The new wall is the genuine
/// `[sp,#imm]` 1020-byte VSTR/VLDR ceiling: at n=66 the rung already asks for offset
/// 1024, so ~128 8-byte slots are the addressable maximum and this family consumes
/// about two per local. But the newly-accepted code is WRONG. Driven
/// through the `#1069` execution differential against wasmtime, every NEGATIVE
/// input returns a result differing from wasmtime in EXACTLY the sign bit
/// (`got ^ want == 0x8000_0000` for -0.0, -1.0, -0.25, -3.14159265, -1e30, -inf;
/// every non-negative input is correct). All 60 factors share the param's sign, so
/// 60 of them multiply to a POSITIVE result — an odd number of sign contributions
/// means one factor is not the value it should be. `live24` above exercises
/// `vfp-frame-locals+pool-grow` and is bit-exact in that same differential, so the
/// defect is in the WIDE-FILE path, not in pool growth.
///
/// That path has encoding tests (`vfp_wide_file_1267.rs` asserts the VPUSH/VPOP
/// pair, its position relative to the frame `sub sp`, and the #1273 stack-param
/// refusal) but NO execution oracle — nothing in `scripts/repro/` covers #1267.
/// Its own header records that nothing on this tree reaches it, and that on the
/// reporter's module it is "reached TWICE and rescues neither call". So extending
/// the ladder would convert two loud declines in a real customer module into
/// possibly-wrong code: "accept more and check less", which the reach rule forbids.
///
/// THIS TEST PINS THE CURRENT, HONEST STATE so the next attempt starts from a
/// failing assertion rather than from scratch: the shape declines, and the ladder
/// REACHES the wide-file rung and dies there on slot exhaustion. When the
/// wide-file miscompile is fixed and the retry added, this test must flip to
/// asserting a successful compile AND `wide60` must join the execution
/// differential's export list — a compile-only green here would be the
/// "it compiles now" claim that says nothing about the code.
fn wide_f32_ops(n: u32) -> Vec<WasmOp> {
    let mut ops = Vec::new();
    for k in 1..=n {
        ops.push(WasmOp::LocalGet(0));
        ops.push(WasmOp::F32Const(k as f32 + 0.5));
        ops.push(WasmOp::F32Mul);
        ops.push(WasmOp::LocalSet(k));
    }
    // RIGHT-leaning consumption: every local stays live simultaneously, so the
    // pressure is homes AND operand stack at once. `live_f32_ops` folds LEFT (two
    // live at a time), which is why none of the other fixtures reach stage 3.
    for k in 1..=n {
        ops.push(WasmOp::LocalGet(k));
    }
    for _ in 1..n {
        ops.push(WasmOp::F32Mul);
    }
    ops.push(WasmOp::End);
    ops
}

#[test]
fn wide60_declines_and_the_ladder_dies_on_the_wide_file_rung_1426() {
    let ops = wide_f32_ops(60);
    // `.map(len)` first: on the FAILING side of this assertion the Ok value is the
    // whole emitted byte vector, and `expect_err` prints it — 2 KB of decimal
    // bytes burying the one fact that matters. The byte COUNT is the useful
    // signal, because it says the rung landed and roughly how big the result is.
    let err = ladder_compile("wide60", &ops, false)
        .map(|code| format!("{} bytes", code.len()))
        .expect_err(
            "60 right-leaning-consumed homed f32 locals must still DECLINE. \
             IF THIS FIRED, THE RUNG LANDED: give the ladder's stage 3 its \
             pool-grow retry and this shape compiles. Before trusting that as \
             reach, flip this test to assert a successful compile AND add a \
             right-leaning 60-local export to scripts/gen_vfp_local_1069.py, \
             regenerate the .wat, and add it to F32_EXPORTS in the #1069 \
             execution differential — the wide-file path emitted SIGN-WRONG \
             code for every negative input when this was measured (#1439), so a \
             compile-only green here says nothing about the bytes",
        );
    // The ladder must REACH the last rung — if it stopped earlier the asymmetry
    // above would be about an unreached rung and this test would prove nothing.
    assert!(
        err.contains("vfp-wide-file"),
        "the ladder must reach the wide-file rung for this shape: {err}"
    );
    // And it must die there on SLOT exhaustion, which is what a grown pool fixes.
    assert!(
        err.contains(VFP_FRAME_HOME_SLOT_EXHAUSTION),
        "the wide-file rung must fail on slot-pool exhaustion (the wall a grown \
         pool relieves): {err}"
    );
    // NEGATIVE CONTROL for the claim that the retry is genuinely absent: stage 2
    // records its grow attempt by name, so the ladder text proves stage 2 HAS a
    // retry while stage 3 does not.
    assert!(
        err.contains("vfp-frame-locals+pool-grow("),
        "stage 2's grow retry must appear, or 'stage 3 lacks one' is not a \
         contrast: {err}"
    );
    assert!(
        !err.contains("vfp-wide-file+pool-grow("),
        "stage 3 must have NO grow retry today — if this fires, the rung landed \
         and this test must be flipped to assert a successful compile AND \
         `wide60` added to the #1069 execution differential (#1426): {err}"
    );
}

#[test]
fn live24_slot_exhaustion_message_still_triggers_the_pool_grow() {
    // 24 homed locals need more PERMANENT frame slots than the default
    // 8-slot pool. With the rung on but the default pool, the selector must
    // fail with the #1069 message (pinning the substring the backend
    // matches); the full ladder must then succeed — which it can ONLY do by
    // recognizing that substring and rerunning with a grown pool. If the
    // message and the matcher ever drift apart, this test goes red.
    let ops = live_f32_ops(24);
    let mut rung_only = m7dp_selector(false);
    rung_only.set_vfp_spill_on_exhaustion(true);
    rung_only.set_vfp_frame_home_locals(true);
    let err = rung_only
        .select_with_stack(&ops, 1)
        .expect_err("24 frame-homed locals must exhaust the default 8-slot pool");
    assert!(
        err.to_string().contains(VFP_FRAME_HOME_SLOT_EXHAUSTION),
        "slot-exhaustion Err must carry the grow-retry trigger substring \
         ({VFP_FRAME_HOME_SLOT_EXHAUSTION:?}): {err}"
    );
    ladder_compile("live24", &ops, false)
        .expect("live24 must compile via the grown pool inside the VFP rung");
}

/// RQ-77-FALCON2 (#1318): the exhaustion diagnostic must cite the OPEN issue
/// about the pool, not the CLOSED one titled about the class v0.76 fixed.
///
/// The residual decline on the external reporter's `controller@0.10.0#step` is
/// this pool exhaustion. It used to cite #1069 — which is CLOSED and titled
/// "GI-FPU-002: three named cascade entry points are the entire remaining
/// gap…", i.e. titled about the `GI-FPU-002` class v0.76 FIXED.
///
/// ITS THREAD DOES DISCUSS THE POOL, and the first version of this comment said
/// it did not — a false statement produced by a narrow regex
/// (`spill.slot pool|pool exhaust|slot pool`) returning a true zero, because the
/// thread writes "pool-grow" and "*slot* exhaustion". Caught by v0.77's round-1
/// cold review. What it actually says is stronger for this change: "the pool-grow
/// rung (#587) cannot fire for this shape". So a reporter sent there reads an
/// argument that the pool mechanism is NOT their problem, while their function
/// declines on precisely that mechanism.
///
/// Citing a closed issue is this repo's documented convention and is NOT the
/// defect (RQ-74-STALEMSG measured 93% of citation sites pointing at closed
/// issues). The defect is that a reporter following THIS citation lands on an
/// issue whose title says the gap is elsewhere and, by implication, already
/// closed.
///
/// WHY A TEST RATHER THAN A COMMENT: the citation is prose inside a format
/// string, so nothing would notice it drifting back. This asserts BOTH
/// directions — the new citation present, the misleading one absent — because
/// asserting only the first would stay green if someone cited both.
///
/// The grow-retry substring is asserted by `live24_...` above and is deliberately
/// untouched by this: `arm_backend.rs` matches it as CONTROL FLOW. The MATCHED
/// CONST is byte-identical to v0.76.0; what changed sits outside it — the `#NNNN:`
/// prefix AND a new explanatory sentence naming #1318 and #1069. An earlier version
/// of this comment said "only the `#NNNN:` prefix … moved", which is false: round 1
/// of the cold review corrected that sentence in `instruction_selector.rs` and round
/// 2 found it still standing HERE, in the twin edited by the same commit. Fixing one
/// of two identical claims is the shape v0.71 recorded as "a twin check does not
/// inherit the fix".
#[test]
fn the_pool_exhaustion_diagnostic_cites_the_open_pool_issue_not_the_closed_class_one() {
    let ops = live_f32_ops(24);
    let mut rung_only = m7dp_selector(false);
    rung_only.set_vfp_spill_on_exhaustion(true);
    rung_only.set_vfp_frame_home_locals(true);
    let msg = rung_only
        .select_with_stack(&ops, 1)
        .expect_err("24 frame-homed locals must exhaust the default 8-slot pool")
        .to_string();
    assert!(
        msg.contains("#1426"),
        "RQ-77-FALCON2: the exhaustion diagnostic must cite #1426, the OPEN issue about the          VFP frame-home spill-slot pool: {msg}"
    );
    assert!(
        !msg.contains("#1069:"),
        "the diagnostic must NOT lead with #1069 — that issue is CLOSED and          titled about the GI-FPU-002 class v0.76 fixed, so a reporter following          it is sent to the wrong defect: {msg}"
    );
    // The grow-retry trigger must survive the reword, or the ladder breaks.
    assert!(
        msg.contains(VFP_FRAME_HOME_SLOT_EXHAUSTION),
        "the control-flow substring must be untouched by the citation change: {msg}"
    );
}

#[test]
fn live8d_f64_locals_red_on_base_green_via_rung() {
    let ops = live_f64_ops(8);
    let mut base = m7dp_selector(true);
    let err = base
        .select_with_stack(&ops, 1)
        .expect_err("8 homed f64 locals must still exhaust the BASE path");
    assert!(
        err.to_string().contains("VFP D-register file exhausted"),
        "base-path Err must stay the #881 D-file retry trigger substring: {err}"
    );
    ladder_compile("live8d", &ops, true)
        .expect("live8d must compile via the VFP rung's frame-homed f64 locals");
    // Rung-level: expect D-frame traffic (F64Store/F64Load to [SP,#imm]).
    let mut sel = m7dp_selector(true);
    sel.set_vfp_spill_on_exhaustion(true);
    sel.set_vfp_frame_home_locals(true);
    let instrs = sel
        .select_with_stack(&ops, 1)
        .expect("live8d must compile with the rung enabled");
    let d_stores = instrs
        .iter()
        .filter(|i| matches!(&i.op, ArmOp::F64Store { addr, .. } if addr.base == Reg::SP))
        .count();
    let d_loads = instrs
        .iter()
        .filter(|i| matches!(&i.op, ArmOp::F64Load { addr, .. } if addr.base == Reg::SP))
        .count();
    assert!(
        d_stores >= 3 && d_loads >= 3,
        "expected frame-homed f64 local traffic, got {d_stores} VSTR.64 / \
         {d_loads} VLDR.64 to [SP,#imm]"
    );
}

#[test]
fn plain_rung_stays_yesterdays_path_for_shapes_it_already_rescues() {
    // The rate@0.7.0#tick class: f64 local homes ABOVE the D3 cap that the
    // PLAIN #881 rung (frame lever off) already rescues. Found empirically at
    // authoring: the first draft gated frame-homing on the rung flag itself,
    // and the real falcon `rate.o` moved bytes — rate#tick compiles TODAY via
    // the plain rung with above-cap homes. The fix is ladder ORDER: the
    // frame lever is a separate LAST-resort stage the backend tries only
    // after the plain rung also failed. This test pins all three premises:
    //  (1) the class is red on the base path (it genuinely needs the rung);
    //  (2) the plain rung still rescues it BY ITSELF (so the ladder's stage 1
    //      succeeds and stage 2 is never consulted — yesterday's bytes by
    //      construction);
    //  (3) the frame lever WOULD produce different instructions for it — the
    //      reason the ordering is load-bearing and not a stylistic choice.
    // 4 f64 local homes (D1..D4 with the param in D0 — D4 sits ABOVE the
    // D3 cap, but 4 locals alone still fit the base path) plus an 8-deep f64
    // constant stack: the stack pressure exhausts the base path, and the
    // plain rung rescues it by spilling STACK values only — homes untouched.
    let mut ops = Vec::new();
    for k in 1..=4u32 {
        ops.push(WasmOp::LocalGet(0));
        ops.push(WasmOp::F64Const(k as f64 + 0.5));
        ops.push(WasmOp::F64Mul);
        ops.push(WasmOp::LocalSet(k));
    }
    for k in 0..8 {
        ops.push(WasmOp::F64Const(k as f64 + 0.25));
    }
    for _ in 0..7 {
        ops.push(WasmOp::F64Mul);
    }
    for k in 1..=4u32 {
        ops.push(WasmOp::LocalGet(k));
        ops.push(WasmOp::F64Mul);
    }
    ops.push(WasmOp::End);
    let mut base = m7dp_selector(true);
    let err = base
        .select_with_stack(&ops, 1)
        .expect_err("4 homed f64 locals + 8-deep f64 stack must exhaust the base path");
    assert!(
        err.to_string().contains("VFP D-register file exhausted"),
        "base-path Err must be the D-file exhaustion trigger: {err}"
    );
    let mut plain = m7dp_selector(true);
    plain.set_vfp_spill_on_exhaustion(true);
    let plain_out = plain
        .select_with_stack(&ops, 1)
        .expect("the PLAIN #881 rung must still rescue this shape by itself");
    let mut framed = m7dp_selector(true);
    framed.set_vfp_spill_on_exhaustion(true);
    framed.set_vfp_frame_home_locals(true);
    let framed_out = framed
        .select_with_stack(&ops, 1)
        .expect("the frame lever must also compile the shape");
    assert_ne!(
        format!("{plain_out:?}"),
        format!("{framed_out:?}"),
        "the frame lever changes this shape's instructions — if this ever \
         becomes equal the ordering premise should be re-examined"
    );
    ladder_compile("d5", &ops, true).expect("the ladder must compile the shape");
}

#[test]
fn deep_operand_stack_rescue_unchanged_by_the_local_work() {
    // The #881 stack-value rescue (jess's 60-deep column) must keep working:
    // 20 simultaneously-live f32 pushed as one right-leaning tree, no locals.
    let mut ops = Vec::new();
    ops.push(WasmOp::LocalGet(0));
    for k in 0..19 {
        ops.push(WasmOp::F32Const(k as f32 + 1.5));
    }
    for _ in 0..19 {
        ops.push(WasmOp::F32Add);
    }
    ops.push(WasmOp::End);
    ladder_compile("deep20", &ops, false)
        .expect("20-deep operand-stack pressure must still be rescued by #881");
}
