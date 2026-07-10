//! #498 (VCR-ORACLE-001, epic #242) — end-to-end close-verify for the latent
//! branch-displacement drift the estimator gaps warned about.
//!
//! The `estimator_encoder_agreement` oracle pins the per-op sizes; this test
//! closes the loop the issue's *acceptance criterion* asks for: a `block`/
//! `br_if` whose body spans a mis-sizable op (`popcnt`, an ~86-byte pseudo-op
//! expansion) **between the conditional branch and its target**, lowered on the
//! OPTIMIZED path, must resolve the branch displacement against the op's REAL
//! encoded length — not the old `_ => 2` default.
//!
//! Why `popcnt` is the sharpest probe: the pre-#498 estimator sized it as 2
//! bytes while the encoder emits 86. A forward `br_if` that skips the popcnt
//! would then be given a displacement short by 84 bytes, landing the branch in
//! the MIDDLE of the popcnt expansion (the #483-class miscompile, here between
//! branch and target rather than in a sub-word store). With the estimator
//! mirroring the encoder (86), the displacement lands exactly on the real
//! continuation.
//!
//! This test sits downstream of synth-synthesis, so it can lower on the real
//! optimized path AND re-encode with the real Thumb-2 encoder — checking the
//! whole chain (estimator → branch resolution → emitted bytes), not just the
//! per-op mirror.

use synth_backend::ArmEncoder;
use synth_core::WasmOp;
use synth_synthesis::{ArmOp, OptimizerBridge, estimate_arm_byte_size};

/// `(block (br_if 0 (local.get 0)) (drop (i32.popcnt (local.get 0))))`
///
/// The `br_if` targets the block end; the `popcnt` sits between the branch and
/// that end. In both directions the observable is where the branch lands.
fn block_brif_spanning_popcnt() -> Vec<WasmOp> {
    vec![
        WasmOp::Block,
        WasmOp::LocalGet(0),
        WasmOp::BrIf(0), // forward branch to block end (past the popcnt)
        WasmOp::LocalGet(0),
        WasmOp::I32Popcnt, // ~86-byte expansion between branch and target
        WasmOp::Drop,
        WasmOp::End,
    ]
}

#[test]
fn brif_displacement_resolves_past_popcnt_body() {
    let bridge = OptimizerBridge::new();
    let (instrs, _cfg, _stats) = bridge
        .optimize_full(&block_brif_spanning_popcnt())
        .expect("optimize_full accepts the block/br_if shape");
    let arm = bridge
        .ir_to_arm(&instrs, 1)
        .expect("ir_to_arm lowers the shape on the optimized path (no decline)");

    // Precondition: the shape actually stayed on the optimized path WITH the
    // mis-sizable op between the branch and its target. If a future change
    // declines this shape (or stops emitting Popcnt), the test would pass
    // vacuously — so assert both are present.
    let popcnt_idx = arm
        .iter()
        .position(|o| matches!(o, ArmOp::Popcnt { .. }))
        .expect("optimized path emits ArmOp::Popcnt for i32.popcnt");
    let branch_idx = arm
        .iter()
        .position(|o| matches!(o, ArmOp::BCondOffset { .. }))
        .expect("br_if resolved to a BCondOffset on the optimized path");
    assert!(
        branch_idx < popcnt_idx,
        "the conditional branch must precede the popcnt it spans \
         (branch_idx={branch_idx}, popcnt_idx={popcnt_idx})"
    );

    // Build the REAL byte layout from the encoder, and confirm the estimator
    // matched it op-for-op (the property that makes the displacement sound).
    let enc = ArmEncoder::new_thumb2();
    let mut real_offsets: Vec<usize> = Vec::with_capacity(arm.len() + 1);
    let mut cur = 0usize;
    for op in &arm {
        let real = enc
            .encode(op)
            .unwrap_or_else(|e| panic!("encoder rejected {op:?}: {e:?}"))
            .len();
        let est = estimate_arm_byte_size(op);
        assert_eq!(
            est, real,
            "estimator↔encoder drift on {op:?}: est {est} != real {real} \
             (the #498 latent branch-displacement drift)"
        );
        real_offsets.push(cur);
        cur += real;
    }
    real_offsets.push(cur);

    // The popcnt is genuinely large — this is the whole point (a 2-byte
    // mis-estimate would have been off by ~84).
    let popcnt_len = enc.encode(&arm[popcnt_idx]).unwrap().len();
    assert!(
        popcnt_len > 80,
        "popcnt expansion should be large (got {popcnt_len}) — otherwise this \
         fixture would not exercise the drift"
    );

    // End-to-end: the resolved displacement, applied to the REAL branch byte
    // position, must land on a REAL instruction boundary that is PAST the
    // popcnt body (the block continuation). Thumb PC = branch_byte + 4.
    let ArmOp::BCondOffset { offset, .. } = arm[branch_idx] else {
        unreachable!()
    };
    let branch_byte = real_offsets[branch_idx] as i32;
    let popcnt_end = real_offsets[popcnt_idx + 1] as i32;
    let landing = branch_byte + 4 + offset * 2;

    assert!(
        real_offsets.iter().any(|&b| b as i32 == landing),
        "resolved br_if lands at byte {landing}, not on any real instruction \
         boundary {real_offsets:?} — the displacement drifted from the encoder"
    );
    assert!(
        landing >= popcnt_end,
        "resolved br_if lands at byte {landing}, INSIDE/before the popcnt body \
         (ends at {popcnt_end}) — the #498 miscompile: displacement short by the \
         under-estimated popcnt length"
    );
}
