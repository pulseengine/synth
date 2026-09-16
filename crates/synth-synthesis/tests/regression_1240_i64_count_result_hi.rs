//! #1240 — `i64.clz` / `i64.ctz` / `i64.popcnt` returned the OPERAND's high
//! word on the optimized path.
//!
//! The name of the issue points at a missing zero-fill. It was not one.
//! `ir_to_arm` emits `Mov { rd: rd_hi, op2: Imm(0) }` for all three ops and
//! always has (#1048). The defect was in the EPILOGUE's choice of register.
//!
//! It resolves the i64 return value's high half as
//!
//! ```text
//! last_result_vreg_hi.and_then(|v| vreg_to_arm.get(&v)).or(last_result_vreg_hi_reg)
//! ```
//!
//! where `last_result_vreg_hi_reg` is the physical stash these three ops set,
//! because they carry no `dest_hi` vreg to record. But `last_result_vreg_hi`
//! is assigned `Some(..)` in 25 places and `None` in NONE, so after any
//! earlier i64 op in the same function it is permanently `Some` — the `.or()`
//! fallback was dead code, and the epilogue moved the STALE pair's high
//! register into R1. That register still held the operand's high word, which
//! is exactly the wrong answer the self-contained boot sweep observed on
//! `clz64`, `ctz64` (10 vectors each) and `popcnt64` (3).
//!
//! The assertion below is deliberately STRUCTURAL rather than a pinned
//! register name: it does not care WHICH register the allocator picks, only
//! that the one handed to R1 is the one just proven to hold zero. A pinned
//! `R11` would pass for the wrong reason the day the allocator changes.

use synth_synthesis::{ArmOp, Operand2, OptimizerBridge, Reg, WasmOp};

/// `f(x: i32) -> i64 = OP(0xFEDCBA9876543210 >>u u64(x))`.
///
/// The leading `i64.shr_u` is the whole point: it is an ordinary i64 op that
/// sets `last_result_vreg_hi`, which is what made the count op's own
/// `.or(..)` fallback unreachable. A bare `OP(x)` with nothing before it
/// takes the fallback and was CORRECT even before the fix — the bug was
/// never universal, which is why it survived to be found by execution.
///
/// The SHIFT AMOUNT is the runtime value and the shifted value is a
/// constant, not the other way round. `u64(x) >>u 32` is provably 0 for any
/// i32 `x`, so the optimizer folds the shift away, nothing sets
/// `last_result_vreg_hi`, the count op takes its `.or(..)` fallback and the
/// assertion holds WITH OR WITHOUT the fix. That vacuous version of this test
/// was written first and passed against a deliberately un-fixed tree; this
/// shape was checked the same way and fails.
///
/// The param is an i32 widened by `i64.extend_i32_u`, not an i64: the
/// optimized path DECLINES any function that reads an i64 param (#518), so an
/// i64 param would silently move this test to the direct selector — which was
/// never wrong here — and assert nothing. That is the same shape the boot
/// sweep's `clz64` fixture uses.
fn ops_for(count_op: WasmOp) -> Vec<WasmOp> {
    vec![
        WasmOp::I64Const(0xFEDC_BA98_7654_3210_u64 as i64),
        WasmOp::LocalGet(0),
        WasmOp::I64ExtendI32U,
        WasmOp::I64ShrU,
        count_op,
        WasmOp::End,
    ]
}

/// The register the epilogue hands to R1 must be the one a preceding
/// `Mov rd, #0` zeroed, with no later write to it.
fn assert_result_hi_is_the_zeroed_reg(label: &str, arm: &[ArmOp]) {
    let (idx, src) = arm
        .iter()
        .enumerate()
        .rev()
        .find_map(|(i, op)| match op {
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(src),
            } => Some((i, *src)),
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!("{label}: no `Mov R1, <reg>` in the epilogue — stream: {arm:#?}")
        });

    let zeroed_at = arm[..idx]
        .iter()
        .rposition(|op| matches!(op, ArmOp::Mov { rd, op2: Operand2::Imm(0) } if *rd == src));

    assert!(
        zeroed_at.is_some(),
        "{label}: the epilogue returns {src:?} as the i64 result's HIGH half, but \
         nothing zeroed {src:?} beforehand. #1240: this is the stale-`last_result_vreg_hi` \
         register, still holding the OPERAND's high word. Stream: {arm:#?}"
    );
}

fn lower(label: &str, count_op: WasmOp) -> Vec<ArmOp> {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge
        .optimize_full(&ops_for(count_op))
        .unwrap_or_else(|e| panic!("{label}: optimize_full failed: {e}"));
    bridge
        .ir_to_arm(&ir, /* num_params = */ 1)
        .unwrap_or_else(|e| panic!("{label}: ir_to_arm declined: {e}"))
}

#[test]
fn i64_clz_returns_the_zeroed_high_half_after_an_earlier_i64_op() {
    assert_result_hi_is_the_zeroed_reg("i64.clz", &lower("i64.clz", WasmOp::I64Clz));
}

#[test]
fn i64_ctz_returns_the_zeroed_high_half_after_an_earlier_i64_op() {
    assert_result_hi_is_the_zeroed_reg("i64.ctz", &lower("i64.ctz", WasmOp::I64Ctz));
}

#[test]
fn i64_popcnt_returns_the_zeroed_high_half_after_an_earlier_i64_op() {
    assert_result_hi_is_the_zeroed_reg("i64.popcnt", &lower("i64.popcnt", WasmOp::I64Popcnt));
}
