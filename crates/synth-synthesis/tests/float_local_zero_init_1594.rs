//! #1594: a float local that may be read before it is written (on SOME path)
//! must observe wasm's 0.0. The direct selector reserves such a local's VFP
//! home at function entry and writes +0.0 into it (`F32Const 0.0` per
//! S-register) BEFORE the body's first branch. These tests pin that emission,
//! its dependence on the declared-type table, and that a local whose write
//! dominates every read gets nothing (byte-identical). The execution truth —
//! register AND frame homes, zeroed and garbage stack/registers, against
//! wasmtime — is `scripts/repro/float_local_zero_init_1594_differential.py`.

use synth_core::target::FPUPrecision;
use synth_synthesis::rules::ArmOp;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

/// `(param $a f32) (param $c i32) (local $x f32)`, lowered on cortex-m4f.
fn lower(ops: &[WasmOp], declared_float_locals: Option<Vec<u8>>) -> Vec<ArmOp> {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_target(Some(FPUPrecision::Single), "cortex-m4f");
    sel.set_params_f32(vec![true, false]);
    if let Some(d) = declared_float_locals {
        sel.set_declared_float_locals(d);
    }
    sel.select_with_stack(ops, 2)
        .expect("select_with_stack")
        .into_iter()
        .map(|i| i.op)
        .collect()
}

/// `if (c) { x = a } ; return x` — x is written on the then-arm only.
fn one_arm_write() -> Vec<WasmOp> {
    vec![
        WasmOp::LocalGet(1),
        WasmOp::If,
        WasmOp::LocalGet(0),
        WasmOp::LocalSet(2),
        WasmOp::End,
        WasmOp::LocalGet(2),
        WasmOp::End,
    ]
}

/// Index of the first `F32Const 0.0`, and of the first compare (the `if`).
fn zero_and_cmp(ops: &[ArmOp]) -> (Option<usize>, Option<usize>) {
    let zero = ops
        .iter()
        .position(|o| matches!(o, ArmOp::F32Const { value, .. } if value.to_bits() == 0));
    let cmp = ops.iter().position(|o| matches!(o, ArmOp::Cmp { .. }));
    (zero, cmp)
}

#[test]
fn one_arm_float_local_is_zeroed_before_the_branch_1594() {
    let ops = lower(&one_arm_write(), Some(vec![4]));
    let (zero, cmp) = zero_and_cmp(&ops);
    let (zero, cmp) = (
        zero.unwrap_or_else(|| panic!("no entry +0.0 for the one-arm f32 local: {ops:?}")),
        cmp.unwrap_or_else(|| panic!("no compare for the `if`: {ops:?}")),
    );
    assert!(
        zero < cmp,
        "the +0.0 must dominate the branch (zero at {zero}, cmp at {cmp}): {ops:?}"
    );
}

/// Red half: without the declared-type table there is no entry zero — the
/// pre-#1594 emission (the defect), pinned so a regression of the plumbing
/// is caught here and not only downstream.
#[test]
fn without_declared_types_no_entry_zero_1594() {
    let ops = lower(&one_arm_write(), None);
    assert_eq!(zero_and_cmp(&ops).0, None, "{ops:?}");
}

/// A write that dominates every read: not in the read-before-write set, so
/// the emission is byte-identical with or without the declared-type table.
#[test]
fn dominating_write_is_byte_identical_1594() {
    let straight = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalSet(2),
        WasmOp::LocalGet(2),
        WasmOp::End,
    ];
    assert_eq!(lower(&straight, Some(vec![4])), lower(&straight, None));
}
