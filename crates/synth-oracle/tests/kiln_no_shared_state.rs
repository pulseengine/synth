//! A kiln reference run must not see state left by an earlier run on the same
//! module bytes. The converted-module cache in `reference.rs` once shared a
//! module's linear memory across calls: a store in one `reference::run` was
//! returned by a load in the next, so every oracle comparing a fresh emulator
//! image against kiln compared against accumulated state. Found by the cold
//! review of the RV32 reach lane.
#![cfg(feature = "exec")]

use synth_oracle::compare::RefOutcome;
use synth_oracle::reference::{self, Imports};
use synth_oracle::value::WasmValue;

fn module(extra: &str) -> Vec<u8> {
    wat::parse_str(format!(
        "(module (memory 1) (global $g (mut i32) (i32.const 7)) \
         (func (export \"st\") (param i32 i32) local.get 0 local.get 1 i32.store) \
         (func (export \"ld\") (param i32) (result i32) local.get 0 i32.load) \
         (func (export \"gset\") (param i32) local.get 0 global.set $g) \
         (func (export \"gget\") (result i32) global.get $g) {extra})"
    ))
    .unwrap()
}

fn i32_of(o: &RefOutcome) -> Option<u32> {
    match o {
        RefOutcome::Values(v) => match v.as_slice() {
            [WasmValue::I32(x)] => Some(*x),
            _ => None,
        },
        _ => None,
    }
}

#[test]
fn memory_does_not_cross_calls() {
    let m = module("");
    let imp = Imports::new();
    reference::run(
        &m,
        "st",
        &[WasmValue::I32(100), WasmValue::I32(0x5a5a)],
        100_000,
        &imp,
    )
    .unwrap();
    let after = reference::run(&m, "ld", &[WasmValue::I32(100)], 100_000, &imp).unwrap();
    assert_eq!(
        i32_of(&after.outcome),
        Some(0),
        "a store in an earlier run leaked: {after:?}"
    );
}

#[test]
fn globals_do_not_cross_calls() {
    let m = module("(func (export \"pad\"))");
    let imp = Imports::new();
    reference::run(&m, "gset", &[WasmValue::I32(99)], 100_000, &imp).unwrap();
    let after = reference::run(&m, "gget", &[], 100_000, &imp).unwrap();
    assert_eq!(
        i32_of(&after.outcome),
        Some(7),
        "a global set in an earlier run leaked: {after:?}"
    );
}

#[test]
fn tables_do_not_cross_calls() {
    // `tset` fills slot 0, which starts null; `call0` dispatches through it.
    // On a fresh instance `call0` must trap on the null entry.
    let m = wat::parse_str(
        "(module (table 1 funcref) (type $t (func (result i32))) \
         (func $one (type $t) i32.const 1) (elem declare func $one) \
         (func (export \"tset\") i32.const 0 ref.func $one table.set 0) \
         (func (export \"call0\") (result i32) i32.const 0 call_indirect (type $t)))",
    )
    .unwrap();
    let imp = Imports::new();
    let before = reference::run(&m, "call0", &[], 100_000, &imp).unwrap();
    assert!(
        matches!(before.outcome, RefOutcome::Trap { .. }),
        "control: a null slot must trap on a fresh instance: {before:?}"
    );
    reference::run(&m, "tset", &[], 100_000, &imp).unwrap();
    let after = reference::run(&m, "call0", &[], 100_000, &imp).unwrap();
    assert!(
        matches!(after.outcome, RefOutcome::Trap { .. }),
        "a table.set in an earlier run leaked: {after:?}"
    );
}
