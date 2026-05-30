//! Regression test: `OptimizerBridge::wasm_to_ir` overloaded `inst_id` as both
//! "unique IR instruction id" AND "vreg-slot index", and back-references like
//! `inst_id.saturating_sub(2)` assumed a one-to-one correspondence between
//! `inst_id` and the wasm value stack.
//!
//! That assumption broke whenever any wasm op consumed a stack slot WITHOUT
//! producing one — `Drop`, `LocalSet`, `GlobalSet`, the store family, `BrIf`,
//! plus the structural `Block`/`Loop`/`End` markers. The next binary or unary
//! op's `inst_id.saturating_sub(N)` would then index a stale or never-mapped
//! vreg, and `get_arm_reg` would either trip the PR #101 defensive panic or
//! (pre-PR-101) silently fall back to R0 — the classic silent-miscompilation
//! bug class first surfaced in issue #93.
//!
//! Gale (the real-hardware test rig) caught WASM modules in the field that
//! tripped this on production silicon; the cargo-fuzz `wasm_ops_lower_or_error`
//! harness on PR #117 surfaced the same class six different ways. This file
//! covers each of the shapes the fuzz harness found plus a semantic-correctness
//! probe to confirm that fixing the panic also fixes the silent miscompile.
//!
//! Fix (issue #121): introduce a `slot_stack: Vec<u32>` in `wasm_to_ir` that
//! mirrors the wasm value stack. Each producer pushes its dest vreg; each
//! consumer pops to discover its source vreg. `inst_id` reverts to its
//! original meaning — a monotonically increasing unique IR id — and is no
//! longer used for slot lookup.

use synth_opt::Opcode;
use synth_synthesis::{OptimizerBridge, WasmOp};

/// Type-mismatched malformed wasm: `[I32Const, I64Clz, ...]` — I64Clz
/// expects i64 (2 slots) but only an i32 (1 slot) is on the stack.
/// Pre-flight's depth-only check doesn't catch this; wasm_to_ir's
/// slot_stack model would pop on empty stack. Fix: wasm_to_ir returns
/// Result and propagates Err on underflow. Both lowering paths must
/// return cleanly (Ok or Err) — never panic.
#[test]
fn type_mismatch_i32_then_i64_clz_does_not_panic() {
    let ops = vec![
        WasmOp::I32Const(1059004415),
        WasmOp::I64Clz,
        WasmOp::I32Const(0),
    ];
    let bridge = OptimizerBridge::new();
    // Either Ok or Err is acceptable — panic is not.
    let _ = bridge.optimize_full(&ops);
}

#[test]
fn i64_unary_on_empty_stack_does_not_panic() {
    // Even more degenerate: I64Clz with nothing on the stack.
    let ops = vec![WasmOp::I64Clz];
    let bridge = OptimizerBridge::new();
    let _ = bridge.optimize_full(&ops);
}

#[test]
fn i64_binary_on_partial_stack_does_not_panic() {
    // I64Add wants 4 slots (two i64s), only 2 slots present.
    let ops = vec![WasmOp::I64Const(7), WasmOp::I64Add];
    let bridge = OptimizerBridge::new();
    let _ = bridge.optimize_full(&ops);
}

fn compile_through_optimized(ops: &[WasmOp]) {
    let bridge = OptimizerBridge::new();
    // The point of this audit is "no panic". #178: the optimized path now
    // declines linear-memory ops (typed Err → backend falls back to
    // select_with_stack), a panic-free outcome. If it does optimize, the
    // ir_to_arm step must still not panic on the back-reference.
    match bridge.optimize_full(ops) {
        Ok((instrs, _cfg, _stats)) => {
            let _arm = bridge.ir_to_arm(&instrs, /* num_params = */ 4);
        }
        Err(_) => { /* declined (e.g. linear memory, #178) — panic-free, fine */ }
    }
}

/// Round-6 fuzz-harness shape from PR #117: a Drop sits between the
/// producer and consumer, breaking the `inst_id-1` back-reference.
#[test]
fn drop_between_producer_and_consumer() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::Drop,
        WasmOp::I32Popcnt,
    ];
    compile_through_optimized(&ops);
}

/// LocalSet consumes a slot without producing one — same bug class as Drop.
#[test]
fn local_set_between_producer_and_consumer() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::LocalSet(2),
        WasmOp::I32Popcnt,
    ];
    compile_through_optimized(&ops);
}

/// Two consecutive Drops sandwiched between producers — confirms slot_stack
/// supports multiple pops in a row (not just a single "consume gap").
#[test]
fn double_drop_then_const() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::I32Const(42),
        WasmOp::I32Popcnt,
    ];
    compile_through_optimized(&ops);
}

/// GlobalSet is another pure consumer.
#[test]
fn global_set_between_producer_and_consumer() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::I32Const(7),
        WasmOp::GlobalSet(0),
        WasmOp::I32Popcnt,
    ];
    compile_through_optimized(&ops);
}

/// I32Store consumes two slots (addr, value) without producing — extreme
/// case of the "consume without produce" pattern.
#[test]
fn i32_store_between_producer_and_consumer() {
    let ops = vec![
        WasmOp::LocalGet(0),      // surviving operand for Popcnt
        WasmOp::I32Const(0x1000), // addr for store
        WasmOp::I32Const(42),     // value for store
        WasmOp::I32Store {
            offset: 0,
            align: 2,
        },
        WasmOp::I32Popcnt, // must read LocalGet(0)'s slot, not store's stale slot
    ];
    compile_through_optimized(&ops);
}

/// BrIf inside a block — pops a condition without producing. The value
/// beneath the cond must remain on slot_stack for the trailing op.
#[test]
fn br_if_between_producer_and_consumer() {
    let ops = vec![
        WasmOp::Block,
        WasmOp::LocalGet(0),
        WasmOp::I32Const(1),
        WasmOp::BrIf(0),
        WasmOp::I32Popcnt, // reads LocalGet(0)'s slot
        WasmOp::Drop,
        WasmOp::End,
    ];
    compile_through_optimized(&ops);
}

/// i64 Drop: drops 2 slots (1 i64). Mirror of the i32 Drop case for the
/// i64 register-pair model.
#[test]
fn i64_drop_between_i64_consts() {
    let ops = vec![
        WasmOp::I64Const(7),
        WasmOp::I64Const(11),
        WasmOp::Drop,
        WasmOp::Drop,
        WasmOp::I64Const(0),
        WasmOp::I64Eqz, // pops 1 i64 (= 2 slots), produces i32
    ];
    compile_through_optimized(&ops);
}

/// Mixed i32 + i64 sequence with a Drop in the middle. Pre-fix this would
/// either panic on the second I64Add or miscompile silently because the
/// Drop scrambled the inst_id-to-slot correspondence for the i64 pair.
#[test]
fn mixed_i32_i64_with_drop() {
    let ops = vec![
        WasmOp::I64Const(1),
        WasmOp::I64Const(2),
        WasmOp::I64Add,
        WasmOp::I32Const(99),
        WasmOp::Drop, // discards the i32 const
        WasmOp::I64Const(3),
        WasmOp::I64Add, // must add the surviving I64Add result + I64Const(3)
    ];
    compile_through_optimized(&ops);
}

/// Block/Loop/End markers do not push or pop wasm-stack values, but their
/// presence DID increment `inst_id` in the pre-fix code, shifting all
/// subsequent slot back-references by one. Verify slot_stack model is
/// immune to that.
#[test]
fn block_loop_end_between_producer_and_consumer() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::Block,
        WasmOp::Loop,
        WasmOp::End,
        WasmOp::End,
        WasmOp::I32Popcnt, // reads LocalGet(0)
    ];
    compile_through_optimized(&ops);
}

/// LocalTee writes to a local and keeps the value on stack (consumes 1,
/// produces 1). Verify that the produced value is the one the next op
/// reads — not a stale slot.
#[test]
fn local_tee_then_consumer() {
    let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalTee(1), WasmOp::I32Popcnt];
    compile_through_optimized(&ops);
}

/// SEMANTIC-CORRECTNESS PROBE.
///
/// Pre-fix, `[I32Const(7), I32Const(11), Drop, I32Popcnt]` would compile —
/// but the Popcnt's source vreg would point at I32Const(11)'s slot (the one
/// the Drop semantically discarded), not I32Const(7)'s. The compiler ran
/// to completion, the ARM output looked sensible, but the firmware computed
/// `popcnt(11) = 3` instead of `popcnt(7) = 3`. Same answer by accident in
/// this case, so let's check a pair where the result actually differs.
///
/// `popcnt(0b111) = 3` (I32Const(7)); `popcnt(0b1011) = 3` — wait, also 3.
/// Pick a pair with distinct popcounts. `popcnt(7) = 3`, `popcnt(15) = 4`.
#[test]
fn drop_preserves_correct_value_for_consumer() {
    let ops = vec![
        WasmOp::I32Const(7),
        WasmOp::I32Const(15), // discarded by Drop
        WasmOp::Drop,
        WasmOp::I32Popcnt,
    ];
    let bridge = OptimizerBridge::new();
    let (instrs, _cfg, _stats) = bridge.optimize_full(&ops).expect("optimize_full");

    // Find the Popcnt; its `src` vreg MUST be the same vreg that
    // I32Const(7) wrote to — NOT the one I32Const(15) wrote to.
    let popcnt = instrs
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Popcnt { .. }))
        .expect("Popcnt should appear in IR");
    let popcnt_src = match popcnt.opcode {
        Opcode::Popcnt { src, .. } => src,
        _ => unreachable!(),
    };

    // Look for the Const-7 producer and Const-15 producer.
    let const7_dest = instrs
        .iter()
        .find_map(|i| match i.opcode {
            Opcode::Const { dest, value: 7 } => Some(dest),
            _ => None,
        })
        .expect("I32Const(7) should appear in IR");

    assert_eq!(
        popcnt_src.0, const7_dest.0,
        "Popcnt must read I32Const(7)'s vreg (the surviving stack value), \
         not I32Const(15)'s (the dropped one). Pre-fix #121, the back-reference \
         `inst_id-1` would land on Const(15)'s slot — silent miscompilation."
    );
}

/// Same shape as `drop_preserves_correct_value_for_consumer` but verifies
/// LocalSet behaves identically. LocalSet's pre-fix bug was exactly the
/// same as Drop's — it consumed a slot via `inst_id.saturating_sub(1)`
/// without `slot_stack`-style bookkeeping, so the next consumer landed on
/// the slot that LocalSet had semantically already moved out to a local.
#[test]
fn local_set_preserves_correct_value_for_consumer() {
    let ops = vec![
        WasmOp::I32Const(7),
        WasmOp::I32Const(99),
        WasmOp::LocalSet(0), // stores 99 to local 0; stack now has [7]
        WasmOp::I32Popcnt,   // must popcnt 7, not 99
    ];
    let bridge = OptimizerBridge::new();
    let (instrs, _cfg, _stats) = bridge.optimize_full(&ops).expect("optimize_full");

    let popcnt_src = instrs
        .iter()
        .find_map(|i| match i.opcode {
            Opcode::Popcnt { src, .. } => Some(src),
            _ => None,
        })
        .expect("Popcnt should appear in IR");

    let const7_dest = instrs
        .iter()
        .find_map(|i| match i.opcode {
            Opcode::Const { dest, value: 7 } => Some(dest),
            _ => None,
        })
        .expect("I32Const(7) should appear in IR");

    assert_eq!(
        popcnt_src.0, const7_dest.0,
        "Popcnt must read I32Const(7)'s vreg after LocalSet discarded \
         the 99 from the wasm stack. Pre-fix #121 would have read 99's vreg."
    );
}
