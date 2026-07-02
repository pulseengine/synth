//! #509 — value-carrying `br`/`br_if`/`br_table` on the direct selector.
//!
//! The shipped (`--relocatable`) selector used to emit a bare branch for every
//! `br*`, silently DROPPING the value a branch carries to a result-typed block
//! (wasmtime: `pick(1) = 12`; synth: `2`). The fix threads the decoder's
//! blocktype-arity side-table (`set_block_arity`, ordinal-keyed) into
//! `select_with_stack`, which gives each branched-to arity-1 block a
//! DESIGNATED RESULT REGISTER `R_res`: every edge into the join —
//! `br`/`br_if`/`br_table` (a `mov R_res, carried` before the jump) and the
//! fall-through at `End` (`mov R_res, top`, elided when equal) — agrees on it
//! by construction (the #313 if/else reconciliation generalized to N edges).
//!
//! This file is the cargo-CI structural gate (the execution gate is
//! `scripts/repro/br_table_value_509_differential.py`, red→green on this fix):
//!   * a value-carrying `br_table` emits the per-edge `mov R_res` and `End`
//!     publishes `R_res` as the block result (traced to the function return);
//!   * an arity-0 (void) block emits NO extra moves — control-flow-only code
//!     is byte-identical with and without the side-table;
//!   * the honest declines: loop-parameter-carrying br, multi-value results,
//!     br to a result-typed if join, i64 carried values — loud `Err`
//!     (#180/#185 Ok-or-Err), never a silent drop.

use synth_synthesis::{
    ArmInstruction, ArmOp, InstructionSelector, Operand2, Reg, RuleDatabase, WasmOp,
};

fn select(ops: &[WasmOp], num_params: u32, arity: Vec<(u8, u8)>) -> Vec<ArmInstruction> {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_block_arity(arity);
    sel.select_with_stack(ops, num_params)
        .expect("selection should succeed")
}

fn select_err(ops: &[WasmOp], num_params: u32, arity: Vec<(u8, u8)>) -> String {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_block_arity(arity);
    sel.select_with_stack(ops, num_params)
        .expect_err("selection must decline loudly")
        .to_string()
}

/// The `pick` shape from `scripts/repro/br_value_509.wat`: a value-carrying
/// `br_table` dispatching into two nested result-typed blocks.
///
///   (block (result i32)                 ;; outer
///     (block (result i32)               ;; inner
///       (i32.const 10) (i32.const 0)    ;; carried value, selector index
///       (br_table 0 1))
///     (i32.const 1) (i32.add))          ;; inner fall-in arm: +1
///
/// Asserts the full designated-register chain: one `mov R_res` per distinct
/// edge at the dispatch, the fall-through reconcile `mov` before each block's
/// end label, and the outer block's `R_res` reaching the function return (R0).
#[test]
fn br_table_value_carry_emits_edge_moves_and_end_publishes_r_res_509() {
    use WasmOp::*;
    let ops = vec![
        Block,        // outer (result i32)
        Block,        // inner (result i32)
        I32Const(10), // carried value
        I32Const(0),  // br_table selector index
        BrTable {
            targets: vec![0],
            default: 1,
        },
        End, // inner
        I32Const(1),
        I32Add,
        End, // outer
        End, // function
    ];
    let instrs = select(&ops, 0, vec![(0, 1), (0, 1)]);

    // The br_table op is index 4 — every edge mov + the dispatch cascade
    // carries source_line Some(4). The two distinct targets (inner, outer)
    // get distinct designated registers, so exactly two movs precede the
    // first CMP of the cascade.
    let at_dispatch: Vec<&ArmOp> = instrs
        .iter()
        .filter(|i| i.source_line == Some(4))
        .map(|i| &i.op)
        .collect();
    let first_cmp = at_dispatch
        .iter()
        .position(|op| matches!(op, ArmOp::Cmp { .. }))
        .expect("br_table emits a CMP cascade");
    let edge_movs: Vec<Reg> = at_dispatch[..first_cmp]
        .iter()
        .filter_map(|op| match op {
            ArmOp::Mov { rd, .. } => Some(*rd),
            _ => None,
        })
        .collect();
    assert_eq!(
        edge_movs.len(),
        2,
        "one `mov R_res, carried` per distinct br_table target, all before \
         the CMP cascade (never between CMP and Bcc): {at_dispatch:?}"
    );
    assert_ne!(
        edge_movs[0], edge_movs[1],
        "inner and outer blocks get distinct designated result registers"
    );
    // No mov may sit between a CMP and its Bcc (flag-setting encodings).
    for w in at_dispatch[first_cmp..].windows(2) {
        if matches!(w[0], ArmOp::Cmp { .. }) {
            assert!(
                matches!(w[1], ArmOp::Bcc { .. }),
                "CMP must be immediately followed by its Bcc: {at_dispatch:?}"
            );
        }
    }

    // End (inner, op idx 5; outer, op idx 8): the fall-through reconcile mov
    // into the SAME designated register, emitted BEFORE the end label.
    for (end_idx, r_res) in [(5usize, edge_movs[0]), (8usize, edge_movs[1])] {
        let at_end: Vec<&ArmOp> = instrs
            .iter()
            .filter(|i| i.source_line == Some(end_idx))
            .map(|i| &i.op)
            .collect();
        let mov_pos = at_end
            .iter()
            .position(|op| matches!(op, ArmOp::Mov { rd, .. } if *rd == r_res))
            .unwrap_or_else(|| {
                panic!("End #{end_idx} reconciles the fall-through into {r_res:?}: {at_end:?}")
            });
        let label_pos = at_end
            .iter()
            .position(|op| matches!(op, ArmOp::Label { .. }))
            .expect("block End emits its end label");
        assert!(
            mov_pos < label_pos,
            "the fall-through mov lands BEFORE the join label (branch edges \
             jump past it): {at_end:?}"
        );
    }

    // The outer block's R_res is the function result: the epilogue moves it
    // (or already finds it) in R0.
    let outer_res = edge_movs[1];
    assert!(
        outer_res == Reg::R0
            || instrs.iter().any(|i| {
                matches!(
                    &i.op,
                    ArmOp::Mov { rd: Reg::R0, op2: Operand2::Reg(r) } if *r == outer_res
                )
            }),
        "the outer designated register {outer_res:?} must reach R0"
    );
}

/// The `pick_brif` shape: `br_if` peeks the carried value (it stays on the
/// stack for the fall-through path) and the mov precedes the CMP.
#[test]
fn br_if_value_carry_moves_before_cmp_and_keeps_fallthrough_value_509() {
    use WasmOp::*;
    let ops = vec![
        Block,        // (result i32)
        I32Const(10), // carried value
        LocalGet(0),  // condition
        BrIf(0),
        Drop,
        I32Const(20),
        End, // block
        End, // function
    ];
    let instrs = select(&ops, 1, vec![(0, 1)]);

    // At the br_if (op idx 3): mov R_res BEFORE the CMP, then CMP + BNE.
    let at_brif: Vec<&ArmOp> = instrs
        .iter()
        .filter(|i| i.source_line == Some(3))
        .map(|i| &i.op)
        .collect();
    let mov_pos = at_brif
        .iter()
        .position(|op| matches!(op, ArmOp::Mov { .. }))
        .expect("br_if to a value block emits the edge mov");
    let cmp_pos = at_brif
        .iter()
        .position(|op| matches!(op, ArmOp::Cmp { .. }))
        .expect("br_if emits CMP");
    assert!(
        mov_pos < cmp_pos,
        "edge mov precedes the CMP (nothing between CMP and Bcc): {at_brif:?}"
    );

    // The value was PEEKED: the fall-through `Drop` (op idx 4) must not
    // underflow, and the not-taken arm's 20 must reconcile into the same
    // R_res at End — i.e. the End emits a mov into the edge-mov's register.
    let r_res = at_brif
        .iter()
        .find_map(|op| match op {
            ArmOp::Mov { rd, .. } => Some(*rd),
            _ => None,
        })
        .unwrap();
    assert!(
        instrs
            .iter()
            .any(|i| i.source_line == Some(6)
                && matches!(&i.op, ArmOp::Mov { rd, .. } if *rd == r_res)),
        "End reconciles the fall-through 20 into the same designated register"
    );
}

/// Void blocks are BYTE-NEUTRAL: with the side-table present-but-(0,0) the
/// emitted sequence is identical to the legacy no-table lowering — no extra
/// moves, no allocation shift, for br, br_if, and br_table alike.
#[test]
fn arity_zero_blocks_emit_no_extra_moves_byte_neutral_509() {
    use WasmOp::*;
    let ops = vec![
        Block, // void
        Block, // void
        I32Const(1),
        Drop,
        LocalGet(0),
        BrIf(0),
        I32Const(7),
        BrTable {
            targets: vec![0],
            default: 1,
        },
        End,
        Br(0),
        End,
        End, // function
    ];
    let legacy = select(&ops, 1, Vec::new());
    let with_table = select(&ops, 1, vec![(0, 0), (0, 0)]);
    assert_eq!(
        format!("{legacy:?}"),
        format!("{with_table:?}"),
        "a (0,0) side-table entry must not change a single instruction"
    );
}

/// Honest declines (#180/#185 Ok-or-Err): the unsupported value-carry shapes
/// produce a loud `Err` naming #509 — never a silent drop.
#[test]
fn unsupported_value_carry_shapes_decline_loudly_509() {
    use WasmOp::*;

    // br to a parameterized loop header (loop-param carry).
    let loop_param = vec![
        I32Const(1),
        Loop, // (param i32)
        I32Const(2),
        Br(0),
        End,
        Drop,
        End,
    ];
    let e = select_err(&loop_param, 0, vec![(1, 0)]);
    assert!(
        e.contains("#509") && e.contains("loop"),
        "loop-param br declines loudly: {e}"
    );

    // br to a multi-value block.
    let multi = vec![Block, I32Const(1), I32Const(2), Br(0), End, Drop, End];
    let e = select_err(&multi, 0, vec![(0, 2)]);
    assert!(
        e.contains("#509") && e.contains("multi-value"),
        "multi-value br declines loudly: {e}"
    );

    // br to a result-typed if/else join (the #313-reconciled join).
    let if_join = vec![
        LocalGet(0),
        If, // (result i32)
        I32Const(1),
        Br(0),
        Else,
        I32Const(2),
        End,
        End,
    ];
    let e = select_err(&if_join, 1, vec![(0, 1)]);
    assert!(
        e.contains("#509") && e.contains("if"),
        "br to a result-typed if join declines loudly: {e}"
    );

    // i64 carried value.
    let wide = vec![Block, I64Const(1), Br(0), End, Drop, End];
    let e = select_err(&wide, 0, vec![(0, 1)]);
    assert!(
        e.contains("#509") && e.contains("i64"),
        "i64 value-carry declines loudly: {e}"
    );
}
