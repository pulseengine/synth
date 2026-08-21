//! #457: a read-before-write NON-PARAM local must observe the wasm-mandated 0.
//!
//! `count_params` (the backends' access-pattern param inference) mistook such a
//! local for a parameter — it was read from a parameter register (caller
//! garbage). With the declared-count cap the local lands in a frame slot, and
//! the direct selector's prologue must ZERO that slot before the body runs
//! (`movs r,#0; str r,[sp,#off]`). These tests pin the zero-init emission and
//! the classification helper; the classification cap itself is pinned in
//! `synth-backend` (`arm_backend.rs`) and `synth-backend-riscv`.

use synth_synthesis::{
    ArmInstruction, ArmOp, InstructionSelector, Operand2, Reg, WasmOp, read_before_write_locals,
};

fn lower(wasm_ops: &[WasmOp], num_params: u32) -> Vec<ArmInstruction> {
    let mut sel = InstructionSelector::new(vec![]);
    sel.select_with_stack(wasm_ops, num_params)
        .expect("select_with_stack")
}

/// The prologue zero-init: a `mov rz,#0` whose register is then stored to an
/// SP-relative slot, BEFORE the first non-prologue op. Returns the zeroed
/// SP offsets.
fn zeroed_sp_offsets(instrs: &[ArmInstruction]) -> Vec<i32> {
    let mut zero_reg: Option<Reg> = None;
    let mut offs = Vec::new();
    for i in instrs {
        match &i.op {
            ArmOp::Mov {
                rd,
                op2: Operand2::Imm(0),
            } => zero_reg = Some(*rd),
            ArmOp::Str { rd, addr } if Some(*rd) == zero_reg && addr.base == Reg::SP => {
                offs.push(addr.offset);
            }
            // Stop at the first op that isn't prologue-shaped: the zero-init
            // must dominate the body.
            ArmOp::Push { .. } | ArmOp::Sub { .. } | ArmOp::Str { .. } => {}
            _ => break,
        }
    }
    offs
}

/// The #457 repro shape: `(param i32) (local i32)`, `p0 + local1` — local 1 is
/// read before any write, so the prologue must zero its frame slot.
#[test]
fn rbw_i32_local_frame_slot_is_zero_inited_457() {
    let ops = vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::I32Add,
        WasmOp::End,
    ];
    let instrs = lower(&ops, 1);
    let offs = zeroed_sp_offsets(&instrs);
    assert!(
        !offs.is_empty(),
        "read-before-write local 1 must get a prologue zero-init store, got: {:?}",
        instrs.iter().map(|i| &i.op).collect::<Vec<_>>()
    );
}

/// An i64 read-before-write local zeroes BOTH words of its 8-byte slot.
#[test]
fn rbw_i64_local_zeroes_both_words_457() {
    let ops = vec![
        WasmOp::LocalGet(1),
        WasmOp::LocalSet(1), // tags local 1 as touched; first access is the READ
        WasmOp::LocalGet(1),
        WasmOp::I64Const(1),
        WasmOp::I64Add,
        WasmOp::LocalSet(1),
        WasmOp::I32Const(0),
        WasmOp::End,
    ];
    // Make local 1 i64 via an i64-producing write AFTER the first read:
    // infer_i64_locals sees the I64Add-fed LocalSet.
    let instrs = lower(&ops, 0);
    let offs = zeroed_sp_offsets(&instrs);
    assert!(
        offs.len() >= 2,
        "i64 rbw local must zero both slot words (off, off+4), got offsets {offs:?}"
    );
    assert!(
        offs.windows(2).any(|w| w[1] == w[0] + 4),
        "expected adjacent word zero-init (off, off+4), got {offs:?}"
    );
}

/// Byte-neutrality guard: a WRITE-first local gets NO zero-init — functions
/// without read-before-write locals keep their pre-#457 prologue.
#[test]
fn write_first_local_gets_no_zero_init_457() {
    let ops = vec![
        WasmOp::I32Const(7),
        WasmOp::LocalSet(1),
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::I32Add,
        WasmOp::End,
    ];
    let instrs = lower(&ops, 1);
    assert!(
        zeroed_sp_offsets(&instrs).is_empty(),
        "write-first local must not be zero-inited (prologue must stay byte-identical)"
    );
}

/// The classification helper: first-access-in-op-order, params excluded.
#[test]
fn read_before_write_locals_classification_457() {
    use WasmOp::*;
    // local 1 read-first, local 2 write-first, param 0 excluded.
    let ops = vec![
        LocalGet(0),
        LocalGet(1),
        I32Add,
        LocalSet(2),
        LocalGet(2),
        End,
    ];
    let rbw = read_before_write_locals(&ops, 1);
    assert!(rbw.contains(&1), "read-first local 1 is rbw");
    assert!(!rbw.contains(&2), "write-first local 2 is not rbw");
    assert!(!rbw.contains(&0), "param 0 is never rbw");
    // A tee counts as a write.
    let tee = vec![LocalTee(1), LocalGet(1), End];
    assert!(!read_before_write_locals(&tee, 0).contains(&1));
}

/// #990: "write before read in op order" is NOT domination. A write on a
/// conditionally-skipped path must not suppress the zero-init of a later
/// merge-point read — the executed leak is pinned by
/// `scripts/repro/brif_local_zeroinit_990_{arm,riscv}_differential.py`; these
/// pin the classifier arithmetic per shape.
#[test]
fn conditional_write_does_not_dominate_990() {
    use WasmOp::*;
    // THE #990 shape: block { br_if; set } get — the br_if jumps past the set.
    let brif = vec![
        Block,
        LocalGet(0),
        BrIf(0),
        I32Const(10),
        LocalSet(1),
        End,
        LocalGet(1),
        End,
    ];
    assert!(
        read_before_write_locals(&brif, 1).contains(&1),
        "a write on the br_if-not-taken arm does not dominate the merge read"
    );

    // `if` without else: the only write sits in the then-arm.
    let if_no_else = vec![
        LocalGet(0),
        If,
        I32Const(7),
        LocalSet(1),
        End,
        LocalGet(1),
        End,
    ];
    assert!(read_before_write_locals(&if_no_else, 1).contains(&1));

    // A then-arm write does not dominate the ELSE arm.
    let else_read = vec![
        LocalGet(0),
        If,
        I32Const(7),
        LocalSet(1),
        Else,
        LocalGet(1),
        LocalSet(2),
        End,
        LocalGet(2),
        End,
    ];
    let rbw = read_before_write_locals(&else_read, 1);
    assert!(
        rbw.contains(&1),
        "then-arm write must not dominate the else-arm read"
    );
    assert!(
        rbw.contains(&2),
        "an else-arm write is skipped when the then-arm runs — not dominating either"
    );

    // A block that IS a branch target does not let its writes dominate what
    // follows — the branch lands at its End, skipping them.
    let targeted_block = vec![
        Block,
        LocalGet(0),
        BrIf(0),
        I32Const(3),
        LocalSet(1),
        End,
        LocalGet(1),
        End,
    ];
    assert!(read_before_write_locals(&targeted_block, 1).contains(&1));
}

/// #990: the shapes where the write DOES dominate stay out of the set — the
/// byte-identity half of the fix (the common straight-line case must not
/// grow a zero-init).
#[test]
fn dominating_write_still_suppresses_zero_init_990() {
    use WasmOp::*;
    // Write at function scope, read inside a later block: dominated. And a
    // write inside an UNTARGETED block (no branch names its label, so its
    // End cannot be jumped to) dominates a read after the End — fall-through
    // is the only way there. This precision is what keeps the entry
    // zero-init from becoming a dead store in the same straight-line segment
    // as the real store, which VCR-RA-003's holder model rightly refuses.
    let outer_write = vec![
        I32Const(3),
        LocalSet(1),
        Block,
        LocalGet(1),
        LocalSet(2),
        End,
        LocalGet(2),
        End,
    ];
    let rbw = read_before_write_locals(&outer_write, 1);
    assert!(
        !rbw.contains(&1),
        "a depth-0 write before the block dominates the read inside it"
    );
    assert!(
        !rbw.contains(&2),
        "an untargeted block's write dominates the read after its End"
    );

    // if/else writing the SAME local on both arms: every path writes it, so
    // the read after the End is dominated (the arms' INTERSECTION survives).
    let both_arms = vec![
        LocalGet(0),
        If,
        I32Const(5),
        LocalSet(1),
        Else,
        I32Const(7),
        LocalSet(1),
        End,
        LocalGet(1),
        End,
    ];
    assert!(!read_before_write_locals(&both_arms, 1).contains(&1));

    // Write and read within the SAME block, write first: dominated (straight
    // line within the body; a br_if between them would exit, not re-enter).
    let same_block = vec![
        Block,
        I32Const(5),
        LocalSet(1),
        LocalGet(1),
        Drop,
        End,
        I32Const(0),
        End,
    ];
    assert!(!read_before_write_locals(&same_block, 0).contains(&1));

    // Inside a loop, write-then-read in the body: dominated on EVERY
    // iteration (the back-edge re-runs the write before the read).
    let loop_body = vec![
        Block,
        Loop,
        I32Const(1),
        LocalSet(1),
        LocalGet(1),
        BrIf(1),
        Br(0),
        End,
        End,
        I32Const(0),
        End,
    ];
    assert!(!read_before_write_locals(&loop_body, 0).contains(&1));

    // But a loop-body write does NOT dominate a read AFTER the loop (an exit
    // branch can leave before the write).
    let after_loop = vec![
        Block,
        Loop,
        LocalGet(0),
        BrIf(1),
        I32Const(1),
        LocalSet(1),
        Br(0),
        End,
        End,
        LocalGet(1),
        End,
    ];
    assert!(read_before_write_locals(&after_loop, 1).contains(&1));
}
