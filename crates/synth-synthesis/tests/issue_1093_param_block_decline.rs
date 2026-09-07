//! #1093 — a PARAMETER-taking block type declines LOUDLY on the direct
//! selector, never a panic, never a silent miscompile.
//!
//! Red-first evidence, measured on v0.60.0 (`4e7a179c`) before the guard:
//!   * `if (param i32 i32) (result i32)` with an `else` PANICKED —
//!     "`at` split index (is 2) should be <= len (is 1)" at the `Else` arm's
//!     `split_off(checkpoint)` (exit 101 on 5 of the 5 ARM invocation paths);
//!   * `if (param i32) (result i32)` WITHOUT an else compiled (exit 0) and
//!     silently returned the wrong value on the false path (unicorn vs
//!     wasmtime: `ipe(0)` → 0, want 7 — the "implicit else has nothing to
//!     reconcile" assumption is false once the frame has params);
//!   * fall-through `block`/`loop (param ..)` happened to compile correctly,
//!     but the same types with a branch edge mis-reconcile (measured on the
//!     RV32 sibling), so the WHOLE class declines — exactly the aarch64
//!     VCR-A64-CF-001 frame-open refusal, ported
//!     (`synth_core::find_param_block_type`).
//!
//! DO-NOT: this is a loud decline, NOT multi-value support (#1013 policy —
//! match the existing refusal, don't invent policy).

use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

fn select_err(ops: &[WasmOp], num_params: u32, arity: Vec<(u8, u8)>) -> String {
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_block_arity(arity);
    sel.select_with_stack(ops, num_params)
        .expect_err("a parameter-taking block type must decline loudly")
        .to_string()
}

/// The #1093 repro: `(i32.const 1) (i32.const 2) (if (param i32 i32)
/// (result i32) (local.get 0) (then i32.add) (else i32.sub))`.
/// Was: panic (`split_off` past the vstack). Now: typed decline by NAME.
#[test]
fn if_with_else_and_params_declines_not_panics_1093() {
    use WasmOp::*;
    let ops = vec![
        I32Const(1),
        I32Const(2),
        LocalGet(0),
        If,
        I32Add,
        Else,
        I32Sub,
        End,
        End,
    ];
    let msg = select_err(&ops, 1, vec![(2, 1)]);
    assert!(
        msg.contains("PARAMETER-taking block type"),
        "decline must name the class (the aarch64 VCR-A64-CF-001 needle); got: {msg}"
    );
    assert!(
        msg.contains("if #0 has type (2, 1)"),
        "decline must name the construct, ordinal and arity; got: {msg}"
    );
}

/// The SILENT direction: the else-less `if (param i32) (result i32)` used to
/// compile (exit 0) and return 0 instead of the pass-through param on the
/// false path. It must now decline by the same name.
#[test]
fn if_without_else_and_params_declines_1093() {
    use WasmOp::*;
    let ops = vec![I32Const(7), LocalGet(0), If, I32Const(1), I32Add, End, End];
    let msg = select_err(&ops, 1, vec![(1, 1)]);
    assert!(msg.contains("PARAMETER-taking block type"), "got: {msg}");
}

/// `block (param ..)` and `loop (param ..)` decline on the NON-relocatable
/// selector (the self-contained image configuration, which no #1097 oracle
/// leg executes), and `loop (param ..)` declines everywhere: a back-edge
/// would have to land the carried parameter in the header's registers
/// (#509), which the selector does not do yet (RQ-64-MVLOWER).
#[test]
fn block_and_loop_params_decline_1093() {
    use WasmOp::*;
    let block_ops = vec![I32Const(5), Block, LocalGet(0), I32Add, End, End];
    let msg = select_err(&block_ops, 1, vec![(1, 1)]);
    assert!(msg.contains("block #0 has type (1, 1)"), "got: {msg}");

    let loop_ops = vec![I32Const(0), Loop, I32Const(1), I32Add, End, End];
    let msg = select_err(&loop_ops, 1, vec![(1, 1)]);
    assert!(msg.contains("loop #0 has type (1, 1)"), "got: {msg}");
}

/// RQ-64-MVLOWER increment 1 (#1093): on the RELOCATABLE direct selector —
/// the configuration `scripts/repro/param_block_silent_1097_differential.py`
/// executes under unicorn against wasmtime — `block (param ..)` LOWERS: the
/// params are plain operand-stack entries and #509's designated-result-
/// register landing reconciles the `br_if` edge into the join. The execution
/// evidence is the oracle's LOWERED block/arm leg (14 vectors, fixture +
/// extra + sub-shapes); this test pins the selector-level acceptance and
/// that every construct of the class now lowers there.
#[test]
fn param_block_types_lower_on_the_relocatable_direct_selector_rq64() {
    use WasmOp::*;
    fn relocatable_selector(arity: Vec<(u8, u8)>) -> InstructionSelector {
        let db = RuleDatabase::with_standard_rules();
        let mut sel = InstructionSelector::new(db.rules().to_vec());
        sel.set_block_arity(arity);
        sel.set_relocatable(true);
        sel
    }
    // (i32.const 7) (block (param i32) (result i32) (local.get 0) (br_if 0)
    //   (i32.const 42) (i32.add)) — the #1097 `bpb` shape.
    let bpb = vec![
        I32Const(7),
        Block,
        LocalGet(0),
        BrIf(0),
        I32Const(42),
        I32Add,
        End,
        End,
    ];
    let instrs = relocatable_selector(vec![(1, 1)])
        .select_with_stack(&bpb, 1)
        .expect("block (param i32) (result i32) + br_if lowers on --relocatable (RQ-64-MVLOWER)");
    assert!(!instrs.is_empty());

    // RQ-64-MVLOWER increment 2: `if (param ..)` lowers on the same
    // relocatable selector — else-less (the #1097 `ipe` shape whose false
    // path returned 0xC0DE0003 pre-#1096) AND the #1093 two-param `if/else`
    // repro that PANICKED at the `Else` split. Execution evidence: the
    // oracle's LOWERED if/arm leg.
    let ipe = vec![I32Const(7), LocalGet(0), If, I32Const(42), I32Add, End, End];
    relocatable_selector(vec![(1, 1)])
        .select_with_stack(&ipe, 1)
        .expect("else-less if (param i32) (result i32) lowers on --relocatable (RQ-64 #2)");
    let ipe2 = vec![
        I32Const(1),
        I32Const(2),
        LocalGet(0),
        If,
        I32Add,
        Else,
        I32Sub,
        End,
        End,
    ];
    relocatable_selector(vec![(2, 1)])
        .select_with_stack(&ipe2, 1)
        .expect("the #1093 if (param i32 i32) (result i32) + else repro lowers (no panic)");

    // RQ-64-MVLOWER increment 3: `loop (param ..)` lowers on the same
    // relocatable selector — the #1097 `lpb` shape (a conditional back-edge
    // carrying the accumulator) and a TWO-parameter loop. Execution evidence:
    // the oracle's LOWERED loop/arm leg.
    let lpb = vec![
        I32Const(7),
        Loop,
        I32Const(1),
        I32Add,
        LocalGet(0),
        BrIf(0),
        End,
        End,
    ];
    relocatable_selector(vec![(1, 1)])
        .select_with_stack(&lpb, 1)
        .expect("loop (param i32) (result i32) + back-edge lowers on --relocatable (RQ-64 #3)");
    let lp2 = vec![
        I32Const(0),
        I32Const(3),
        Loop, // (param i32 i32) (result i32 i32)
        I32Add,
        I32Const(1),
        LocalGet(0),
        BrIf(0),
        End,
        Drop,
        End,
    ];
    relocatable_selector(vec![(2, 2)])
        .select_with_stack(&lp2, 1)
        .expect("a two-parameter loop lowers on --relocatable (RQ-64 #3)");
}

/// Negative control — the guard must NOT widen the refusal: a (0, 1)
/// value-carrying `if/else` (the #313-reconciled class) still compiles, and
/// an empty side-table (hand-built op streams) still reads as all-void.
#[test]
fn param_free_block_types_still_compile_1093() {
    use WasmOp::*;
    let ops = vec![LocalGet(0), If, I32Const(1), Else, I32Const(2), End, End];
    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    sel.set_block_arity(vec![(0, 1)]);
    sel.select_with_stack(&ops, 1)
        .expect("(0,1) if/else is the supported #313 class and must still compile");

    let db = RuleDatabase::with_standard_rules();
    let mut sel = InstructionSelector::new(db.rules().to_vec());
    // No side-table at all: the legacy all-void reading.
    sel.select_with_stack(&ops, 1)
        .expect("empty side-table must keep the legacy void lowering");
}
