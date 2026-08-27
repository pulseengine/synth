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

/// `block (param ..)` and `loop (param ..)` decline as a class — the
/// branch-free shape happens to be correct today, but a branch edge into the
/// same type mis-reconciles, and telling the two apart would be a new
/// predicate with its own proof burden (see `find_param_block_type`).
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
