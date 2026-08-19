//! #946 — `infer_i64_locals` vstack drift: ops that consume values the
//! stack-effect table said they don't.
//!
//! `infer_i64_locals` re-derives local widths by simulating a virtual stack of
//! widths over the op stream (the decoder discards local-declaration types).
//! Its per-op effects came from `wasm_stack_effect`, whose table carried FOUR
//! wrong rows behind a "no value stack effect at this level" comment plus a
//! `_ => (0, 0)` wildcard:
//!
//!   * `If` / `BrIf` really pop their i32 condition, `BrTable` its i32 index
//!     — listed as `(0, 0)`;
//!   * `MemoryCopy` / `MemoryFill` really pop 3 i32 operands — absorbed by
//!     the wildcard as `(0, 0)`;
//!   * `Call` / `CallIndirect` really pop their arguments (and the table
//!     index) — listed as `(0, 1)` "approximate".
//!
//! Each stale entry shifts the width stack, so a later `local.set` of an i64
//! reads a stale i32 width, the local gets a 4-byte slot and a single-word
//! STR/LDR, and the upper half is silently dropped. Executed proof (unicorn
//! vs wasmtime, cortex-m4 `--relocatable --no-optimize`): the `br_if`, `if`
//! and `br_table` shapes below returned 32 where wasmtime returns 1; the
//! `memory.copy` shape returned 0. The same inference feeds the RV32
//! selector's frame layout (#312), so the drift was cross-backend.
//!
//! These tests pin the inference directly: in every shape, local `$x` (the
//! first non-param local) is stored an i64 and MUST be classified i64.
//! Red-first: all six failed on the pre-fix tree.

use synth_synthesis::{WasmOp, infer_i64_locals};

/// `i64.const` then the shape under test, then `local.set 0` + a read-back.
fn assert_local0_is_i64(mut prefix: Vec<WasmOp>, ctx: &Ctx) {
    use WasmOp::*;
    let mut ops = vec![I64Const(0x1_0000_0005)];
    ops.append(&mut prefix);
    ops.extend([LocalSet(0), LocalGet(0)]);
    let set = infer_i64_locals(
        &ops,
        &ctx.func_ret_i64,
        &ctx.type_ret_i64,
        &ctx.func_arg_counts,
        &ctx.type_arg_counts,
    );
    assert!(
        set.contains(&0),
        "local 0 is stored an i64 but was inferred i32 — the width vstack \
         drifted across {:?} (#946: its stack effect is mis-modelled)",
        ops.get(2)
    );
}

#[derive(Default)]
struct Ctx {
    func_ret_i64: Vec<bool>,
    type_ret_i64: Vec<bool>,
    func_arg_counts: Vec<u32>,
    type_arg_counts: Vec<u32>,
}

#[test]
fn br_if_pops_its_condition() {
    use WasmOp::*;
    // block { i32.const 1; br_if 0 } — the cond must leave the width stack.
    assert_local0_is_i64(
        vec![Block, I32Const(1), BrIf(0), End],
        &Ctx::default(),
    );
}

#[test]
fn if_pops_its_condition() {
    use WasmOp::*;
    assert_local0_is_i64(
        vec![I32Const(1), If, Nop, End],
        &Ctx::default(),
    );
}

#[test]
fn br_table_pops_its_index() {
    use WasmOp::*;
    assert_local0_is_i64(
        vec![
            Block,
            Block,
            I32Const(1),
            BrTable {
                targets: vec![0],
                default: 1,
            },
            End,
            End,
        ],
        &Ctx::default(),
    );
}

#[test]
fn memory_copy_pops_three_operands() {
    use WasmOp::*;
    assert_local0_is_i64(
        vec![I32Const(0), I32Const(16), I32Const(4), MemoryCopy],
        &Ctx::default(),
    );
}

#[test]
fn memory_fill_pops_three_operands() {
    use WasmOp::*;
    assert_local0_is_i64(
        vec![I32Const(0), I32Const(0xAB), I32Const(4), MemoryFill],
        &Ctx::default(),
    );
}

#[test]
fn call_pops_its_arguments() {
    use WasmOp::*;
    // call $g(i32) -> i32, then drop the result: the arg must leave the
    // width stack along with it.
    let ctx = Ctx {
        func_ret_i64: vec![false],
        func_arg_counts: vec![1],
        ..Ctx::default()
    };
    assert_local0_is_i64(vec![I32Const(7), Call(0), Drop], &ctx);
}

#[test]
fn call_indirect_pops_args_and_table_index() {
    use WasmOp::*;
    let ctx = Ctx {
        type_ret_i64: vec![false],
        type_arg_counts: vec![1],
        ..Ctx::default()
    };
    assert_local0_is_i64(
        vec![
            I32Const(7),
            I32Const(0), // table index
            CallIndirect {
                type_index: 0,
                table_index: 0,
            },
            Drop,
        ],
        &ctx,
    );
}

/// The i64-width case the OLD code got right must stay right: a call
/// RETURNING i64 feeding `local.set` (#311).
#[test]
fn i64_returning_call_still_classifies() {
    use WasmOp::*;
    let ctx = Ctx {
        func_ret_i64: vec![true],
        func_arg_counts: vec![0],
        ..Ctx::default()
    };
    let ops = vec![Call(0), LocalSet(0), LocalGet(0)];
    let set = infer_i64_locals(
        &ops,
        &ctx.func_ret_i64,
        &ctx.type_ret_i64,
        &ctx.func_arg_counts,
        &ctx.type_arg_counts,
    );
    assert!(set.contains(&0), "#311 regression: i64-returning call result");
}

/// Straight-line i32 shape: local 0 must NOT be classified i64 (over-widening
/// direction — the fix must not turn every local into a pair).
#[test]
fn i32_local_stays_i32() {
    use WasmOp::*;
    let ops = vec![
        I64Const(9),
        Drop,
        I32Const(3),
        LocalSet(0),
        LocalGet(0),
    ];
    let set = infer_i64_locals(&ops, &[], &[], &[], &[]);
    assert!(!set.contains(&0), "i32 local over-widened to i64");
}
