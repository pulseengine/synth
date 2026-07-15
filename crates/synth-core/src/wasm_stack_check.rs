//! Pre-flight wasm value-stack underflow detector.
//!
//! Real wasm input is validated by the decoder (wasmparser). This module is
//! a safety net for *direct callers* of the lowering pipeline that feed in
//! raw `Vec<WasmOp>` without going through the validator — most notably the
//! fuzz harnesses, which intentionally generate malformed sequences to
//! prove the contract that lowering returns `Err`, not panics.
//!
//! The check is best-effort and, above all, *sound* — it never rejects valid
//! wasm. Stack effects that depend on data we don't have here (block-result
//! arities, callee signatures) are handled conservatively:
//!
//! * `Call` and unmodeled ops (SIMD, etc.) bail out with `Ok(())` — their
//!   effect is signature/type dependent.
//! * The stack-polymorphic terminators `unreachable`/`return`/`br`/`br_table`
//!   also bail with `Ok(())`: everything after them (up to the enclosing
//!   `end`) is unreachable and, per the wasm spec, type-checks against an
//!   infinite-depth polymorphic stack, so depth-only reasoning would produce
//!   *false* underflows there (issue #329).
//! * `Block`/`Loop`/`If`/`Else`/`End` are modeled as stack-neutral. In
//!   reachable code the depth counter can then only ever *over*-count (it
//!   never pops the `if` condition and never resets at `else`/`end`), so it
//!   cannot invent an underflow — it just catches fewer of them past a block.
//!
//! The net effect: the check reliably rejects the control-flow-free underflow
//! shapes (the fuzz-harness bug class below) and never false-rejects a
//! `wasm-tools`-valid module.
//!
//! The bug this was written for ([PR #113 fuzz harness wasm_ops_lower_or_error,
//! input `[I32DivS]` with empty initial stack]) sits squarely inside the
//! modeled subset, which is the common case.
//!
//! ## Scope
//!
//! The validator does *not* enforce wasm type checking — it only tracks
//! stack *depth*. So `i32.const ; i64.add` will pass even though it's
//! type-invalid. Type errors fall to the lowering pipeline, which now
//! raises them as `Err` (per PR #117 — the same audit pass).
//!
//! ## Why not just call wasmparser?
//!
//! Two reasons:
//! * The lowering pipeline accepts `Vec<WasmOp>` (its own enum), not raw
//!   wasm bytes. Threading wasmparser back would require a re-encoder.
//! * The harnesses *want* to feed malformed input. We want a cheap local
//!   check that returns Err rather than panics, not full re-validation.
//!
//! See PR #117 for the original fuzz crash that motivated this module.
//!
//! Note: `Select` is modeled as `pop 3, push 1` — wasm's `select` consumes
//! two values and a condition. `MemoryGrow` pops a page count and pushes
//! the previous size (or -1). `MemorySize` is a pure push.

use crate::Error;
use crate::wasm_op::WasmOp;

/// Pre-flight check: returns `Err(Error::validation(...))` if any modeled
/// op would underflow the wasm value stack. If the sequence contains
/// control-flow ops we don't model, returns `Ok(())` (bails conservatively).
pub fn check_no_underflow(wasm_ops: &[WasmOp]) -> crate::Result<()> {
    let mut depth: i64 = 0;
    for (idx, op) in wasm_ops.iter().enumerate() {
        match stack_effect_or_bail(op) {
            StackEffect::Modeled { pops, pushes } => {
                if depth < pops as i64 {
                    return Err(Error::validation(format!(
                        "wasm value-stack underflow at op {idx} ({op:?}): \
                         would pop {pops} from depth {depth}"
                    )));
                }
                depth -= pops as i64;
                depth += pushes as i64;
            }
            StackEffect::Bail => return Ok(()),
        }
    }
    Ok(())
}

/// #587: a conservative UPPER BOUND on the wasm value-stack depth this op
/// sequence can reach. Used by the ARM backend's `pool-grow` exhaustion-
/// recovery rung to size the i64 spill-slot pool: the number of values
/// *simultaneously* spilled by the direct selector can never exceed the
/// number of values simultaneously live on the operand stack, so a pool of
/// `max_depth_bound` slots (plus the resolver/result-parking transients the
/// caller adds) cannot exhaust through the deepest-value spill loop.
///
/// Over-approximation rules (never under-counts in reachable code):
/// * Modeled ops apply their exact pops/pushes; a would-be underflow clamps
///   to 0 (malformed input is someone else's Err, not a panic here).
/// * Unmodeled/`Bail` ops (`call`, terminators, SIMD, …) are treated as net
///   `+1` — every wasm op pushes at most one value net, so this only ever
///   over-counts (a call pops its args; a terminator pushes nothing).
/// * `Block`/`Loop`/`If`/`Else`/`End` are stack-neutral in the effects table,
///   which over-counts (`if` really pops its condition) — same direction.
pub fn max_depth_bound(wasm_ops: &[WasmOp]) -> u32 {
    let mut depth: i64 = 0;
    let mut max: i64 = 0;
    for op in wasm_ops {
        match stack_effect_or_bail(op) {
            StackEffect::Modeled { pops, pushes } => {
                depth = (depth - pops as i64).max(0) + pushes as i64;
            }
            StackEffect::Bail => depth += 1,
        }
        max = max.max(depth);
    }
    u32::try_from(max).unwrap_or(u32::MAX)
}

enum StackEffect {
    Modeled { pops: u32, pushes: u32 },
    Bail,
}

fn modeled(pops: u32, pushes: u32) -> StackEffect {
    StackEffect::Modeled { pops, pushes }
}

#[allow(clippy::too_many_lines)]
fn stack_effect_or_bail(op: &WasmOp) -> StackEffect {
    use WasmOp::*;
    match op {
        // ---- pushes (constants, reads) -----------------------------------
        I32Const(_) | I64Const(_) | F32Const(_) | F64Const(_) | V128Const(_) | LocalGet(_)
        | GlobalGet(_) | MemorySize(_) => modeled(0, 1),

        // ---- i32 binary (pop 2, push 1) ----------------------------------
        I32Add | I32Sub | I32Mul | I32DivS | I32DivU | I32RemS | I32RemU | I32And | I32Or
        | I32Xor | I32Shl | I32ShrS | I32ShrU | I32Rotl | I32Rotr | I32Eq | I32Ne | I32LtS
        | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS | I32GeU => modeled(2, 1),

        // ---- i32 unary (pop 1, push 1) -----------------------------------
        I32Clz | I32Ctz | I32Popcnt | I32Eqz | I32Extend8S | I32Extend16S | I32WrapI64 => {
            modeled(1, 1)
        }

        // ---- i64 binary (pop 2, push 1) ----------------------------------
        I64Add | I64Sub | I64Mul | I64DivS | I64DivU | I64RemS | I64RemU | I64And | I64Or
        | I64Xor | I64Shl | I64ShrS | I64ShrU | I64Rotl | I64Rotr | I64Eq | I64Ne | I64LtS
        | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU | I64GeS | I64GeU => modeled(2, 1),

        // ---- i64 unary (pop 1, push 1) -----------------------------------
        I64Clz | I64Ctz | I64Popcnt | I64Eqz | I64Extend8S | I64Extend16S | I64Extend32S
        | I64ExtendI32S | I64ExtendI32U => modeled(1, 1),

        // ---- f32 binary --------------------------------------------------
        F32Add | F32Sub | F32Mul | F32Div | F32Eq | F32Ne | F32Lt | F32Le | F32Gt | F32Ge
        | F32Min | F32Max | F32Copysign => modeled(2, 1),

        // ---- f32 unary ---------------------------------------------------
        F32Abs | F32Neg | F32Ceil | F32Floor | F32Trunc | F32Nearest | F32Sqrt => modeled(1, 1),

        // ---- f64 binary --------------------------------------------------
        F64Add | F64Sub | F64Mul | F64Div | F64Eq | F64Ne | F64Lt | F64Le | F64Gt | F64Ge
        | F64Min | F64Max | F64Copysign => modeled(2, 1),

        // ---- f64 unary ---------------------------------------------------
        F64Abs | F64Neg | F64Ceil | F64Floor | F64Trunc | F64Nearest | F64Sqrt => modeled(1, 1),

        // ---- f32 ↔ f64 / int conversions (pop 1, push 1) -----------------
        F32ConvertI32S | F32ConvertI32U | F32ConvertI64S | F32ConvertI64U | F32DemoteF64
        | F32ReinterpretI32 | I32ReinterpretF32 | I32TruncF32S | I32TruncF32U | F64ConvertI32S
        | F64ConvertI32U | F64ConvertI64S | F64ConvertI64U | F64PromoteF32 | F64ReinterpretI64
        | I64ReinterpretF64 | I64TruncF64S | I64TruncF64U | I32TruncF64S | I32TruncF64U => {
            modeled(1, 1)
        }

        // ---- pop-only ----------------------------------------------------
        LocalSet(_) | GlobalSet(_) | Drop => modeled(1, 0),

        // ---- pop-modify-push (peek-write) --------------------------------
        LocalTee(_) => modeled(1, 1),

        // ---- memory ------------------------------------------------------
        // load: pops address, pushes value
        I32Load { .. }
        | I32Load8S { .. }
        | I32Load8U { .. }
        | I32Load16S { .. }
        | I32Load16U { .. }
        | I64Load { .. }
        | I64Load8S { .. }
        | I64Load8U { .. }
        | I64Load16S { .. }
        | I64Load16U { .. }
        | I64Load32S { .. }
        | I64Load32U { .. }
        | F32Load { .. }
        | F64Load { .. } => modeled(1, 1),
        // store: pops value, pops address
        I32Store { .. }
        | I32Store8 { .. }
        | I32Store16 { .. }
        | I64Store { .. }
        | I64Store8 { .. }
        | I64Store16 { .. }
        | I64Store32 { .. }
        | F32Store { .. }
        | F64Store { .. } => modeled(2, 0),
        // memory.grow: pops page count, pushes previous size or -1
        MemoryGrow(_) => modeled(1, 1),

        // ---- bulk memory (#374) -----------------------------------------
        // memory.copy(dst, src, len) and memory.fill(dst, val, len) each pop
        // three i32 operands and push nothing.
        MemoryCopy | MemoryFill => modeled(3, 0),

        // ---- multi-memory (#406) ----------------------------------------
        // A wrapped load/store has exactly its inner op's stack effect — the
        // memory index changes the BASE it addresses, not the operand shape.
        MultiMemory { op, .. } => stack_effect_or_bail(op),

        // ---- select / nop -----------------------------------------------
        // select: pops two values and a condition (i32), pushes one value
        Select => modeled(3, 1),
        Nop => modeled(0, 0),

        // ---- stack-polymorphic terminators (#329) ------------------------
        // `unreachable`, `return`, `br`, and `br_table` unconditionally
        // transfer control, so every op *after* one of them (up to the
        // enclosing `end`) is unreachable and, per the wasm spec, type-checks
        // against an infinite-depth *polymorphic* stack. A
        // `drop`/`select`/`local.set`/binary op in that dead region is
        // perfectly valid wasm even at depth 0 — but our finite depth counter
        // keeps decrementing and reports a *false* underflow (issue #329).
        //
        // (Note: falcon's original `func_30`/`func_39` underflows were a
        // *different* root cause — the old #369 silent float-op decoder drop,
        // which dropped pushes and starved the abstract stack; that was fixed
        // by #369's loud-skip. This arm closes the remaining, latent
        // dead-code-after-terminator false-positive in the same model.)
        //
        // Note the model can only ever *over*-count in reachable code (it
        // never pops the `if` condition, never resets at `else`/`end`), so a
        // false underflow is impossible there. Dead code after a polymorphic
        // terminator is the sole false-reject class — and without block-result
        // arities we cannot tell where reachable code resumes after the
        // matching `end`. So we BAIL to `Ok(())` at the terminator: this keeps
        // the check SOUND (it can only miss a genuine underflow, never invent
        // one) and matches the module's documented "accept when unsure" intent.
        //
        // This does NOT reintroduce the PR #117 fuzz crashes. Those were
        // panics deep in `wasm_to_ir`/`ir_to_arm` on shapes like
        // `[Unreachable, I32GeS]`; the panic sites were since converted to
        // typed `Err` (issue #93 / PR #101 `get_arm_reg`, issue #121
        // `slot_stack`, and the `Unreachable`/`Return` handlers in
        // `wasm_to_ir`). The fuzz contract is *no panic* — `Ok` or `Err` both
        // pass — and those downstream changes, not this pre-flight, guarantee
        // it. See the `*_does_not_panic_*` regression tests in synth-synthesis.
        Unreachable | Return | Br(_) | BrTable { .. } => StackEffect::Bail,
        // BrIf pops the condition (i32) but does NOT terminate — the
        // fall-through path keeps executing reachable code. After it the stack
        // lost the condition, so a genuine depth-0 `br_if` still underflows
        // (kept as a real-underflow anchor).
        BrIf(_) => modeled(1, 0),
        // Block / Loop / If / Else / End — control region delimiters. Their
        // stack effect depends on block type, which we don't have. Treat as
        // stack-neutral; if a real underflow lurks past one of these, we
        // accept it (matches the pre-flight's "best-effort safety net" intent).
        Block | Loop | If | Else | End => modeled(0, 0),
        // Call — pops N args, pushes M results. Without the callee's
        // signature we can't compute this. Yield to upstream validation.
        Call(_) => StackEffect::Bail,

        // ---- SIMD lane ops, etc. — bail ---------------------------------
        // The selector doesn't fully support these yet; their stack effects
        // are well-defined but we don't enumerate them here. Bail.
        _ => StackEffect::Bail,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_op_at_empty_stack_is_underflow() {
        // This is the exact crash input from PR #113's fuzz harness:
        // FuzzInput { num_params: 1, ops: [I32DivS] }
        let err = check_no_underflow(&[WasmOp::I32DivS]).unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)), "got: {err:?}");
        let msg = format!("{err}");
        assert!(msg.contains("underflow"));
        assert!(msg.contains("I32DivS"));
    }

    #[test]
    fn well_formed_add_passes() {
        let ops = vec![WasmOp::I32Const(1), WasmOp::I32Const(2), WasmOp::I32Add];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn unary_op_at_empty_stack_is_underflow() {
        let err = check_no_underflow(&[WasmOp::I32Eqz]).unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)));
    }

    #[test]
    fn drop_at_empty_stack_is_underflow() {
        let err = check_no_underflow(&[WasmOp::Drop]).unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)));
    }

    #[test]
    fn bulk_memory_pops_three_374() {
        // memory.copy / memory.fill pop 3, push 0: three pushed operands then the
        // op must balance to depth 0.
        for op in [WasmOp::MemoryCopy, WasmOp::MemoryFill] {
            let ok = vec![
                WasmOp::I32Const(0),
                WasmOp::I32Const(0),
                WasmOp::I32Const(0),
                op.clone(),
            ];
            assert!(check_no_underflow(&ok).is_ok(), "{op:?} with 3 operands");
            // only two operands -> underflow
            let bad = vec![WasmOp::I32Const(0), WasmOp::I32Const(0), op.clone()];
            assert!(
                matches!(
                    check_no_underflow(&bad).unwrap_err(),
                    Error::ValidationError(_)
                ),
                "{op:?} with 2 operands must underflow"
            );
        }
    }

    #[test]
    fn store_at_empty_stack_is_underflow() {
        let err = check_no_underflow(&[WasmOp::I32Store {
            offset: 0,
            align: 2,
        }])
        .unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)));
    }

    #[test]
    fn select_needs_three_operands() {
        // select with only 2 operands underflows.
        let ops = vec![WasmOp::I32Const(1), WasmOp::I32Const(2), WasmOp::Select];
        let err = check_no_underflow(&ops).unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)));
    }

    #[test]
    fn select_with_three_operands_passes() {
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::I32Const(0),
            WasmOp::Select,
        ];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn call_bails_conservatively() {
        // Call(_) has a callee-signature-dependent stack effect we can't
        // compute here, so we bail (accept). Upstream wasm validation
        // catches real signature mismatches.
        let ops = vec![WasmOp::Call(0), WasmOp::I32Add];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn return_then_binary_op_is_accepted_dead_code_329() {
        // #329: after `return`, the rest of the block is unreachable and
        // type-checks against a polymorphic (infinite-depth) stack in wasm, so
        // `[Return, I64Eqz]` is VALID wasm — the pre-flight must not invent an
        // underflow. (It previously did, modeling `Return` as stack-neutral.)
        // The downstream `wasm_to_ir` panic-safety this used to stand in for is
        // now guaranteed by the `slot_stack`/`get_arm_reg` Err conversions —
        // see the synth-synthesis `*_does_not_panic_*` regression tests.
        let ops = vec![WasmOp::Return, WasmOp::I64Eqz];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn br_then_binary_op_is_accepted_dead_code_329() {
        // Mirror of the Return case for unconditional branch: code after `br`
        // is unreachable/polymorphic, hence accepted.
        let ops = vec![WasmOp::Br(0), WasmOp::I32Add];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn br_table_then_pop_is_accepted_dead_code_329() {
        // br_table is also a stack-polymorphic terminator.
        let ops = vec![
            WasmOp::BrTable {
                targets: vec![0],
                default: 0,
            },
            WasmOp::Select,
        ];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn br_if_pops_condition() {
        // BrIf pops one (the i32 condition). At depth 0, the BrIf itself
        // underflows.
        let ops = vec![WasmOp::BrIf(0)];
        let err = check_no_underflow(&ops).unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)));
    }

    #[test]
    fn br_if_with_condition_then_op_is_ok() {
        // BrIf pops 1 (the condition), then I32Const pushes 1, then
        // I32Eqz pops 1 / pushes 1 — no underflow.
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::BrIf(0),
            WasmOp::I32Const(0),
            WasmOp::I32Eqz,
        ];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn unreachable_then_binary_op_is_accepted_dead_code_329() {
        // `[Unreachable, I32GeS]` is VALID wasm: after `unreachable` the stack
        // is polymorphic, so i32.ge_s type-checks. The pre-flight must accept
        // it (it previously reported a false underflow). The `wasm_to_ir`
        // no-panic guarantee this used to proxy for now lives downstream.
        let ops = vec![WasmOp::Unreachable, WasmOp::I32GeS];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn unreachable_then_consts_then_binary_op_is_ok() {
        // Also valid — and accepted whether or not the consts re-push (we bail
        // at the `unreachable`).
        let ops = vec![
            WasmOp::Unreachable,
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::I32GeS,
        ];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn unreachable_then_drop_is_accepted_329() {
        // Minimal #329 repro shape: `(unreachable) (drop)` — wasm-tools valid,
        // previously rejected with "would pop 1 from depth 0".
        let ops = vec![WasmOp::Unreachable, WasmOp::Drop];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn return_then_select_is_accepted_329() {
        // The #329 `func_39` Select shape: a select in dead code after a
        // terminator. Previously "would pop 3 from depth N".
        let ops = vec![WasmOp::I32Const(0), WasmOp::Return, WasmOp::Select];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn return_then_local_set_is_accepted_329() {
        // The #329 `func_30` LocalSet shape: a local.set in dead code.
        // Previously "would pop 1 from depth 0".
        let ops = vec![WasmOp::Return, WasmOp::LocalSet(0)];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn reachable_select_with_block_result_operand_is_ok_329() {
        // A reachable select whose operands include a block result stays
        // accepted — the depth counter over-counts across the block markers,
        // so it never false-rejects. (Sanity that we didn't over-loosen away
        // from reachable control flow.)
        let ops = vec![
            WasmOp::Block,
            WasmOp::I32Const(5),
            WasmOp::End,
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::Select,
        ];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn reachable_binary_op_underflow_still_caught_after_block() {
        // Bounded-loosening anchor: a genuine underflow that does NOT sit in a
        // dead region is still caught. `Block` is stack-neutral, then I32Add at
        // depth 0 underflows.
        let ops = vec![WasmOp::Block, WasmOp::I32Add];
        let err = check_no_underflow(&ops).unwrap_err();
        assert!(matches!(err, Error::ValidationError(_)));
    }

    #[test]
    fn const_then_unary_then_binary() {
        // const → eqz → const → const → add — last add needs 2, has 3.
        let ops = vec![
            WasmOp::I32Const(0),
            WasmOp::I32Eqz,
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::I32Add,
        ];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn empty_input_is_ok() {
        assert!(check_no_underflow(&[]).is_ok());
    }

    #[test]
    fn max_depth_bound_exact_on_modeled_ops() {
        // #587: 3 consts (depth 3) folded to 1 — the bound is the peak, 3.
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::I32Const(3),
            WasmOp::I32Add,
            WasmOp::I32Add,
        ];
        assert_eq!(max_depth_bound(&ops), 3);
        assert_eq!(max_depth_bound(&[]), 0);
    }

    #[test]
    fn max_depth_bound_over_approximates_unmodeled_ops() {
        // #587: `call` bails in the underflow checker; the bound treats it as
        // net +1 (an over-approximation, never an under-count).
        let ops = vec![WasmOp::I32Const(1), WasmOp::Call(0), WasmOp::I32Add];
        assert!(max_depth_bound(&ops) >= 2);
    }
}
