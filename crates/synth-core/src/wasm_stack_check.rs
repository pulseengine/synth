//! Pre-flight wasm value-stack underflow detector.
//!
//! Real wasm input is validated by the decoder (wasmparser). This module is
//! a safety net for *direct callers* of the lowering pipeline that feed in
//! raw `Vec<WasmOp>` without going through the validator — most notably the
//! fuzz harnesses, which intentionally generate malformed sequences to
//! prove the contract that lowering returns `Err`, not panics.
//!
//! The check is best-effort: control-flow ops (`Block`, `Loop`, `If`/`Else`,
//! `End`, `Br`/`BrIf`/`BrTable`, `Return`, `Call`) have stack effects that
//! depend on block types and function signatures we don't have here. When
//! the input contains any such op, validation gracefully bails out with
//! `Ok(())` rather than reporting a spurious underflow. This keeps the
//! check conservative — it never rejects valid input — at the cost of
//! catching only the underflow cases that don't involve control flow.
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

        // ---- select / nop / unreachable ---------------------------------
        // select: pops two values and a condition (i32), pushes one value
        Select => modeled(3, 1),
        Nop => modeled(0, 0),
        // unreachable is a stack-polymorphic terminator; treat as bail since
        // anything after it is unreachable code with a poison stack.
        Unreachable => StackEffect::Bail,

        // ---- control flow — bail conservatively --------------------------
        // We don't have block types / call signatures at this level, so we
        // can't compute precise effects. Yielding to upstream validation
        // is safer than rejecting valid input.
        Block | Loop | If | Else | End | Br(_) | BrIf(_) | Return | Call(_) => StackEffect::Bail,

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
    fn control_flow_bails_conservatively() {
        // A binary op after a Call would underflow if we modeled Call as
        // stack-neutral. We bail instead — accept the input, let upstream
        // wasm validation reject it if needed.
        let ops = vec![WasmOp::Call(0), WasmOp::I32Add];
        assert!(check_no_underflow(&ops).is_ok());
    }

    #[test]
    fn unreachable_terminates_check() {
        // After Unreachable, the stack is poisoned. We bail.
        let ops = vec![WasmOp::Unreachable, WasmOp::I32Add];
        assert!(check_no_underflow(&ops).is_ok());
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
}
