//! F64 Operations Test Suite
//!
//! Validates that all f64 operations are explicitly rejected by the instruction
//! selector. ARM Cortex-M3 does not have hardware floating-point support (VFP/NEON).
//! Rather than silently emitting NOPs (which produces wrong results), the transcoder
//! returns an explicit error. Modules using floats should be routed to the Kiln
//! interpreter instead.
//!
//! When VFP support is added for Cortex-M4F+ targets, these tests should be
//! updated to expect success on those targets.

use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

/// Helper: assert that a sequence of WASM ops containing a float operation
/// is rejected by the instruction selector with a synthesis error.
/// Accepts either "floating-point" or "i64" errors since some float conversions
/// require i64 inputs which are also unsupported on 32-bit ARM.
fn assert_float_rejected(wasm_ops: Vec<WasmOp>, op_name: &str) {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let result = selector.select(&wasm_ops);
    assert!(
        result.is_err(),
        "{op_name} should be rejected (no VFP on Cortex-M3)"
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("no FPU")
            || err.contains("VFP")
            || err.contains("floating-point")
            || err.contains("i64"),
        "{op_name} error should mention FPU/VFP/floating-point or i64, got: {err}"
    );
}

// ============================================================================
// F64 ARITHMETIC (4)
// ============================================================================

#[test]
fn test_f64_add() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.5), WasmOp::F64Const(2.5), WasmOp::F64Add],
        "f64.add",
    );
}

#[test]
fn test_f64_sub() {
    assert_float_rejected(
        vec![WasmOp::F64Const(5.0), WasmOp::F64Const(2.0), WasmOp::F64Sub],
        "f64.sub",
    );
}

#[test]
fn test_f64_mul() {
    assert_float_rejected(
        vec![WasmOp::F64Const(2.5), WasmOp::F64Const(4.0), WasmOp::F64Mul],
        "f64.mul",
    );
}

#[test]
fn test_f64_div() {
    assert_float_rejected(
        vec![
            WasmOp::F64Const(10.0),
            WasmOp::F64Const(3.0),
            WasmOp::F64Div,
        ],
        "f64.div",
    );
}

// ============================================================================
// F64 COMPARISONS (6)
// ============================================================================

#[test]
fn test_f64_eq() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Eq],
        "f64.eq",
    );
}

#[test]
fn test_f64_ne() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Ne],
        "f64.ne",
    );
}

#[test]
fn test_f64_lt() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Lt],
        "f64.lt",
    );
}

#[test]
fn test_f64_le() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Le],
        "f64.le",
    );
}

#[test]
fn test_f64_gt() {
    assert_float_rejected(
        vec![WasmOp::F64Const(2.0), WasmOp::F64Const(1.0), WasmOp::F64Gt],
        "f64.gt",
    );
}

#[test]
fn test_f64_ge() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Ge],
        "f64.ge",
    );
}

// ============================================================================
// F64 MATH FUNCTIONS (10)
// ============================================================================

#[test]
fn test_f64_abs() {
    assert_float_rejected(vec![WasmOp::F64Const(-1.5), WasmOp::F64Abs], "f64.abs");
}

#[test]
fn test_f64_neg() {
    assert_float_rejected(vec![WasmOp::F64Const(1.5), WasmOp::F64Neg], "f64.neg");
}

#[test]
fn test_f64_ceil() {
    assert_float_rejected(vec![WasmOp::F64Const(1.3), WasmOp::F64Ceil], "f64.ceil");
}

#[test]
fn test_f64_floor() {
    assert_float_rejected(vec![WasmOp::F64Const(1.7), WasmOp::F64Floor], "f64.floor");
}

#[test]
fn test_f64_trunc() {
    assert_float_rejected(vec![WasmOp::F64Const(1.7), WasmOp::F64Trunc], "f64.trunc");
}

#[test]
fn test_f64_nearest() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.5), WasmOp::F64Nearest],
        "f64.nearest",
    );
}

#[test]
fn test_f64_sqrt() {
    assert_float_rejected(vec![WasmOp::F64Const(4.0), WasmOp::F64Sqrt], "f64.sqrt");
}

#[test]
fn test_f64_min() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Min],
        "f64.min",
    );
}

#[test]
fn test_f64_max() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Max],
        "f64.max",
    );
}

#[test]
fn test_f64_copysign() {
    assert_float_rejected(
        vec![
            WasmOp::F64Const(1.0),
            WasmOp::F64Const(-1.0),
            WasmOp::F64Copysign,
        ],
        "f64.copysign",
    );
}

// ============================================================================
// F64 CONSTANTS AND MEMORY (3)
// ============================================================================

#[test]
fn test_f64_const() {
    // F64Const itself goes through the catch-all since there's no
    // explicit handler — it's a float operation.
    assert_float_rejected(vec![WasmOp::F64Const(3.125)], "f64.const");
}

#[test]
fn test_f64_load() {
    assert_float_rejected(
        vec![
            WasmOp::I32Const(0),
            WasmOp::F64Load {
                offset: 0,
                align: 8,
            },
        ],
        "f64.load",
    );
}

#[test]
fn test_f64_store() {
    assert_float_rejected(
        vec![
            WasmOp::I32Const(0),
            WasmOp::F64Const(1.0),
            WasmOp::F64Store {
                offset: 0,
                align: 8,
            },
        ],
        "f64.store",
    );
}

// ============================================================================
// F64 CONVERSIONS (8)
// ============================================================================

#[test]
fn test_f64_convert_i32_s() {
    assert_float_rejected(
        vec![WasmOp::I32Const(42), WasmOp::F64ConvertI32S],
        "f64.convert_i32_s",
    );
}

#[test]
fn test_f64_convert_i32_u() {
    assert_float_rejected(
        vec![WasmOp::I32Const(42), WasmOp::F64ConvertI32U],
        "f64.convert_i32_u",
    );
}

#[test]
fn test_f64_convert_i64_s() {
    assert_float_rejected(
        vec![WasmOp::I64Const(42), WasmOp::F64ConvertI64S],
        "f64.convert_i64_s",
    );
}

#[test]
fn test_f64_convert_i64_u() {
    assert_float_rejected(
        vec![WasmOp::I64Const(42), WasmOp::F64ConvertI64U],
        "f64.convert_i64_u",
    );
}

#[test]
fn test_f64_promote_f32() {
    assert_float_rejected(
        vec![WasmOp::F32Const(1.5), WasmOp::F64PromoteF32],
        "f64.promote_f32",
    );
}

#[test]
fn test_f64_reinterpret_i64() {
    assert_float_rejected(
        vec![WasmOp::I64Const(0), WasmOp::F64ReinterpretI64],
        "f64.reinterpret_i64",
    );
}

#[test]
fn test_i64_reinterpret_f64() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::I64ReinterpretF64],
        "i64.reinterpret_f64",
    );
}

#[test]
fn test_i32_trunc_f64_s() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.7), WasmOp::I32TruncF64S],
        "i32.trunc_f64_s",
    );
}

#[test]
fn test_i32_trunc_f64_u() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.7), WasmOp::I32TruncF64U],
        "i32.trunc_f64_u",
    );
}

#[test]
fn test_i64_trunc_f64_s() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.7), WasmOp::I64TruncF64S],
        "i64.trunc_f64_s",
    );
}

#[test]
fn test_i64_trunc_f64_u() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.7), WasmOp::I64TruncF64U],
        "i64.trunc_f64_u",
    );
}

// ============================================================================
// EDGE CASES
// ============================================================================

#[test]
fn test_f64_special_values() {
    // NaN, infinity, etc. should all be rejected at the instruction selection level
    assert_float_rejected(vec![WasmOp::F64Const(f64::NAN)], "f64.const(NaN)");
    assert_float_rejected(vec![WasmOp::F64Const(f64::INFINITY)], "f64.const(infinity)");
    assert_float_rejected(
        vec![WasmOp::F64Const(f64::NEG_INFINITY)],
        "f64.const(-infinity)",
    );
}

#[test]
fn test_f64_nan_propagation() {
    assert_float_rejected(
        vec![
            WasmOp::F64Const(f64::NAN),
            WasmOp::F64Const(1.0),
            WasmOp::F64Add,
        ],
        "f64.add(NaN)",
    );
}

#[test]
fn test_f64_signed_zero() {
    assert_float_rejected(vec![WasmOp::F64Const(-0.0)], "f64.const(-0.0)");
}

#[test]
fn test_f64_infinity_arithmetic() {
    assert_float_rejected(
        vec![
            WasmOp::F64Const(f64::INFINITY),
            WasmOp::F64Const(1.0),
            WasmOp::F64Add,
        ],
        "f64.add(infinity)",
    );
}

#[test]
fn test_f64_comparison_chain() {
    assert_float_rejected(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Lt],
        "f64.lt (chain)",
    );
}

#[test]
fn test_f64_complex_expression() {
    assert_float_rejected(
        vec![WasmOp::F64Const(2.0), WasmOp::F64Const(3.0), WasmOp::F64Add],
        "f64.add (complex)",
    );
}

#[test]
fn test_f64_mixed_with_f32() {
    // F32 operations should also be rejected
    assert_float_rejected(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Add],
        "f32.add",
    );
}
