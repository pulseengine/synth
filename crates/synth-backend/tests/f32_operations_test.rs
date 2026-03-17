//! F32 Operations Integration Test Suite
//!
//! Validates that F32 operations:
//! - Compile successfully on Cortex-M4F (has single-precision FPU)
//! - Are rejected on Cortex-M3 (no FPU)
//! - Generate correct ArmOp variants through instruction selection

use synth_core::target::FPUPrecision;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

// ============================================================================
// HELPERS
// ============================================================================

/// Create an instruction selector with cortex-m4f FPU capability
fn selector_with_fpu() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_target(Some(FPUPrecision::Single), "cortex-m4f");
    selector
}

/// Create an instruction selector with no FPU (cortex-m3)
fn selector_no_fpu() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    InstructionSelector::new(db.rules().to_vec())
}

/// Assert that a WASM op sequence compiles on cortex-m4f
fn assert_f32_compiles(wasm_ops: Vec<WasmOp>, op_name: &str) {
    let mut selector = selector_with_fpu();
    let result = selector.select(&wasm_ops);
    assert!(
        result.is_ok(),
        "{op_name} should compile on cortex-m4f, got: {}",
        result.unwrap_err()
    );
    let instrs = result.unwrap();
    assert!(!instrs.is_empty(), "{op_name} should produce instructions");
}

/// Assert that a WASM op sequence is rejected on cortex-m3
fn assert_f32_rejected_no_fpu(wasm_ops: Vec<WasmOp>, op_name: &str) {
    let mut selector = selector_no_fpu();
    let result = selector.select(&wasm_ops);
    assert!(result.is_err(), "{op_name} should be rejected on cortex-m3");
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("no FPU"),
        "{op_name} error should mention 'no FPU', got: {err}"
    );
}

// ============================================================================
// F32 ARITHMETIC — compiles on cortex-m4f
// ============================================================================

#[test]
fn test_f32_add_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Add],
        "f32.add",
    );
}

#[test]
fn test_f32_sub_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(5.0), WasmOp::F32Const(2.0), WasmOp::F32Sub],
        "f32.sub",
    );
}

#[test]
fn test_f32_mul_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(3.0), WasmOp::F32Const(4.0), WasmOp::F32Mul],
        "f32.mul",
    );
}

#[test]
fn test_f32_div_compiles() {
    assert_f32_compiles(
        vec![
            WasmOp::F32Const(10.0),
            WasmOp::F32Const(3.0),
            WasmOp::F32Div,
        ],
        "f32.div",
    );
}

// ============================================================================
// F32 MATH FUNCTIONS
// ============================================================================

#[test]
fn test_f32_abs_compiles() {
    assert_f32_compiles(vec![WasmOp::F32Const(-1.5), WasmOp::F32Abs], "f32.abs");
}

#[test]
fn test_f32_neg_compiles() {
    assert_f32_compiles(vec![WasmOp::F32Const(1.5), WasmOp::F32Neg], "f32.neg");
}

#[test]
fn test_f32_sqrt_compiles() {
    assert_f32_compiles(vec![WasmOp::F32Const(4.0), WasmOp::F32Sqrt], "f32.sqrt");
}

// ============================================================================
// F32 COMPARISONS
// ============================================================================

#[test]
fn test_f32_eq_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(1.0), WasmOp::F32Eq],
        "f32.eq",
    );
}

#[test]
fn test_f32_ne_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Ne],
        "f32.ne",
    );
}

#[test]
fn test_f32_lt_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Lt],
        "f32.lt",
    );
}

#[test]
fn test_f32_le_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Le],
        "f32.le",
    );
}

#[test]
fn test_f32_gt_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(2.0), WasmOp::F32Const(1.0), WasmOp::F32Gt],
        "f32.gt",
    );
}

#[test]
fn test_f32_ge_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(2.0), WasmOp::F32Const(1.0), WasmOp::F32Ge],
        "f32.ge",
    );
}

// ============================================================================
// F32 CONSTANTS AND MEMORY
// ============================================================================

#[test]
fn test_f32_const_compiles() {
    assert_f32_compiles(vec![WasmOp::F32Const(3.125)], "f32.const");
}

#[test]
fn test_f32_const_zero_compiles() {
    assert_f32_compiles(vec![WasmOp::F32Const(0.0)], "f32.const 0.0");
}

#[test]
fn test_f32_load_compiles() {
    assert_f32_compiles(
        vec![
            WasmOp::I32Const(0),
            WasmOp::F32Load {
                offset: 0,
                align: 4,
            },
        ],
        "f32.load",
    );
}

#[test]
fn test_f32_store_compiles() {
    assert_f32_compiles(
        vec![
            WasmOp::I32Const(0),
            WasmOp::F32Const(1.0),
            WasmOp::F32Store {
                offset: 0,
                align: 4,
            },
        ],
        "f32.store",
    );
}

// ============================================================================
// F32 CONVERSIONS
// ============================================================================

#[test]
fn test_f32_convert_i32_s_compiles() {
    assert_f32_compiles(
        vec![WasmOp::I32Const(42), WasmOp::F32ConvertI32S],
        "f32.convert_i32_s",
    );
}

#[test]
fn test_f32_convert_i32_u_compiles() {
    assert_f32_compiles(
        vec![WasmOp::I32Const(42), WasmOp::F32ConvertI32U],
        "f32.convert_i32_u",
    );
}

#[test]
fn test_f32_reinterpret_i32_compiles() {
    assert_f32_compiles(
        vec![WasmOp::I32Const(0x3F800000), WasmOp::F32ReinterpretI32],
        "f32.reinterpret_i32",
    );
}

#[test]
fn test_i32_reinterpret_f32_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(1.0), WasmOp::I32ReinterpretF32],
        "i32.reinterpret_f32",
    );
}

#[test]
fn test_i32_trunc_f32_s_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(3.7), WasmOp::I32TruncF32S],
        "i32.trunc_f32_s",
    );
}

#[test]
fn test_i32_trunc_f32_u_compiles() {
    assert_f32_compiles(
        vec![WasmOp::F32Const(3.7), WasmOp::I32TruncF32U],
        "i32.trunc_f32_u",
    );
}

// ============================================================================
// F32 PSEUDO-OPS — now supported on cortex-m4f via VFP sequences
// ============================================================================

#[test]
fn test_f32_ceil_compiles_on_m4f() {
    let mut selector = selector_with_fpu();
    let result = selector.select(&[WasmOp::F32Const(1.5), WasmOp::F32Ceil]);
    assert!(result.is_ok(), "f32.ceil should compile on cortex-m4f");
}

#[test]
fn test_f32_floor_compiles_on_m4f() {
    let mut selector = selector_with_fpu();
    let result = selector.select(&[WasmOp::F32Const(1.5), WasmOp::F32Floor]);
    assert!(result.is_ok(), "f32.floor should compile on cortex-m4f");
}

#[test]
fn test_f32_min_compiles_on_m4f() {
    let mut selector = selector_with_fpu();
    let result = selector.select(&[WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Min]);
    assert!(result.is_ok(), "f32.min should compile on cortex-m4f");
}

#[test]
fn test_f32_copysign_compiles_on_m4f() {
    let mut selector = selector_with_fpu();
    let result = selector.select(&[
        WasmOp::F32Const(1.0),
        WasmOp::F32Const(-1.0),
        WasmOp::F32Copysign,
    ]);
    assert!(result.is_ok(), "f32.copysign should compile on cortex-m4f");
}

// ============================================================================
// CORTEX-M3 REJECTION — all F32 ops rejected without FPU
// ============================================================================

#[test]
fn test_f32_add_rejected_no_fpu() {
    assert_f32_rejected_no_fpu(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(2.0), WasmOp::F32Add],
        "f32.add",
    );
}

#[test]
fn test_f32_const_rejected_no_fpu() {
    assert_f32_rejected_no_fpu(vec![WasmOp::F32Const(1.0)], "f32.const");
}

#[test]
fn test_f32_sqrt_rejected_no_fpu() {
    assert_f32_rejected_no_fpu(vec![WasmOp::F32Const(4.0), WasmOp::F32Sqrt], "f32.sqrt");
}

#[test]
fn test_f32_eq_rejected_no_fpu() {
    assert_f32_rejected_no_fpu(
        vec![WasmOp::F32Const(1.0), WasmOp::F32Const(1.0), WasmOp::F32Eq],
        "f32.eq",
    );
}

#[test]
fn test_f32_load_rejected_no_fpu() {
    assert_f32_rejected_no_fpu(
        vec![
            WasmOp::I32Const(0),
            WasmOp::F32Load {
                offset: 0,
                align: 4,
            },
        ],
        "f32.load",
    );
}
