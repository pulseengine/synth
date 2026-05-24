//! F64 Operations Integration Test Suite
//!
//! Validates that F64 operations:
//! - Compile successfully on Cortex-M7DP (has double-precision FPU)
//! - Are rejected on Cortex-M4F (single-precision FPU only)
//! - Are rejected on Cortex-M3 (no FPU)
//!
//! Targets without a double-precision FPU must surface a typed error that
//! mentions the missing capability — silently emitting wrong code or
//! panicking is unacceptable.

use synth_core::target::FPUPrecision;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

// ============================================================================
// HELPERS
// ============================================================================

/// Selector configured for Cortex-M7DP (double-precision FPU).
fn selector_with_dp_fpu() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_target(Some(FPUPrecision::Double), "cortex-m7dp");
    selector
}

/// Selector configured for Cortex-M4F (single-precision FPU only).
fn selector_with_sp_fpu() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_target(Some(FPUPrecision::Single), "cortex-m4f");
    selector
}

/// Selector configured for Cortex-M3 (no FPU).
fn selector_no_fpu() -> InstructionSelector {
    let db = RuleDatabase::with_standard_rules();
    InstructionSelector::new(db.rules().to_vec())
}

/// Assert that an F64 op sequence compiles on Cortex-M7DP.
fn assert_f64_compiles(wasm_ops: Vec<WasmOp>, op_name: &str) {
    let mut selector = selector_with_dp_fpu();
    let result = selector.select(&wasm_ops);
    assert!(
        result.is_ok(),
        "{op_name} should compile on cortex-m7dp, got: {}",
        result.unwrap_err()
    );
    let instrs = result.unwrap();
    assert!(!instrs.is_empty(), "{op_name} should produce instructions");
}

/// Assert that an F64 op sequence is rejected on Cortex-M4F (no DP FPU).
fn assert_f64_rejected_on_m4f(wasm_ops: Vec<WasmOp>, op_name: &str) {
    let mut selector = selector_with_sp_fpu();
    let result = selector.select(&wasm_ops);
    assert!(
        result.is_err(),
        "{op_name} should be rejected on cortex-m4f (single-precision only)"
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("double-precision") || err.contains("F64") || err.contains("i64"),
        "{op_name} error should mention double-precision/F64/i64, got: {err}"
    );
}

/// Assert that an F64 op sequence is rejected on Cortex-M3 (no FPU at all).
fn assert_f64_rejected_no_fpu(wasm_ops: Vec<WasmOp>, op_name: &str) {
    let mut selector = selector_no_fpu();
    let result = selector.select(&wasm_ops);
    assert!(result.is_err(), "{op_name} should be rejected on cortex-m3");
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
// F64 ARITHMETIC — compiles on Cortex-M7DP
// ============================================================================

#[test]
fn test_f64_add_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.5), WasmOp::F64Const(2.5), WasmOp::F64Add],
        "f64.add",
    );
}

#[test]
fn test_f64_sub_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(5.0), WasmOp::F64Const(2.0), WasmOp::F64Sub],
        "f64.sub",
    );
}

#[test]
fn test_f64_mul_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(2.5), WasmOp::F64Const(4.0), WasmOp::F64Mul],
        "f64.mul",
    );
}

#[test]
fn test_f64_div_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![
            WasmOp::F64Const(10.0),
            WasmOp::F64Const(3.0),
            WasmOp::F64Div,
        ],
        "f64.div",
    );
}

// ============================================================================
// F64 COMPARISONS — compiles on Cortex-M7DP
// ============================================================================

#[test]
fn test_f64_eq_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Eq],
        "f64.eq",
    );
}

#[test]
fn test_f64_ne_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Ne],
        "f64.ne",
    );
}

#[test]
fn test_f64_lt_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Lt],
        "f64.lt",
    );
}

#[test]
fn test_f64_le_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Le],
        "f64.le",
    );
}

#[test]
fn test_f64_gt_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(2.0), WasmOp::F64Const(1.0), WasmOp::F64Gt],
        "f64.gt",
    );
}

#[test]
fn test_f64_ge_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Ge],
        "f64.ge",
    );
}

// ============================================================================
// F64 MATH FUNCTIONS — compiles on Cortex-M7DP
// ============================================================================

#[test]
fn test_f64_abs_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(-1.5), WasmOp::F64Abs], "f64.abs");
}

#[test]
fn test_f64_neg_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(1.5), WasmOp::F64Neg], "f64.neg");
}

#[test]
fn test_f64_sqrt_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(4.0), WasmOp::F64Sqrt], "f64.sqrt");
}

#[test]
fn test_f64_ceil_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(1.3), WasmOp::F64Ceil], "f64.ceil");
}

#[test]
fn test_f64_floor_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(1.7), WasmOp::F64Floor], "f64.floor");
}

#[test]
fn test_f64_trunc_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(1.7), WasmOp::F64Trunc], "f64.trunc");
}

#[test]
fn test_f64_nearest_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.5), WasmOp::F64Nearest],
        "f64.nearest",
    );
}

#[test]
fn test_f64_min_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Min],
        "f64.min",
    );
}

#[test]
fn test_f64_max_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Max],
        "f64.max",
    );
}

#[test]
fn test_f64_copysign_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![
            WasmOp::F64Const(1.0),
            WasmOp::F64Const(-1.0),
            WasmOp::F64Copysign,
        ],
        "f64.copysign",
    );
}

// ============================================================================
// F64 CONSTANTS AND MEMORY — compiles on Cortex-M7DP
// ============================================================================

#[test]
fn test_f64_const_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(3.125)], "f64.const");
}

#[test]
fn test_f64_const_zero_compiles_on_m7dp() {
    assert_f64_compiles(vec![WasmOp::F64Const(0.0)], "f64.const 0.0");
}

#[test]
fn test_f64_const_special_compiles_on_m7dp() {
    // Special values are 64-bit constant-pool / immediate; selector must accept.
    assert_f64_compiles(vec![WasmOp::F64Const(f64::NAN)], "f64.const NaN");
    assert_f64_compiles(vec![WasmOp::F64Const(f64::INFINITY)], "f64.const +inf");
    assert_f64_compiles(vec![WasmOp::F64Const(f64::NEG_INFINITY)], "f64.const -inf");
    assert_f64_compiles(vec![WasmOp::F64Const(-0.0)], "f64.const -0.0");
}

#[test]
fn test_f64_load_compiles_on_m7dp() {
    assert_f64_compiles(
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
fn test_f64_store_compiles_on_m7dp() {
    assert_f64_compiles(
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
// F64 CONVERSIONS — compiles on Cortex-M7DP (i32 ↔ f64, f32 → f64, bitcasts)
// ============================================================================

#[test]
fn test_f64_convert_i32_s_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::I32Const(42), WasmOp::F64ConvertI32S],
        "f64.convert_i32_s",
    );
}

#[test]
fn test_f64_convert_i32_u_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::I32Const(42), WasmOp::F64ConvertI32U],
        "f64.convert_i32_u",
    );
}

#[test]
fn test_f64_promote_f32_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F32Const(1.5), WasmOp::F64PromoteF32],
        "f64.promote_f32",
    );
}

#[test]
fn test_f64_reinterpret_i64_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::I64Const(0), WasmOp::F64ReinterpretI64],
        "f64.reinterpret_i64",
    );
}

#[test]
fn test_i64_reinterpret_f64_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.0), WasmOp::I64ReinterpretF64],
        "i64.reinterpret_f64",
    );
}

#[test]
fn test_i32_trunc_f64_s_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.7), WasmOp::I32TruncF64S],
        "i32.trunc_f64_s",
    );
}

#[test]
fn test_i32_trunc_f64_u_compiles_on_m7dp() {
    assert_f64_compiles(
        vec![WasmOp::F64Const(1.7), WasmOp::I32TruncF64U],
        "i32.trunc_f64_u",
    );
}

// ============================================================================
// F64 i64 conversions: deferred (require i64 register-pair lowering)
// ============================================================================

#[test]
fn test_f64_convert_i64_s_rejected_even_on_m7dp() {
    let mut selector = selector_with_dp_fpu();
    let result = selector.select(&[WasmOp::I64Const(42), WasmOp::F64ConvertI64S]);
    assert!(result.is_err());
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("i64"),
        "Error should mention i64 register pairs, got: {err}"
    );
}

#[test]
fn test_i64_trunc_f64_s_rejected_even_on_m7dp() {
    let mut selector = selector_with_dp_fpu();
    let result = selector.select(&[WasmOp::F64Const(1.7), WasmOp::I64TruncF64S]);
    assert!(result.is_err());
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("i64"),
        "Error should mention i64 register pairs, got: {err}"
    );
}

// ============================================================================
// F64 REJECTION ON CORTEX-M4F (single-precision FPU only)
// ============================================================================

#[test]
fn test_f64_add_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(2.0), WasmOp::F64Add],
        "f64.add",
    );
}

#[test]
fn test_f64_mul_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(
        vec![WasmOp::F64Const(2.0), WasmOp::F64Const(3.0), WasmOp::F64Mul],
        "f64.mul",
    );
}

#[test]
fn test_f64_eq_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Eq],
        "f64.eq",
    );
}

#[test]
fn test_f64_sqrt_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(vec![WasmOp::F64Const(4.0), WasmOp::F64Sqrt], "f64.sqrt");
}

#[test]
fn test_f64_load_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(
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
fn test_f64_const_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(vec![WasmOp::F64Const(3.125)], "f64.const");
}

#[test]
fn test_f64_promote_f32_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(
        vec![WasmOp::F32Const(1.5), WasmOp::F64PromoteF32],
        "f64.promote_f32",
    );
}

#[test]
fn test_f64_reinterpret_i64_rejected_on_m4f() {
    assert_f64_rejected_on_m4f(
        vec![WasmOp::I64Const(0), WasmOp::F64ReinterpretI64],
        "f64.reinterpret_i64",
    );
}

// ============================================================================
// F64 REJECTION ON CORTEX-M3 (no FPU)
// ============================================================================

#[test]
fn test_f64_add_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(
        vec![WasmOp::F64Const(1.5), WasmOp::F64Const(2.5), WasmOp::F64Add],
        "f64.add",
    );
}

#[test]
fn test_f64_sub_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(
        vec![WasmOp::F64Const(5.0), WasmOp::F64Const(2.0), WasmOp::F64Sub],
        "f64.sub",
    );
}

#[test]
fn test_f64_mul_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(
        vec![WasmOp::F64Const(2.5), WasmOp::F64Const(4.0), WasmOp::F64Mul],
        "f64.mul",
    );
}

#[test]
fn test_f64_div_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(
        vec![
            WasmOp::F64Const(10.0),
            WasmOp::F64Const(3.0),
            WasmOp::F64Div,
        ],
        "f64.div",
    );
}

#[test]
fn test_f64_eq_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(
        vec![WasmOp::F64Const(1.0), WasmOp::F64Const(1.0), WasmOp::F64Eq],
        "f64.eq",
    );
}

#[test]
fn test_f64_sqrt_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(vec![WasmOp::F64Const(4.0), WasmOp::F64Sqrt], "f64.sqrt");
}

#[test]
fn test_f64_const_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(vec![WasmOp::F64Const(3.125)], "f64.const");
}

#[test]
fn test_f64_load_rejected_no_fpu() {
    assert_f64_rejected_no_fpu(
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

// ============================================================================
// EDGE CASES (M7DP)
// ============================================================================

#[test]
fn test_f64_complex_expression_compiles_on_m7dp() {
    // (1.5 + 2.5) * 3.0
    assert_f64_compiles(
        vec![
            WasmOp::F64Const(1.5),
            WasmOp::F64Const(2.5),
            WasmOp::F64Add,
            WasmOp::F64Const(3.0),
            WasmOp::F64Mul,
        ],
        "f64 complex expr",
    );
}

#[test]
fn test_f64_round_trip_through_i64_bitcast_compiles_on_m7dp() {
    // f64 → i64 (reinterpret) → f64 (reinterpret)
    assert_f64_compiles(
        vec![
            WasmOp::F64Const(1.25),
            WasmOp::I64ReinterpretF64,
            WasmOp::F64ReinterpretI64,
        ],
        "f64 reinterpret round-trip",
    );
}

// ============================================================================
// END-TO-END: select_with_stack → validate → encode for an f64 function body
// ============================================================================

use synth_backend::ArmEncoder;
use synth_synthesis::validate_instructions;

#[test]
fn test_f64_function_body_lowers_to_valid_thumb_bytes_on_m7dp() {
    // A small f64 function: f(a) = sqrt(a*a + 1.0)
    // (omitting structured params — the stack selector requires param=0 to
    //  drive locals through the constant pool, which is enough to exercise
    //  the full pipeline: select_with_stack → validate → encode.)
    let wasm_ops = vec![
        WasmOp::F64Const(2.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Mul,
        WasmOp::F64Const(1.0),
        WasmOp::F64Add,
        WasmOp::F64Sqrt,
        WasmOp::End,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_target(Some(FPUPrecision::Double), "cortex-m7dp");

    let instrs = selector
        .select_with_stack(&wasm_ops, 0)
        .expect("select_with_stack should accept an f64 function body");

    // Validation gate — must accept on cortex-m7dp.
    validate_instructions(&instrs, Some(FPUPrecision::Double), "cortex-m7dp")
        .expect("validate_instructions should accept all F64 ops on m7dp");

    // Validation gate — must REJECT on a single-precision target.
    let sp_result = validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
    assert!(
        sp_result.is_err(),
        "validate_instructions should reject F64 ops on a single-precision target"
    );
    let err = sp_result.unwrap_err().to_string();
    assert!(
        err.contains("double-precision"),
        "Single-precision rejection should mention double-precision FPU, got: {err}"
    );

    // Encode every instruction — no panics, every op produces non-empty bytes
    // except labels.
    let enc = ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Double));
    let mut total = 0usize;
    for instr in &instrs {
        let bytes = enc.encode(&instr.op).expect("encoding must succeed");
        // Labels and other zero-byte ops are fine; just count.
        total += bytes.len();
    }
    assert!(
        total > 0,
        "Function body should encode to a non-empty byte stream"
    );
}

#[test]
fn test_f64_function_body_rejected_on_m4f_at_validate() {
    // Selection on cortex-m4f via `select_with_stack` will error out first,
    // before we even get to validate. Confirm that — there must be no silent
    // pass-through.
    let wasm_ops = vec![
        WasmOp::F64Const(1.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Add,
        WasmOp::End,
    ];
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    selector.set_target(Some(FPUPrecision::Single), "cortex-m4f");
    let result = selector.select_with_stack(&wasm_ops, 0);
    assert!(
        result.is_err(),
        "f64 function body should be rejected at selection on cortex-m4f"
    );
}
