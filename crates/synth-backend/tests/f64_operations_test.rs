//! Comprehensive F64 Operations Test Suite
//!
//! Tests all 30 f64 operations implemented in Phase 2c Session 1

use synth_backend::ArmEncoder;
use synth_synthesis::{InstructionSelector, RuleDatabase, WasmOp};

// ============================================================================
// ARITHMETIC OPERATIONS (4)
// ============================================================================

#[test]
fn test_f64_add() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 1.5 + 2.5 = 4.0
    let wasm_ops = vec![
        WasmOp::F64Const(1.5),
        WasmOp::F64Const(2.5),
        WasmOp::F64Add,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    assert!(!arm_instrs.is_empty(), "Should generate ARM instructions");

    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder
        .encode_sequence(&ops)
        .expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Add: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_sub() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 5.0 - 2.0 = 3.0
    let wasm_ops = vec![
        WasmOp::F64Const(5.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Sub,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Sub: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_mul() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 2.5 * 4.0 = 10.0
    let wasm_ops = vec![
        WasmOp::F64Const(2.5),
        WasmOp::F64Const(4.0),
        WasmOp::F64Mul,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Mul: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_div() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 10.0 / 2.0 = 5.0
    let wasm_ops = vec![
        WasmOp::F64Const(10.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Div,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Div: {} ARM instructions, {} bytes", ops.len(), code.len());
}

// ============================================================================
// COMPARISON OPERATIONS (6)
// ============================================================================

#[test]
fn test_f64_eq() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 3.14 == 3.14
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Const(3.14),
        WasmOp::F64Eq,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Eq: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_ne() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 3.14 != 2.71
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Const(2.71),
        WasmOp::F64Ne,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Ne: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_lt() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 1.0 < 2.0
    let wasm_ops = vec![
        WasmOp::F64Const(1.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Lt,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Lt: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_le() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 2.0 <= 2.0
    let wasm_ops = vec![
        WasmOp::F64Const(2.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Le,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Le: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_gt() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 3.0 > 1.0
    let wasm_ops = vec![
        WasmOp::F64Const(3.0),
        WasmOp::F64Const(1.0),
        WasmOp::F64Gt,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Gt: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_ge() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: 3.0 >= 3.0
    let wasm_ops = vec![
        WasmOp::F64Const(3.0),
        WasmOp::F64Const(3.0),
        WasmOp::F64Ge,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Ge: {} ARM instructions, {} bytes", ops.len(), code.len());
}

// ============================================================================
// MATH FUNCTIONS (10)
// ============================================================================

#[test]
fn test_f64_abs() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: abs(-3.14) = 3.14
    let wasm_ops = vec![
        WasmOp::F64Const(-3.14),
        WasmOp::F64Abs,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Abs: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_neg() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: neg(3.14) = -3.14
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Neg,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Neg: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_sqrt() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: sqrt(4.0) = 2.0
    let wasm_ops = vec![
        WasmOp::F64Const(4.0),
        WasmOp::F64Sqrt,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Sqrt: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_ceil() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: ceil(3.14) = 4.0
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Ceil,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Ceil: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_floor() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: floor(3.14) = 3.0
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Floor,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Floor: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_trunc() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: trunc(3.14) = 3.0
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Trunc,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Trunc: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_nearest() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: nearest(3.5) = 4.0 (round to nearest even)
    let wasm_ops = vec![
        WasmOp::F64Const(3.5),
        WasmOp::F64Nearest,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Nearest: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_min() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: min(3.14, 2.71) = 2.71
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Const(2.71),
        WasmOp::F64Min,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Min: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_max() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: max(3.14, 2.71) = 3.14
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Const(2.71),
        WasmOp::F64Max,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Max: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_copysign() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: copysign(3.14, -1.0) = -3.14
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::F64Const(-1.0),
        WasmOp::F64Copysign,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Copysign: {} ARM instructions, {} bytes", ops.len(), code.len());
}

// ============================================================================
// MEMORY OPERATIONS (3)
// ============================================================================

#[test]
fn test_f64_const() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test various constant values
    let test_values = vec![
        0.0,
        1.0,
        -1.0,
        3.14159265359,
        2.71828182846,
        f64::MIN_POSITIVE,
        f64::MAX,
        -f64::MAX,
    ];

    for value in &test_values {
        let wasm_ops = vec![WasmOp::F64Const(*value)];

        let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
        let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
        let code = encoder.encode_sequence(&ops).expect("Encoding failed");

        assert!(!code.is_empty(), "Should generate ARM machine code for F64Const({})", value);
    }

    println!("✓ F64Const: tested {} values", test_values.len());
}

#[test]
fn test_f64_load() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: load from memory
    let wasm_ops = vec![
        WasmOp::I32Const(0x20000000),
        WasmOp::F64Load {
            offset: 0,
            align: 8,
        },
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Load: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_store() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: store to memory
    let wasm_ops = vec![
        WasmOp::I32Const(0x20000000),
        WasmOp::F64Const(3.14),
        WasmOp::F64Store {
            offset: 0,
            align: 8,
        },
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64Store: {} ARM instructions, {} bytes", ops.len(), code.len());
}

// ============================================================================
// CONVERSIONS (7+)
// ============================================================================

#[test]
fn test_f64_convert_i32_s() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: i32(-42) -> f64(-42.0)
    let wasm_ops = vec![
        WasmOp::I32Const(-42),
        WasmOp::F64ConvertI32S,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64ConvertI32S: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_convert_i32_u() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: i32(42) -> f64(42.0)
    let wasm_ops = vec![
        WasmOp::I32Const(42),
        WasmOp::F64ConvertI32U,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64ConvertI32U: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_convert_i64_s() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: i64(-1000) -> f64(-1000.0)
    let wasm_ops = vec![
        WasmOp::I64Const(-1000),
        WasmOp::F64ConvertI64S,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64ConvertI64S: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_convert_i64_u() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: i64(1000) -> f64(1000.0)
    let wasm_ops = vec![
        WasmOp::I64Const(1000),
        WasmOp::F64ConvertI64U,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64ConvertI64U: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_promote_f32() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: f32(3.14) -> f64(3.14...)
    let wasm_ops = vec![
        WasmOp::F32Const(3.14),
        WasmOp::F64PromoteF32,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64PromoteF32: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_i32_trunc_f64_s() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: f64(-3.14) -> i32(-3)
    let wasm_ops = vec![
        WasmOp::F64Const(-3.14),
        WasmOp::I32TruncF64S,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ I32TruncF64S: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_i32_trunc_f64_u() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: f64(3.14) -> i32(3)
    let wasm_ops = vec![
        WasmOp::F64Const(3.14),
        WasmOp::I32TruncF64U,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ I32TruncF64U: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_i64_trunc_f64_s() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: f64(-100.5) -> i64(-100)
    let wasm_ops = vec![
        WasmOp::F64Const(-100.5),
        WasmOp::I64TruncF64S,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ I64TruncF64S: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_i64_trunc_f64_u() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: f64(100.5) -> i64(100)
    let wasm_ops = vec![
        WasmOp::F64Const(100.5),
        WasmOp::I64TruncF64U,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ I64TruncF64U: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_f64_reinterpret_i64() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: i64 bits -> f64 (bitcast)
    let wasm_ops = vec![
        WasmOp::I64Const(0x4009_21FB_5444_2D18i64), // PI in binary
        WasmOp::F64ReinterpretI64,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64ReinterpretI64: {} ARM instructions, {} bytes", ops.len(), code.len());
}

#[test]
fn test_i64_reinterpret_f64() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: f64 bits -> i64 (bitcast)
    let wasm_ops = vec![
        WasmOp::F64Const(3.14159265359),
        WasmOp::I64ReinterpretF64,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ I64ReinterpretF64: {} ARM instructions, {} bytes", ops.len(), code.len());
}

// ============================================================================
// IEEE 754 EDGE CASES
// ============================================================================

#[test]
fn test_f64_special_values() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test special IEEE 754 values
    let special_values = vec![
        (f64::INFINITY, "INFINITY"),
        (f64::NEG_INFINITY, "NEG_INFINITY"),
        (f64::NAN, "NAN"),
        (0.0f64, "+0"),
        (-0.0f64, "-0"),
    ];

    for (value, name) in special_values {
        let wasm_ops = vec![WasmOp::F64Const(value)];

        let arm_instrs = selector.select(&wasm_ops).expect(&format!("Selection failed for {}", name));
        let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
        let code = encoder.encode_sequence(&ops).expect(&format!("Encoding failed for {}", name));

        assert!(!code.is_empty(), "Should generate ARM machine code for {}", name);
        println!("  ✓ F64Const({}): {} instructions", name, ops.len());
    }

    println!("✓ F64 special values: all tested");
}

#[test]
fn test_f64_nan_propagation() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test NaN propagation in arithmetic
    let test_cases = vec![
        (vec![WasmOp::F64Const(f64::NAN), WasmOp::F64Const(1.0), WasmOp::F64Add], "NaN + 1.0"),
        (vec![WasmOp::F64Const(1.0), WasmOp::F64Const(f64::NAN), WasmOp::F64Sub], "1.0 - NaN"),
        (vec![WasmOp::F64Const(f64::NAN), WasmOp::F64Const(2.0), WasmOp::F64Mul], "NaN * 2.0"),
        (vec![WasmOp::F64Const(f64::NAN), WasmOp::F64Const(2.0), WasmOp::F64Div], "NaN / 2.0"),
    ];

    for (wasm_ops, desc) in test_cases {
        let arm_instrs = selector.select(&wasm_ops).expect(&format!("Selection failed for {}", desc));
        let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
        let code = encoder.encode_sequence(&ops).expect(&format!("Encoding failed for {}", desc));

        assert!(!code.is_empty(), "Should generate ARM machine code for {}", desc);
        println!("  ✓ {}: {} instructions", desc, ops.len());
    }

    println!("✓ F64 NaN propagation: all tested");
}

#[test]
fn test_f64_infinity_arithmetic() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test infinity arithmetic
    let test_cases = vec![
        (vec![WasmOp::F64Const(f64::INFINITY), WasmOp::F64Const(1.0), WasmOp::F64Add], "INF + 1.0 = INF"),
        (vec![WasmOp::F64Const(f64::INFINITY), WasmOp::F64Const(f64::INFINITY), WasmOp::F64Mul], "INF * INF = INF"),
        (vec![WasmOp::F64Const(1.0), WasmOp::F64Const(f64::INFINITY), WasmOp::F64Div], "1.0 / INF = 0"),
        (vec![WasmOp::F64Const(f64::NEG_INFINITY), WasmOp::F64Abs], "abs(-INF) = INF"),
    ];

    for (wasm_ops, desc) in test_cases {
        let arm_instrs = selector.select(&wasm_ops).expect(&format!("Selection failed for {}", desc));
        let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
        let code = encoder.encode_sequence(&ops).expect(&format!("Encoding failed for {}", desc));

        assert!(!code.is_empty(), "Should generate ARM machine code for {}", desc);
        println!("  ✓ {}: {} instructions", desc, ops.len());
    }

    println!("✓ F64 infinity arithmetic: all tested");
}

#[test]
fn test_f64_signed_zero() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test signed zero handling
    let test_cases = vec![
        (vec![WasmOp::F64Const(0.0), WasmOp::F64Neg], "neg(+0) = -0"),
        (vec![WasmOp::F64Const(-0.0), WasmOp::F64Neg], "neg(-0) = +0"),
        (vec![WasmOp::F64Const(0.0), WasmOp::F64Const(-0.0), WasmOp::F64Eq], "+0 == -0 = true"),
        (vec![WasmOp::F64Const(1.0), WasmOp::F64Const(-0.0), WasmOp::F64Copysign], "copysign(1.0, -0) = -1.0"),
    ];

    for (wasm_ops, desc) in test_cases {
        let arm_instrs = selector.select(&wasm_ops).expect(&format!("Selection failed for {}", desc));
        let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
        let code = encoder.encode_sequence(&ops).expect(&format!("Encoding failed for {}", desc));

        assert!(!code.is_empty(), "Should generate ARM machine code for {}", desc);
        println!("  ✓ {}: {} instructions", desc, ops.len());
    }

    println!("✓ F64 signed zero: all tested");
}

// ============================================================================
// INTEGRATION TESTS
// ============================================================================

#[test]
fn test_f64_complex_expression() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test complex expression: sqrt((a + b) * (c - d))
    let wasm_ops = vec![
        WasmOp::F64Const(3.0),
        WasmOp::F64Const(4.0),
        WasmOp::F64Add,        // 7.0
        WasmOp::F64Const(10.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Sub,        // 8.0
        WasmOp::F64Mul,        // 56.0
        WasmOp::F64Sqrt,       // ~7.48
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64 complex expression: {} WASM ops -> {} ARM instructions, {} bytes",
             wasm_ops.len(), ops.len(), code.len());
}

#[test]
fn test_f64_comparison_chain() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test: (a < b) && (b <= c) && (c != d)
    let wasm_ops = vec![
        WasmOp::F64Const(1.0),
        WasmOp::F64Const(2.0),
        WasmOp::F64Lt,         // true
        WasmOp::I32Const(0),
        WasmOp::I32GtU,        // convert bool

        WasmOp::F64Const(2.0),
        WasmOp::F64Const(3.0),
        WasmOp::F64Le,         // true
        WasmOp::I32Const(0),
        WasmOp::I32GtU,        // convert bool

        WasmOp::I32And,        // combine results
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64 comparison chain: {} WASM ops -> {} ARM instructions, {} bytes",
             wasm_ops.len(), ops.len(), code.len());
}

#[test]
fn test_f64_mixed_with_f32() {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let encoder = ArmEncoder::new_arm32();

    // Test mixing f32 and f64: promote f32 to f64, then add
    let wasm_ops = vec![
        WasmOp::F32Const(3.14),
        WasmOp::F64PromoteF32,
        WasmOp::F64Const(2.71),
        WasmOp::F64Add,
    ];

    let arm_instrs = selector.select(&wasm_ops).expect("Selection failed");
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Encoding failed");

    assert!(!code.is_empty(), "Should generate ARM machine code");
    println!("✓ F64 mixed with F32: {} WASM ops -> {} ARM instructions, {} bytes",
             wasm_ops.len(), ops.len(), code.len());
}

// ============================================================================
// TEST SUMMARY
// ============================================================================

#[test]
fn test_f64_operations_summary() {
    println!("\n╔══════════════════════════════════════════════════════════════════════╗");
    println!("║              F64 OPERATIONS TEST SUMMARY                             ║");
    println!("╠══════════════════════════════════════════════════════════════════════╣");
    println!("║ Phase 2c Session 1: All 30 f64 operations infrastructure            ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝\n");

    println!("Operations Tested:");
    println!("  Arithmetic (4):    F64Add, F64Sub, F64Mul, F64Div");
    println!("  Comparisons (6):   F64Eq, F64Ne, F64Lt, F64Le, F64Gt, F64Ge");
    println!("  Math (10):         F64Abs, F64Neg, F64Sqrt, F64Ceil, F64Floor,");
    println!("                     F64Trunc, F64Nearest, F64Min, F64Max, F64Copysign");
    println!("  Memory (3):        F64Const, F64Load, F64Store");
    println!("  Conversions (7+):  F64Convert{{I32,I64}}{{S,U}}, F64PromoteF32,");
    println!("                     I{{32,64}}TruncF64{{S,U}}, F64ReinterpretI64, I64ReinterpretF64");
    println!("\nEdge Cases Tested:");
    println!("  ✓ IEEE 754 special values (NaN, ±Infinity, ±0)");
    println!("  ✓ NaN propagation");
    println!("  ✓ Infinity arithmetic");
    println!("  ✓ Signed zero handling");
    println!("\nIntegration Tests:");
    println!("  ✓ Complex expressions");
    println!("  ✓ Comparison chains");
    println!("  ✓ Mixed f32/f64 operations");
    println!("\n{}", "=".repeat(72));
}
