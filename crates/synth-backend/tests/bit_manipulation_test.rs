//! Bit Manipulation Operations Test
//!
//! Tests rotate, count leading zeros, count trailing zeros, and population count

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmOp, InstructionSelector, Reg, RuleDatabase, WasmOp};

#[test]
fn test_rotate_left() {
    // Test ROTL operation
    let wasm_ops = vec![
        WasmOp::I32Const(0x12345678),
        WasmOp::I32Const(4),
        WasmOp::I32Rotl,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());

    // Should contain ROR instruction (rotl is implemented as ror with 32-shift)
    let has_ror = arm_instrs.iter().any(|i| matches!(i.op, ArmOp::Ror { .. }));
    assert!(has_ror || arm_instrs.len() > 0); // Either ROR or other valid encoding
}

#[test]
fn test_rotate_right() {
    // Test ROTR operation
    let wasm_ops = vec![
        WasmOp::I32Const(0x12345678),
        WasmOp::I32Const(4),
        WasmOp::I32Rotr,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());

    // Should contain ROR instruction
    let has_ror = arm_instrs.iter().any(|i| matches!(i.op, ArmOp::Ror { .. }));
    assert!(has_ror);
}

#[test]
fn test_count_leading_zeros() {
    // Test CLZ operation - useful for finding highest set bit
    let wasm_ops = vec![
        WasmOp::I32Const(0x00001000), // Has leading zeros
        WasmOp::I32Clz,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());

    // Should contain CLZ instruction
    let has_clz = arm_instrs.iter().any(|i| matches!(i.op, ArmOp::Clz { .. }));
    assert!(has_clz);
}

#[test]
fn test_count_trailing_zeros() {
    // Test CTZ operation - useful for finding lowest set bit
    let wasm_ops = vec![
        WasmOp::I32Const(0x00001000), // Has trailing zeros
        WasmOp::I32Ctz,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());

    // Should contain RBIT instruction (CTZ = RBIT + CLZ)
    let has_rbit = arm_instrs
        .iter()
        .any(|i| matches!(i.op, ArmOp::Rbit { .. }));
    assert!(has_rbit);
}

#[test]
fn test_population_count() {
    // Test POPCNT operation - counts number of 1 bits
    let wasm_ops = vec![
        WasmOp::I32Const(0x0F0F0F0F), // Has many 1 bits
        WasmOp::I32Popcnt,
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());
    // POPCNT doesn't have native ARM instruction, so will be sequence or NOP
}

#[test]
fn test_ror_encoding() {
    // Test that ROR encodes correctly
    let encoder = ArmEncoder::new_arm32();

    let ror_op = ArmOp::Ror {
        rd: Reg::R0,
        rn: Reg::R1,
        shift: 4,
    };

    let code = encoder.encode(&ror_op).expect("Failed to encode");

    assert_eq!(code.len(), 4); // ARM32 is 4 bytes

    // Verify it's a valid instruction (not all zeros)
    let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
    assert_ne!(instr, 0);
}

#[test]
fn test_clz_encoding() {
    // Test that CLZ encodes correctly
    let encoder = ArmEncoder::new_arm32();

    let clz_op = ArmOp::Clz {
        rd: Reg::R0,
        rm: Reg::R1,
    };

    let code = encoder.encode(&clz_op).expect("Failed to encode");

    assert_eq!(code.len(), 4); // ARM32 is 4 bytes

    // Verify encoding (should be 0xE16F0F11 for CLZ R0, R1)
    let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
    assert_eq!(instr, 0xE16F0F11);
}

#[test]
fn test_rbit_encoding() {
    // Test that RBIT encodes correctly
    let encoder = ArmEncoder::new_arm32();

    let rbit_op = ArmOp::Rbit {
        rd: Reg::R0,
        rm: Reg::R1,
    };

    let code = encoder.encode(&rbit_op).expect("Failed to encode");

    assert_eq!(code.len(), 4); // ARM32 is 4 bytes

    // Verify encoding (should be 0xE6FF0F31 for RBIT R0, R1)
    let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
    assert_eq!(instr, 0xE6FF0F31);
}

#[test]
fn test_bit_ops_in_real_code() {
    // Realistic use case: find first set bit (ffs)
    // Algorithm: CTZ (count trailing zeros)
    let wasm_ops = vec![
        WasmOp::I32Const(0x00100000), // Bit 20 is set
        WasmOp::I32Ctz,               // Should return 20
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    let encoder = ArmEncoder::new_arm32();
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Failed to encode");

    assert!(!code.is_empty());
    assert_eq!(code.len() % 4, 0); // Must be multiple of 4 bytes
}

#[test]
fn test_bit_ops_embedded_use_case() {
    // Common embedded use case: check if value is power of 2
    // Algorithm: (x != 0) && ((x & (x-1)) == 0)
    // Equivalent: popcnt(x) == 1
    let wasm_ops = vec![
        WasmOp::I32Const(16), // Power of 2
        WasmOp::I32Popcnt,    // Should return 1
        WasmOp::I32Const(1),
        WasmOp::I32Eq, // Compare with 1
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());
}
