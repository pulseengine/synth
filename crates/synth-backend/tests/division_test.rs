//! Division and Modulo Operations Test
//!
//! Tests hardware division support for ARM Cortex-M3/M4/M7

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmOp, InstructionSelector, Reg, RuleDatabase, WasmOp};

#[test]
fn test_signed_division() {
    // Test signed division
    let wasm_ops = vec![
        WasmOp::I32Const(100),
        WasmOp::I32Const(7),
        WasmOp::I32DivS, // 100 / 7 = 14 (signed)
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());

    // Should contain SDIV instruction
    let has_sdiv = arm_instrs
        .iter()
        .any(|i| matches!(i.op, ArmOp::Sdiv { .. }));
    assert!(has_sdiv, "Should generate SDIV instruction");
}

#[test]
fn test_unsigned_division() {
    // Test unsigned division
    let wasm_ops = vec![
        WasmOp::I32Const(100),
        WasmOp::I32Const(7),
        WasmOp::I32DivU, // 100 / 7 = 14 (unsigned)
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());

    // Should contain UDIV instruction
    let has_udiv = arm_instrs
        .iter()
        .any(|i| matches!(i.op, ArmOp::Udiv { .. }));
    assert!(has_udiv, "Should generate UDIV instruction");
}

#[test]
fn test_signed_remainder() {
    // Test signed remainder (modulo)
    let wasm_ops = vec![
        WasmOp::I32Const(100),
        WasmOp::I32Const(7),
        WasmOp::I32RemS, // 100 % 7 = 2 (signed)
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());
    // Remainder uses division (simplified for now)
}

#[test]
fn test_unsigned_remainder() {
    // Test unsigned remainder (modulo)
    let wasm_ops = vec![
        WasmOp::I32Const(100),
        WasmOp::I32Const(7),
        WasmOp::I32RemU, // 100 % 7 = 2 (unsigned)
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());
    // Remainder uses division (simplified for now)
}

#[test]
fn test_sdiv_encoding() {
    // Test SDIV encoding
    let encoder = ArmEncoder::new_arm32();

    let sdiv_op = ArmOp::Sdiv {
        rd: Reg::R0,
        rn: Reg::R1,
        rm: Reg::R2,
    };

    let code = encoder.encode(&sdiv_op).expect("Failed to encode");

    assert_eq!(code.len(), 4); // ARM32 is 4 bytes

    // Verify encoding: SDIV R0, R1, R2
    // Format: cond(E) | 0111 0001 | Rd(0) | 1111 | Rm(2) | 0001 | Rn(1)
    let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
    assert_eq!(instr, 0xE710F211, "SDIV R0, R1, R2 encoding");
}

#[test]
fn test_udiv_encoding() {
    // Test UDIV encoding
    let encoder = ArmEncoder::new_arm32();

    let udiv_op = ArmOp::Udiv {
        rd: Reg::R0,
        rn: Reg::R1,
        rm: Reg::R2,
    };

    let code = encoder.encode(&udiv_op).expect("Failed to encode");

    assert_eq!(code.len(), 4); // ARM32 is 4 bytes

    // Verify encoding: UDIV R0, R1, R2
    // Format: cond(E) | 0111 0011 | Rd(0) | 1111 | Rm(2) | 0001 | Rn(1)
    let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
    assert_eq!(instr, 0xE730F211, "UDIV R0, R1, R2 encoding");
}

#[test]
fn test_mls_encoding() {
    // Test MLS (multiply and subtract) encoding
    let encoder = ArmEncoder::new_arm32();

    let mls_op = ArmOp::Mls {
        rd: Reg::R0,
        rn: Reg::R1,
        rm: Reg::R2,
        ra: Reg::R3,
    };

    let code = encoder.encode(&mls_op).expect("Failed to encode");

    assert_eq!(code.len(), 4); // ARM32 is 4 bytes

    // Verify it's a valid instruction
    let instr = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
    assert_ne!(instr, 0);
}

#[test]
fn test_division_by_constant() {
    // Test division by constant (could be optimized to shift if power of 2)
    let wasm_ops = vec![
        WasmOp::I32Const(1000),
        WasmOp::I32Const(8), // Power of 2
        WasmOp::I32DivU,     // Could be optimized to shift right by 3
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    assert!(!arm_instrs.is_empty());
}

#[test]
fn test_division_embedded_use_case() {
    // Realistic embedded use case: calculate average
    // average = (a + b + c + d) / 4
    let wasm_ops = vec![
        WasmOp::I32Const(10),
        WasmOp::I32Const(20),
        WasmOp::I32Add,
        WasmOp::I32Const(30),
        WasmOp::I32Add,
        WasmOp::I32Const(40),
        WasmOp::I32Add, // Sum = 100
        WasmOp::I32Const(4),
        WasmOp::I32DivU, // Average = 25
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
fn test_modulo_embedded_use_case() {
    // Realistic embedded use case: circular buffer index wrapping
    // next_index = (current_index + 1) % buffer_size
    let wasm_ops = vec![
        WasmOp::I32Const(15), // current index
        WasmOp::I32Const(1),
        WasmOp::I32Add,       // increment
        WasmOp::I32Const(16), // buffer size
        WasmOp::I32RemU,      // wrap around
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    let encoder = ArmEncoder::new_arm32();
    let ops: Vec<_> = arm_instrs.iter().map(|i| i.op.clone()).collect();
    let code = encoder.encode_sequence(&ops).expect("Failed to encode");

    assert!(!code.is_empty());
    assert_eq!(code.len() % 4, 0);
}

#[test]
fn test_negative_division() {
    // Test signed division with negative numbers
    let wasm_ops = vec![
        WasmOp::I32Const(-100),
        WasmOp::I32Const(7),
        WasmOp::I32DivS, // -100 / 7 = -14 (signed)
    ];

    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let arm_instrs = selector.select(&wasm_ops).expect("Failed to select");

    // Should use SDIV for signed division
    let has_sdiv = arm_instrs
        .iter()
        .any(|i| matches!(i.op, ArmOp::Sdiv { .. }));
    assert!(has_sdiv);
}
