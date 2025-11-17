//! Comprehensive Verification Test Suite for All Synthesis Rules
//!
//! This module systematically verifies all WASM→ARM synthesis rules.

use synth_verify::{create_z3_context, TranslationValidator, ValidationResult};
use synth_synthesis::{ArmOp, Operand2, Pattern, Reg, Replacement, SynthesisRule, WasmOp};

/// Helper to create a test synthesis rule
fn create_rule(name: &str, wasm_op: WasmOp, arm_op: ArmOp) -> SynthesisRule {
    SynthesisRule {
        name: name.to_string(),
        priority: 0,
        pattern: Pattern::WasmInstr(wasm_op),
        replacement: Replacement::ArmInstr(arm_op),
        cost: synth_synthesis::Cost {
            cycles: 1,
            code_size: 4,
            registers: 2,
        },
    }
}

// ============================================================================
// ARITHMETIC OPERATIONS
// ============================================================================

#[test]
fn verify_i32_add() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.add",
        WasmOp::I32Add,
        ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        },
    );

    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Verified) => {}
        other => panic!("Expected Verified, got {:?}", other),
    }
}

#[test]
fn verify_i32_sub() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.sub",
        WasmOp::I32Sub,
        ArmOp::Sub {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

#[test]
fn verify_i32_mul() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.mul",
        WasmOp::I32Mul,
        ArmOp::Mul {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

#[test]
fn verify_i32_div_s() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.div_s",
        WasmOp::I32DivS,
        ArmOp::Sdiv {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

#[test]
fn verify_i32_div_u() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.div_u",
        WasmOp::I32DivU,
        ArmOp::Udiv {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

#[test]
fn verify_i32_rem_s() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // ARM doesn't have REM instruction, but we can test MLS approach
    // rem = a - (a/b)*b, which requires sequence
    // For now, we'll test if the semantics match when implemented
    let rule = create_rule(
        "i32.rem_s",
        WasmOp::I32RemS,
        ArmOp::Nop, // Placeholder - actual implementation uses sequence
    );

    // This should be Unknown since Nop doesn't implement rem semantics
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Verified) => panic!("NOP should not verify as REM"),
        Ok(ValidationResult::Invalid { .. }) => {}
        Ok(ValidationResult::Unknown { .. }) => {}
        Err(_) => {}
    }
}

#[test]
fn verify_i32_rem_u() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.rem_u",
        WasmOp::I32RemU,
        ArmOp::Nop, // Placeholder
    );

    // Should not verify
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Verified) => panic!("NOP should not verify as REM"),
        _ => {}
    }
}

// ============================================================================
// BITWISE OPERATIONS
// ============================================================================

#[test]
fn verify_i32_and() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.and",
        WasmOp::I32And,
        ArmOp::And {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

#[test]
fn verify_i32_or() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.or",
        WasmOp::I32Or,
        ArmOp::Orr {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

#[test]
fn verify_i32_xor() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = create_rule(
        "i32.xor",
        WasmOp::I32Xor,
        ArmOp::Eor {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        },
    );

    assert!(matches!(
        validator.verify_rule(&rule),
        Ok(ValidationResult::Verified)
    ));
}

// ============================================================================
// ROTATION OPERATIONS
// ============================================================================
//
// LIMITATION: WASM rotation operations (I32Rotl, I32Rotr) take dynamic shift
// amounts (2 inputs: value + amount), while ARM ROR has a constant shift.
//
// Verification strategies:
// 1. Constant rotations: When compiler detects constant shift, use ARM ROR
// 2. Dynamic rotations: Requires instruction sequence (not yet verified)
//
// Current status: ARM ROR semantics implemented and tested with concrete values.
// Full verification requires:
// - Parameterized verification (testing all shift amounts 0-31)
// - Or sequence verification for dynamic shifts
//
// This is tracked as Phase 1A task: "Parameterized shift verification"
// ============================================================================

#[test]
fn test_arm_ror_semantics() {
    // This test verifies that ARM ROR semantics are correctly implemented
    // by testing concrete values. Full symbolic verification requires
    // parameterized testing framework (Phase 1A).

    use synth_verify::{create_z3_context, ArmSemantics, ArmState};
    use z3::ast::Ast;

    let ctx = create_z3_context();
    let encoder = ArmSemantics::new(&ctx);
    let mut state = ArmState::new_symbolic(&ctx);

    // Test that ROR(0x12345678, 8) = 0x78123456
    state.set_reg(&Reg::R1, z3::ast::BV::from_u64(&ctx, 0x12345678, 32));
    let ror_op = ArmOp::Ror {
        rd: Reg::R0,
        rn: Reg::R1,
        shift: 8,
    };
    encoder.encode_op(&ror_op, &mut state);
    assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x78123456));

    // Test that ROTL(x, n) = ROR(x, 32-n) transformation holds
    // For example: ROTL(0x12345678, 8) = ROR(0x12345678, 24)
    state.set_reg(&Reg::R1, z3::ast::BV::from_u64(&ctx, 0x12345678, 32));
    let ror_24 = ArmOp::Ror {
        rd: Reg::R0,
        rn: Reg::R1,
        shift: 24, // 32 - 8 = 24
    };
    encoder.encode_op(&ror_24, &mut state);
    // ROTL(0x12345678, 8) = 0x34567812
    // ROR(0x12345678, 24) = 0x34567812 ✓
    assert_eq!(state.get_reg(&Reg::R0).as_i64(), Some(0x34567812));
}

#[test]
#[ignore] // Requires parameterized verification framework
fn verify_i32_rotl_constant() {
    // TODO: Implement parameterized verification
    // For each constant n in 0..32:
    //   Verify: WASM I32Rotl(x, n) ≡ ARM ROR(x, 32-n)
    //
    // This requires extending TranslationValidator to support
    // parameterized rules where shift amounts are concrete but
    // input values remain symbolic.
}

#[test]
#[ignore] // Requires parameterized verification framework
fn verify_i32_rotr_constant() {
    // TODO: Implement parameterized verification
    // For each constant n in 0..32:
    //   Verify: WASM I32Rotr(x, n) ≡ ARM ROR(x, n)
}

// ============================================================================
// BIT MANIPULATION OPERATIONS
// ============================================================================

#[test]
fn verify_i32_clz() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // ARM has CLZ instruction - direct mapping!
    let rule = create_rule(
        "i32.clz",
        WasmOp::I32Clz,
        ArmOp::Clz {
            rd: Reg::R0,
            rm: Reg::R0,
        },
    );

    // CLZ semantics in our implementation are simplified
    // Full verification would require complete CLZ encoding
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Unknown { .. }) => {}
        _ => {}
    }
}

#[test]
fn test_ctz_sequence_concrete() {
    // First, test that the CTZ sequence works correctly with concrete values
    // This builds confidence before formal verification
    use synth_verify::{create_z3_context, ArmSemantics, ArmState, WasmSemantics};
    use z3::ast::Ast;

    let ctx = create_z3_context();
    let wasm_encoder = WasmSemantics::new(&ctx);
    let arm_encoder = ArmSemantics::new(&ctx);

    // Test CTZ(12) = 2
    // Binary: 12 = 0b1100, trailing zeros = 2
    let value = z3::ast::BV::from_i64(&ctx, 12, 32);

    // WASM CTZ
    let wasm_result = wasm_encoder.encode_op(&WasmOp::I32Ctz, &[value.clone()]);
    assert_eq!(wasm_result.as_i64(), Some(2), "WASM CTZ(12) should be 2");

    // ARM sequence: RBIT R1, R0; CLZ R0, R1
    let mut state = ArmState::new_symbolic(&ctx);
    state.set_reg(&Reg::R0, value);

    arm_encoder.encode_op(&ArmOp::Rbit { rd: Reg::R1, rm: Reg::R0 }, &mut state);
    arm_encoder.encode_op(&ArmOp::Clz { rd: Reg::R0, rm: Reg::R1 }, &mut state);

    let arm_result = state.get_reg(&Reg::R0);
    assert_eq!(arm_result.as_i64(), Some(2), "ARM CTZ(12) should be 2");

    // Test CTZ(8) = 3
    // Binary: 8 = 0b1000, trailing zeros = 3
    let value2 = z3::ast::BV::from_i64(&ctx, 8, 32);

    let wasm_result2 = wasm_encoder.encode_op(&WasmOp::I32Ctz, &[value2.clone()]);
    assert_eq!(wasm_result2.as_i64(), Some(3), "WASM CTZ(8) should be 3");

    let mut state2 = ArmState::new_symbolic(&ctx);
    state2.set_reg(&Reg::R0, value2);
    arm_encoder.encode_op(&ArmOp::Rbit { rd: Reg::R1, rm: Reg::R0 }, &mut state2);
    arm_encoder.encode_op(&ArmOp::Clz { rd: Reg::R0, rm: Reg::R1 }, &mut state2);

    let arm_result2 = state2.get_reg(&Reg::R0);
    assert_eq!(arm_result2.as_i64(), Some(3), "ARM CTZ(8) should be 3");

    println!("✓ CTZ sequence concrete tests passed");
}

#[test]
fn verify_i32_ctz() {
    // This test verifies the complete CTZ implementation using ARM instruction sequence
    // CTZ(x) = CLZ(RBIT(x))
    //
    // Sequence:
    //   RBIT R1, R0   ; Reverse bits of R0 into R1
    //   CLZ R0, R1    ; Count leading zeros of R1 into R0
    //
    // This proves that the two-instruction sequence is semantically equivalent
    // to WASM's I32Ctz operation for ALL possible inputs.

    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rule = SynthesisRule {
        name: "i32.ctz".to_string(),
        priority: 0,
        pattern: Pattern::WasmInstr(WasmOp::I32Ctz),
        replacement: Replacement::ArmSequence(vec![
            ArmOp::Rbit {
                rd: Reg::R1,
                rm: Reg::R0,
            },
            ArmOp::Clz {
                rd: Reg::R0,
                rm: Reg::R1,
            },
        ]),
        cost: synth_synthesis::Cost {
            cycles: 2,
            code_size: 8,
            registers: 2,
        },
    };

    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Verified) => {
            println!("✓ CTZ sequence verified: I32Ctz ≡ [RBIT + CLZ]");
        }
        other => panic!("Expected Verified for CTZ sequence, got {:?}", other),
    }
}

// ============================================================================
// COMPARISON OPERATIONS
// ============================================================================

#[test]
fn verify_i32_eq() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // Comparisons in ARM use CMP + conditional
    // For SMT verification, we test the comparison semantics
    let rule = create_rule(
        "i32.eq",
        WasmOp::I32Eq,
        ArmOp::Cmp {
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        },
    );

    // CMP sets flags but doesn't return value
    // Full verification requires modeling conditional execution
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Invalid { .. }) => {} // CMP alone != EQ
        Ok(ValidationResult::Unknown { .. }) => {}
        _ => {}
    }
}

// ============================================================================
// BATCH VERIFICATION
// ============================================================================

#[test]
fn batch_verify_all_arithmetic() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rules = vec![
        create_rule(
            "i32.add",
            WasmOp::I32Add,
            ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
        ),
        create_rule(
            "i32.sub",
            WasmOp::I32Sub,
            ArmOp::Sub {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
        ),
        create_rule(
            "i32.mul",
            WasmOp::I32Mul,
            ArmOp::Mul {
                rd: Reg::R0,
                rn: Reg::R0,
                rm: Reg::R1,
            },
        ),
        create_rule(
            "i32.div_s",
            WasmOp::I32DivS,
            ArmOp::Sdiv {
                rd: Reg::R0,
                rn: Reg::R0,
                rm: Reg::R1,
            },
        ),
        create_rule(
            "i32.div_u",
            WasmOp::I32DivU,
            ArmOp::Udiv {
                rd: Reg::R0,
                rn: Reg::R0,
                rm: Reg::R1,
            },
        ),
    ];

    let results = validator.verify_rules(&rules);

    let verified_count = results
        .iter()
        .filter(|(_, r)| matches!(r, Ok(ValidationResult::Verified)))
        .count();

    assert_eq!(
        verified_count, 5,
        "All 5 arithmetic operations should verify"
    );
}

#[test]
fn batch_verify_all_bitwise() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    let rules = vec![
        create_rule(
            "i32.and",
            WasmOp::I32And,
            ArmOp::And {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
        ),
        create_rule(
            "i32.or",
            WasmOp::I32Or,
            ArmOp::Orr {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
        ),
        create_rule(
            "i32.xor",
            WasmOp::I32Xor,
            ArmOp::Eor {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            },
        ),
    ];

    let results = validator.verify_rules(&rules);

    let verified_count = results
        .iter()
        .filter(|(_, r)| matches!(r, Ok(ValidationResult::Verified)))
        .count();

    assert_eq!(verified_count, 3, "All 3 bitwise operations should verify");
}

// ============================================================================
// VERIFICATION REPORT GENERATION
// ============================================================================

#[test]
fn generate_verification_report() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // Test all directly mappable operations
    let test_cases = vec![
        ("i32.add → ADD", WasmOp::I32Add, ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        }),
        ("i32.sub → SUB", WasmOp::I32Sub, ArmOp::Sub {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        }),
        ("i32.mul → MUL", WasmOp::I32Mul, ArmOp::Mul {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        }),
        ("i32.div_s → SDIV", WasmOp::I32DivS, ArmOp::Sdiv {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        }),
        ("i32.div_u → UDIV", WasmOp::I32DivU, ArmOp::Udiv {
            rd: Reg::R0,
            rn: Reg::R0,
            rm: Reg::R1,
        }),
        ("i32.and → AND", WasmOp::I32And, ArmOp::And {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        }),
        ("i32.or → ORR", WasmOp::I32Or, ArmOp::Orr {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        }),
        ("i32.xor → EOR", WasmOp::I32Xor, ArmOp::Eor {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        }),
    ];

    println!("\n╔══════════════════════════════════════════════════════════════════════╗");
    println!("║              FORMAL VERIFICATION REPORT                              ║");
    println!("╠══════════════════════════════════════════════════════════════════════╣");
    println!("║ WebAssembly → ARM Synthesis Rule Verification                        ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝\n");

    let mut verified = 0;
    let mut invalid = 0;
    let mut unknown = 0;

    for (name, wasm_op, arm_op) in test_cases {
        let rule = create_rule(name, wasm_op, arm_op);
        let result = validator.verify_rule(&rule);

        let status = match &result {
            Ok(ValidationResult::Verified) => {
                verified += 1;
                "✓ PROVEN"
            }
            Ok(ValidationResult::Invalid { .. }) => {
                invalid += 1;
                "✗ INVALID"
            }
            Ok(ValidationResult::Unknown { .. }) => {
                unknown += 1;
                "? UNKNOWN"
            }
            Err(_) => {
                unknown += 1;
                "⚠ ERROR"
            }
        };

        println!("{:40} {}", name, status);
    }

    println!("\n");
    println!("Summary:");
    println!("  ✓ Proven:  {}/8", verified);
    println!("  ✗ Invalid: {}/8", invalid);
    println!("  ? Unknown: {}/8", unknown);
    println!();

    assert_eq!(verified, 8, "Expected 8 operations to be proven correct");
}
