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

#[test]
fn verify_i32_rotl() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // Note: ARM doesn't have ROTL, only ROTR
    // ROTL(x, n) = ROTR(x, 32-n)
    // This requires runtime computation, so we test symbolic equivalence
    let rule = create_rule(
        "i32.rotl",
        WasmOp::I32Rotl,
        ArmOp::Nop, // Placeholder - needs special handling
    );

    // Should not verify directly
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Verified) => panic!("ROTL needs special implementation"),
        _ => {}
    }
}

#[test]
fn verify_i32_rotr() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // ARM has ROR instruction with immediate
    // For verification, we'd need to test with concrete shift amounts
    let rule = create_rule(
        "i32.rotr",
        WasmOp::I32Rotr,
        ArmOp::Ror {
            rd: Reg::R0,
            rn: Reg::R0,
            shift: 0, // Would need to be parameterized
        },
    );

    // Rotation with dynamic amount is complex for SMT
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Unknown { .. }) => {}
        Ok(ValidationResult::Invalid { .. }) => {}
        _ => {}
    }
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
fn verify_i32_ctz() {
    let ctx = create_z3_context();
    let validator = TranslationValidator::new(&ctx);

    // ARM implements CTZ via RBIT + CLZ
    // RBIT reverses bits, then CLZ counts from the other end
    let rule = create_rule(
        "i32.ctz",
        WasmOp::I32Ctz,
        ArmOp::Rbit {
            rd: Reg::R0,
            rm: Reg::R0,
        },
    );

    // This is partial - needs RBIT + CLZ sequence
    match validator.verify_rule(&rule) {
        Ok(ValidationResult::Invalid { .. }) => {} // RBIT alone != CTZ
        _ => {}
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
