//! Verification Coverage Report Generator
//!
//! This example generates a comprehensive report of all verified synthesis rules,
//! showing which WASM->ARM transformations have been formally proven correct.
//! Requires both `z3-solver` and `arm` features.

use synth_synthesis::{ArmOp, Operand2, Pattern, Reg, Replacement, SynthesisRule, WasmOp};
use synth_verify::{with_z3_context, TranslationValidator, ValidationResult};

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

fn main() {
    println!("\n======================================================================");
    println!("                    FORMAL VERIFICATION REPORT");
    println!("                    Synth Compiler - Phase 1");
    println!("======================================================================\n");

    with_z3_context(|| {
        let mut validator = TranslationValidator::new();
        validator.set_timeout(10000); // 10 second timeout per rule

        // Define all directly-mappable synthesis rules
        let test_cases = vec![
            // === ARITHMETIC OPERATIONS ===
            (
                "i32.add -> ADD",
                WasmOp::I32Add,
                ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
            ),
            (
                "i32.sub -> SUB",
                WasmOp::I32Sub,
                ArmOp::Sub {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
            ),
            (
                "i32.mul -> MUL",
                WasmOp::I32Mul,
                ArmOp::Mul {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                },
            ),
            (
                "i32.div_s -> SDIV",
                WasmOp::I32DivS,
                ArmOp::Sdiv {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                },
            ),
            (
                "i32.div_u -> UDIV",
                WasmOp::I32DivU,
                ArmOp::Udiv {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                },
            ),
            // === BITWISE OPERATIONS ===
            (
                "i32.and -> AND",
                WasmOp::I32And,
                ArmOp::And {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
            ),
            (
                "i32.or -> ORR",
                WasmOp::I32Or,
                ArmOp::Orr {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
            ),
            (
                "i32.xor -> EOR",
                WasmOp::I32Xor,
                ArmOp::Eor {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
            ),
        ];

        println!("===================================================================\n");
        println!("  Testing Directly-Mappable WASM -> ARM Synthesis Rules\n");
        println!("===================================================================\n");

        let mut verified = 0;
        let mut invalid = 0;
        let mut unknown = 0;
        let mut errors = 0;

        let mut results_data = Vec::new();

        for (name, wasm_op, arm_op) in test_cases {
            print!("  {:50} ", name);
            std::io::Write::flush(&mut std::io::stdout()).unwrap();

            let rule = create_rule(name, wasm_op, arm_op);
            let start = std::time::Instant::now();
            let result = validator.verify_rule(&rule);
            let elapsed = start.elapsed();

            let (status, symbol) = match &result {
                Ok(ValidationResult::Verified) => {
                    verified += 1;
                    ("PROVEN", "V")
                }
                Ok(ValidationResult::Invalid { counterexample }) => {
                    invalid += 1;
                    eprintln!("\n      Counterexample: {:?}", counterexample);
                    ("INVALID", "X")
                }
                Ok(ValidationResult::Unknown { reason: _ }) => {
                    unknown += 1;
                    if elapsed.as_millis() > 9000 {
                        ("TIMEOUT", "T")
                    } else {
                        ("UNKNOWN", "?")
                    }
                }
                Err(e) => {
                    errors += 1;
                    eprintln!("\n      Error: {}", e);
                    ("ERROR", "!")
                }
            };

            println!("{} ({:>6}ms)", status, elapsed.as_millis());

            results_data.push((name, symbol, elapsed.as_millis()));
        }

        let total = verified + invalid + unknown + errors;

        println!("\n===================================================================");
        println!("\n  VERIFICATION STATISTICS\n");
        println!("===================================================================\n");

        println!("  Total Rules Tested:     {}", total);
        println!(
            "  V Proven Correct:       {} ({:.1}%)",
            verified,
            (verified as f64 / total as f64) * 100.0
        );
        println!(
            "  X Found Incorrect:      {} ({:.1}%)",
            invalid,
            (invalid as f64 / total as f64) * 100.0
        );
        println!(
            "  ? Inconclusive:         {} ({:.1}%)",
            unknown,
            (unknown as f64 / total as f64) * 100.0
        );
        println!(
            "  ! Errors:               {} ({:.1}%)",
            errors,
            (errors as f64 / total as f64) * 100.0
        );

        println!("\n===================================================================\n");
        println!("  FORMAL GUARANTEES\n");
        println!("===================================================================\n");

        if verified > 0 {
            println!("  The following synthesis rules are MATHEMATICALLY GUARANTEED correct:");
            println!();
            for (name, symbol, _) in &results_data {
                if *symbol == "V" {
                    println!("    V {}", name);
                }
            }
            println!();
            println!("  These rules have been proven correct for ALL possible inputs using");
            println!("  Z3 SMT solver with bounded translation validation (Alive2-style).");
            println!();
        }

        if invalid > 0 {
            println!("\n  WARNING: {} rule(s) found INCORRECT!", invalid);
            println!("  These rules would generate wrong code and must be fixed.");
        }

        let coverage_pct = (verified as f64 / 51.0) * 100.0; // 51 total WASM ops
        println!("\n===================================================================");
        println!(
            "\n  COVERAGE: {:.1}% ({}/51 WASM operations verified)\n",
            coverage_pct, verified
        );
        println!("===================================================================\n");

        println!(
            "Report generated: {}",
            chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
        );
        println!();
    });
}
