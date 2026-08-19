//! #981 (RQ-58-VERIFYWIRE) — sensitivity matrix for the newly WIRED shift and
//! rotate rules in `synth verify`.
//!
//! # Why this file exists
//!
//! #981 routes `i32.shl` / `i32.shr_s` / `i32.shr_u` / `i32.rotl` /
//! `i32.rotr` to the register-shift ops #975 modelled (`Rm<7:0>`, ARMv7-M
//! A7.7.68/70/12/117), removing the stale `immediate-shift-encoding` decline.
//! The trap #975 itself documented: a rule that returns `Verified` for BOTH
//! the correct and a corrupted lowering is not wired, it is green-washed —
//! #975 found `i32.add` + `UXTB` "verifying" while the model executed neither
//! instruction. So for every rule this lane claims, this file proves the check
//! is SENSITIVE: the SHIPPED lowering verifies, and each perturbation class
//! (wrong shift op, wrong operand order, dropped/weakened `#31` mask, an
//! extra masking instruction, off-by-one on the rotl amount negation) flips
//! the verdict to `Invalid`.
//!
//! The `Verified` half is instantiated from `sel_dsl::generated` — the SAME
//! single-source table the CLI wiring (#981) and the Rocq model (#667) draw
//! from — at the verify harness's register shape (rd=R0, rn=R0 value, rm=R1
//! amount, rs=R2 scratch). If the shipped table changes shape, the `Verified`
//! half re-verifies the NEW shape or fails loudly; it can never drift into
//! checking a paraphrase.
//!
//! The `verify_rule` entry point is used (not `verify_equivalence` directly)
//! so the path exercised is the one `synth verify`'s rule inventory takes.

#![cfg(feature = "arm")]

use synth_core::WasmOp;
use synth_synthesis::sel_dsl::generated as sel_rules;
use synth_synthesis::{ArmOp, Operand2, Pattern, Reg, Replacement, SynthesisRule};
use synth_verify::{TranslationValidator, ValidationResult, with_verification_context};

/// Wrap an ARM sequence in a `SynthesisRule` the way the #981 CLI wiring does.
fn rule_for(wasm_op: WasmOp, name: &str, ops: Vec<ArmOp>) -> SynthesisRule {
    SynthesisRule {
        name: name.into(),
        priority: 0,
        pattern: Pattern::WasmInstr(wasm_op),
        replacement: Replacement::ArmSequence(ops),
        cost: synth_synthesis::Cost {
            cycles: 2,
            code_size: 6,
            registers: 3,
        },
    }
}

fn assert_verified(v: &TranslationValidator, wasm_op: WasmOp, name: &str, ops: Vec<ArmOp>) {
    let r = v.verify_rule(&rule_for(wasm_op.clone(), name, ops));
    assert!(
        matches!(r, Ok(ValidationResult::Verified)),
        "{name}: shipped lowering for {wasm_op:?} must verify, got {r:?}"
    );
}

fn assert_invalid(v: &TranslationValidator, wasm_op: WasmOp, label: &str, ops: Vec<ArmOp>) {
    let r = v.verify_rule(&rule_for(wasm_op.clone(), label, ops));
    assert!(
        matches!(r, Ok(ValidationResult::Invalid { .. })),
        "{label}: perturbed lowering for {wasm_op:?} MUST be Invalid — a check \
         that passes the corrupted form too is green-washed, not wired; got {r:?}"
    );
}

/// The five shipped instantiations, at the harness register shape.
fn shipped_shl() -> Vec<ArmOp> {
    sel_rules::rule_i32_shl(Reg::R0, Reg::R0, Reg::R1, Reg::R2).expect("rs != rn")
}
fn shipped_shr_s() -> Vec<ArmOp> {
    sel_rules::rule_i32_shr_s(Reg::R0, Reg::R0, Reg::R1, Reg::R2).expect("rs != rn")
}
fn shipped_shr_u() -> Vec<ArmOp> {
    sel_rules::rule_i32_shr_u(Reg::R0, Reg::R0, Reg::R1, Reg::R2).expect("rs != rn")
}
fn shipped_rotl() -> Vec<ArmOp> {
    sel_rules::rule_i32_rotl(Reg::R0, Reg::R0, Reg::R1, Reg::R2).expect("rs != rn")
}
fn shipped_rotr() -> Vec<ArmOp> {
    sel_rules::rule_i32_rotr(Reg::R0, Reg::R0, Reg::R1)
}

const MASK31: ArmOp = ArmOp::And {
    rd: Reg::R2,
    rn: Reg::R1,
    op2: Operand2::Imm(31),
};

// ---------------------------------------------------------------------------
// The claimed half: every shipped lowering verifies through `verify_rule`.
// ---------------------------------------------------------------------------

#[test]
fn all_five_shipped_shift_and_rotate_rules_verify_via_verify_rule() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        assert_verified(&v, WasmOp::I32Shl, "i32.shl shipped", shipped_shl());
        assert_verified(&v, WasmOp::I32ShrS, "i32.shr_s shipped", shipped_shr_s());
        assert_verified(&v, WasmOp::I32ShrU, "i32.shr_u shipped", shipped_shr_u());
        assert_verified(&v, WasmOp::I32Rotl, "i32.rotl shipped", shipped_rotl());
        assert_verified(&v, WasmOp::I32Rotr, "i32.rotr shipped", shipped_rotr());
    });
}

// ---------------------------------------------------------------------------
// Sensitivity: each perturbation class flips the verdict to Invalid.
// ---------------------------------------------------------------------------

/// Wrong shift OPCODE, mask intact. A checker keyed only on "there is a mask
/// and a shift" would pass these.
#[test]
fn wrong_shift_opcode_is_invalid() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        // shl lowered with a LOGICAL RIGHT shift.
        assert_invalid(
            &v,
            WasmOp::I32Shl,
            "shl-as-lsr",
            vec![
                MASK31,
                ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ],
        );
        // shr_s lowered LOGICAL instead of ARITHMETIC (differs on negatives).
        assert_invalid(
            &v,
            WasmOp::I32ShrS,
            "shr_s-as-lsr",
            vec![
                MASK31,
                ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ],
        );
        // shr_u lowered ARITHMETIC instead of LOGICAL.
        assert_invalid(
            &v,
            WasmOp::I32ShrU,
            "shr_u-as-asr",
            vec![
                MASK31,
                ArmOp::AsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ],
        );
        // rotr lowered as a plain right SHIFT (loses the wrapped-around bits).
        assert_invalid(
            &v,
            WasmOp::I32Rotr,
            "rotr-as-lsr",
            vec![
                MASK31,
                ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ],
        );
    });
}

/// Wrong OPERAND ORDER: shifting the amount by the value.
#[test]
fn swapped_operand_order_is_invalid() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        assert_invalid(
            &v,
            WasmOp::I32Shl,
            "shl-operands-swapped",
            vec![
                MASK31,
                ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R2,
                    rm: Reg::R0,
                },
            ],
        );
        assert_invalid(
            &v,
            WasmOp::I32Rotr,
            "rotr-operands-swapped",
            vec![ArmOp::RorReg {
                rd: Reg::R0,
                rn: Reg::R1,
                rm: Reg::R0,
            }],
        );
    });
}

/// The #682 mask, DROPPED or WEAKENED. This is the class the `Rm<7:0>` model
/// exists to catch: an unmasked `LSL (register)` shifts by the low EIGHT bits,
/// so `Rm = 32` clears the register where WASM's mod-32 rule is the identity.
/// A mask of `#15` (off-by-one on the width) diverges at `Rm = 16`; `#63` at
/// `Rm = 32`.
#[test]
fn dropped_or_weakened_mask_is_invalid() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        for (wasm_op, label, unmasked, narrow, wide) in [
            (
                WasmOp::I32Shl,
                "shl",
                vec![ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
                ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
                ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ),
            (
                WasmOp::I32ShrU,
                "shr_u",
                vec![ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
                ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
                ArmOp::LsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ),
            (
                WasmOp::I32ShrS,
                "shr_s",
                vec![ArmOp::AsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R1,
                }],
                ArmOp::AsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
                ArmOp::AsrReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ),
        ] {
            assert_invalid(&v, wasm_op.clone(), &format!("{label}-no-mask"), unmasked);
            assert_invalid(
                &v,
                wasm_op.clone(),
                &format!("{label}-mask-15"),
                vec![
                    ArmOp::And {
                        rd: Reg::R2,
                        rn: Reg::R1,
                        op2: Operand2::Imm(15),
                    },
                    narrow,
                ],
            );
            assert_invalid(
                &v,
                wasm_op,
                &format!("{label}-mask-63"),
                vec![
                    ArmOp::And {
                        rd: Reg::R2,
                        rn: Reg::R1,
                        op2: Operand2::Imm(63),
                    },
                    wide,
                ],
            );
        }
    });
}

/// An EXTRA masking instruction appended to a correct lowering — the exact
/// #975 cautionary shape (`ADD ; UXTB` "verified" while the model executed
/// neither op). With the model executing every instruction, the appended
/// `UXTB` must now flip the verdict.
#[test]
fn extra_masking_instruction_is_invalid() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        let mut shl_uxtb = shipped_shl();
        shl_uxtb.push(ArmOp::Uxtb {
            rd: Reg::R0,
            rm: Reg::R0,
        });
        assert_invalid(&v, WasmOp::I32Shl, "shl-plus-uxtb", shl_uxtb);

        let mut rotr_uxth = shipped_rotr();
        rotr_uxth.push(ArmOp::Uxth {
            rd: Reg::R0,
            rm: Reg::R0,
        });
        assert_invalid(&v, WasmOp::I32Rotr, "rotr-plus-uxth", rotr_uxth);
    });
}

/// rotl's amount negation, corrupted: off-by-one on the RSB immediate, the
/// RSB dropped outright (yielding rotr), and the post-RSB rotate replaced by
/// a shift.
#[test]
fn corrupted_rotl_negation_is_invalid() {
    with_verification_context(|| {
        let v = TranslationValidator::new();
        // RSB #31 instead of #32: off-by-one in the negation.
        assert_invalid(
            &v,
            WasmOp::I32Rotl,
            "rotl-rsb-31",
            vec![
                ArmOp::Rsb {
                    rd: Reg::R2,
                    rn: Reg::R1,
                    imm: 31,
                },
                ArmOp::RorReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ],
        );
        // RSB dropped: rotl lowered as rotr.
        assert_invalid(
            &v,
            WasmOp::I32Rotl,
            "rotl-as-rotr",
            vec![ArmOp::RorReg {
                rd: Reg::R0,
                rn: Reg::R0,
                rm: Reg::R1,
            }],
        );
        // Correct negation, wrong final op (shift discards wrapped bits).
        assert_invalid(
            &v,
            WasmOp::I32Rotl,
            "rotl-ror-as-lsl",
            vec![
                ArmOp::Rsb {
                    rd: Reg::R2,
                    rn: Reg::R1,
                    imm: 32,
                },
                ArmOp::LslReg {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    rm: Reg::R2,
                },
            ],
        );
    });
}
