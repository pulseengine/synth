//! GENERATED FILE — DO NOT EDIT BY HAND.
//!
//! Emitted by `crate::sel_dsl::generate_lowering_source()` from the declarative
//! rule table [`crate::sel_dsl::RULES`] (VCR-SEL-001 increment 1, #242,
//! `docs/design/vcr-sel-001-first-increment.md`). Pinned up-to-date by the
//! `generated_lowering_is_up_to_date` test; regenerate with
//! `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
//!
//! Every function here carries a 1:1 Rocq T1 theorem in
//! `coq/Synth/Synth/VcrSelRules.v` (all Qed — coverage-gated by
//! `//coq:vcr_sel_rules_coverage`): the emitted sequence computes the op's
//! result in `rd` for EVERY register assignment satisfying the stated side
//! conditions.

use crate::rules::{ArmOp, Operand2, Reg};

/// `i32.add`: rd = rn + rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_add_correct` (Qed).
pub fn rule_i32_add(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::Add {
        rd,
        rn,
        op2: Operand2::Reg(rm),
    }]
}

/// `i32.sub`: rd = rn - rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_sub_correct` (Qed).
pub fn rule_i32_sub(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::Sub {
        rd,
        rn,
        op2: Operand2::Reg(rm),
    }]
}

/// `i32.mul`: rd = rn * rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_mul_correct` (Qed).
pub fn rule_i32_mul(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::Mul { rd, rn, rm }]
}

/// `i32.and`: rd = rn & rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_and_correct` (Qed).
pub fn rule_i32_and(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::And {
        rd,
        rn,
        op2: Operand2::Reg(rm),
    }]
}

/// `i32.or`: rd = rn | rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_or_correct` (Qed).
pub fn rule_i32_or(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::Orr {
        rd,
        rn,
        op2: Operand2::Reg(rm),
    }]
}

/// `i32.xor`: rd = rn ^ rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_xor_correct` (Qed).
pub fn rule_i32_xor(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::Eor {
        rd,
        rn,
        op2: Operand2::Reg(rm),
    }]
}

/// `i32.rotl`: rotate left by rm = rotate right by (32 - rm), via scratch rs
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_rotl_correct` (Qed).
///
/// Side condition: `rs` must not alias `rn` (hypothesis of the theorem;
/// violation is a loud `Err`, never a silent misassemble).
pub fn rule_i32_rotl(rd: Reg, rn: Reg, rm: Reg, rs: Reg) -> Result<Vec<ArmOp>, &'static str> {
    if rs == rn {
        return Err("rule_i32_rotl: side condition violated: scratch rs must not alias rn");
    }
    Ok(vec![
        ArmOp::Rsb {
            rd: rs,
            rn: rm,
            imm: 32,
        },
        ArmOp::RorReg { rd, rn, rm: rs },
    ])
}
