//! GENERATED FILE — DO NOT EDIT BY HAND.
//!
//! Emitted by `crate::sel_dsl::generate_lowering_source()` from the declarative
//! rule table [`crate::sel_dsl::RULES`] (VCR-SEL-001 increments 1+2, #242,
//! `docs/design/vcr-sel-001-first-increment.md` +
//! `docs/design/vcr-sel-001-increment-2.md`). Pinned up-to-date by the
//! `generated_lowering_is_up_to_date` test; regenerate with
//! `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
//!
//! Every function here carries a 1:1 Rocq T1 theorem in
//! `coq/Synth/Synth/VcrSelRules.v` (all Qed — coverage-gated by
//! `//coq:vcr_sel_rules_coverage`): the emitted sequence computes the op's
//! result in `rd` for EVERY register assignment satisfying the stated side
//! conditions.

use crate::rules::{ArmOp, Condition, Operand2, Reg};

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

/// `i32.shl`: rd = rn << rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_shl_correct` (Qed).
pub fn rule_i32_shl(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::LslReg { rd, rn, rm }]
}

/// `i32.shr_s`: rd = rn >> rm (arithmetic)
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_shr_s_correct` (Qed).
pub fn rule_i32_shr_s(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::AsrReg { rd, rn, rm }]
}

/// `i32.shr_u`: rd = rn >> rm (logical)
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_shr_u_correct` (Qed).
pub fn rule_i32_shr_u(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::LsrReg { rd, rn, rm }]
}

/// `i32.rotr`: rd = rn rotated right by rm
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_rotr_correct` (Qed).
pub fn rule_i32_rotr(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![ArmOp::RorReg { rd, rn, rm }]
}

/// `i32.eq`: rd = if rn == rm {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_eq_correct` (Qed).
pub fn rule_i32_eq(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::EQ,
        },
    ]
}

/// `i32.ne`: rd = if rn != rm {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_ne_correct` (Qed).
pub fn rule_i32_ne(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::NE,
        },
    ]
}

/// `i32.lt_s`: rd = if rn < rm (signed) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_lt_s_correct` (Qed).
pub fn rule_i32_lt_s(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::LT,
        },
    ]
}

/// `i32.lt_u`: rd = if rn < rm (unsigned) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_lt_u_correct` (Qed).
pub fn rule_i32_lt_u(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::LO,
        },
    ]
}

/// `i32.gt_s`: rd = if rn > rm (signed) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_gt_s_correct` (Qed).
pub fn rule_i32_gt_s(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::GT,
        },
    ]
}

/// `i32.gt_u`: rd = if rn > rm (unsigned) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_gt_u_correct` (Qed).
pub fn rule_i32_gt_u(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::HI,
        },
    ]
}

/// `i32.le_s`: rd = if rn <= rm (signed) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_le_s_correct` (Qed).
pub fn rule_i32_le_s(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::LE,
        },
    ]
}

/// `i32.le_u`: rd = if rn <= rm (unsigned) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_le_u_correct` (Qed).
pub fn rule_i32_le_u(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::LS,
        },
    ]
}

/// `i32.ge_s`: rd = if rn >= rm (signed) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_ge_s_correct` (Qed).
pub fn rule_i32_ge_s(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::GE,
        },
    ]
}

/// `i32.ge_u`: rd = if rn >= rm (unsigned) {1} else {0}
///
/// Rocq obligation: `Synth.Synth.VcrSelRules.rule_i32_ge_u_correct` (Qed).
pub fn rule_i32_ge_u(rd: Reg, rn: Reg, rm: Reg) -> Vec<ArmOp> {
    vec![
        ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        },
        ArmOp::SetCond {
            rd,
            cond: Condition::HS,
        },
    ]
}
