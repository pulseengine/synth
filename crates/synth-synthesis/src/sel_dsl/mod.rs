//! VCR-SEL-001 increments 1+2+3 (#242) — the Rocq-discharged selector rule DSL.
//!
//! Scope: `docs/design/vcr-sel-001-first-increment.md` (increment 1),
//! `docs/design/vcr-sel-001-increment-2.md` (increment 2) and
//! `docs/design/vcr-sel-001-increment-3.md` (increment 3). This module is the
//! **checked-in rule table**: a declarative `op → parameterized ARM sequence`
//! (registers as variables, side conditions explicit) for:
//!
//! - increment 1: the pilot-measured tier-A i32 ALU class
//!   (`add/sub/mul/and/or/xor`, 6/6 auto-discharge) plus one tier-B
//!   scratch-using shape (`i32.rotl`), included deliberately so the rule
//!   format carries a scratch non-aliasing side condition from day one;
//! - increment 2: the i32 register-shift family (`shl/shr_s/shr_u` + `rotr`,
//!   all single-instruction tier-A — no scratch needed, measured) and the ten
//!   i32 comparisons (`eq/ne/lt_s/lt_u/gt_s/gt_u/le_s/le_u/ge_s/ge_u`, the
//!   CMP+SetCond shape — no side conditions either: the flags transfer through
//!   NZCV, not a register, so every rd/rn/rm aliasing is admitted by the
//!   universal quantifier);
//! - increment 3: the i64 register-pair family — `i64.add/sub/and/or/xor`
//!   (the two-instruction pair shapes ADDS+ADC / SUBS+SBC / AND×2 / ORR×2 /
//!   EOR×2, an i64 value living in a (lo, hi) register pair) plus `i64.eqz`
//!   (the single-instruction `I64SetCondZ` shape). The pair shapes carry
//!   THREE explicit aliasing side conditions each — the low-half instruction
//!   writes `rd_lo` before the high-half instruction reads `rn_hi`/`rm_hi`,
//!   so a rule format that could not state "the destination must not be
//!   clobbered before use" is exactly how #632-class bugs happen. Each pair
//!   theorem proves BOTH result words.
//!
//! The table is turned into plain Rust lowering functions by
//! [`generate_lowering_source`] and the output is **committed to the tree** at
//! [`generated`] (reviewable diffs, no build-time codegen). `select_default`
//! keeps dispatch ownership: a migrated arm delegates to the generated rule
//! behind `SYNTH_SEL_DSL` (default OFF), so OFF ≡ baseline byte-identical by
//! construction.
//!
//! Every rule carries a **1:1 Rocq obligation**: rule `rule_i32_add` ↔ theorem
//! `rule_i32_add_correct` in `coq/Synth/Synth/VcrSelRules.v` (T1, discharged by
//! `synth_binop_proof_poly`; the scratch shape by the pilot's stepped proof with
//! the explicit `rs <> rn` hypothesis). Coverage is gated twice:
//!
//! - cargo side: [`tests::coq_coverage_every_rule_has_a_qed_theorem`] reads the
//!   `.v` file and fails if a rule lacks its `Theorem <name>_correct` or the
//!   file contains `Admitted`/`admit.`;
//! - bazel side: `//coq:vcr_sel_rules_coverage` (part of the
//!   `//coq:verify_proofs` suite CI runs) checks `coq/vcr_sel_rules.manifest`
//!   against the `.v`, and [`tests::manifest_matches_rule_table`] pins the
//!   manifest to this table — a rule without a Qed cannot merge.

use synth_core::WasmOp;

pub mod generated;

/// A register **variable** in a rule template — the rule is universally
/// quantified over the concrete assignment (VCR-RA picks the registers; the
/// Rocq theorem holds for every assignment satisfying the side conditions).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegVar {
    /// Destination register.
    Rd,
    /// First (left) operand register.
    Rn,
    /// Second (right) operand register.
    Rm,
    /// Scratch register (tier-B shapes only).
    Rs,
    /// Destination pair, low word (i64 pair rules).
    RdLo,
    /// Destination pair, high word (i64 pair rules).
    RdHi,
    /// First operand pair, low word (i64 pair rules).
    RnLo,
    /// First operand pair, high word (i64 pair rules).
    RnHi,
    /// Second operand pair, low word (i64 pair rules).
    RmLo,
    /// Second operand pair, high word (i64 pair rules).
    RmHi,
}

impl RegVar {
    /// The Rust parameter name this variable binds to in a generated lowering
    /// function (also the Coq binder name in the paired theorem).
    pub const fn rust_name(self) -> &'static str {
        match self {
            RegVar::Rd => "rd",
            RegVar::Rn => "rn",
            RegVar::Rm => "rm",
            RegVar::Rs => "rs",
            RegVar::RdLo => "rd_lo",
            RegVar::RdHi => "rd_hi",
            RegVar::RnLo => "rn_lo",
            RegVar::RnHi => "rn_hi",
            RegVar::RmLo => "rm_lo",
            RegVar::RmHi => "rm_hi",
        }
    }
}

/// An explicit side condition a rule's register assignment must satisfy.
///
/// This is the constraint the DSL must carry and feed to the allocator
/// (VCR-RA-001): e.g. `i32.rotl`'s scratch is written by instruction 1 before
/// the value register is read by instruction 2, so `rs` must not alias `rn` —
/// in the fixed-register proof that was a `discriminate` on `R0 <> R2`; under
/// register generalization it is a real hypothesis of the theorem, and here a
/// real runtime guard in the generated function (Ok-or-Err, never silent).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SideCondition {
    /// The two register variables must be assigned distinct registers.
    NotAlias(RegVar, RegVar),
}

/// Which hand-written selector arm delegates to this rule behind
/// `SYNTH_SEL_DSL` — i.e. where the rule is byte-identically wired.
///
/// Increment 1 wired `select_default` only. Increment 2 steps the comparison
/// family into `select_with_stack` because that is where the load-bearing
/// hand-written CMP+SetCond arm lives: `select_default`'s comparison arms are
/// a *blind* bare-`Cmp` lowering (the 0/1 result is never materialized —
/// production-unreachable, `select_with_stack` owns comparisons), so a rule
/// byte-matching them would be unprovable as T1 result-correspondence. Those
/// arms stay hand-written — an honest holdout, documented in
/// `docs/design/vcr-sel-001-increment-2.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delegation {
    /// Wired in `select_default`'s match arm only (increment 1 pattern).
    SelectDefault,
    /// Wired in `select_with_stack`'s arm only (the load-bearing path).
    SelectWithStack,
    /// Wired in both selectors' arms (byte-identical in each).
    Both,
}

/// A condition code for the `SetCond` template shape — mirrors
/// `crate::rules::Condition` (and the Coq flat model's `MOVcc` family, which
/// is how `ArmOp::SetCond` is modeled in `VcrSelRules.v`: `MOV rd #0;
/// MOVcc rd #1`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CondCode {
    /// Equal (Z == 1).
    Eq,
    /// Not equal (Z == 0).
    Ne,
    /// Signed less-than (N != V).
    Lt,
    /// Unsigned lower (C == 0).
    Lo,
    /// Signed greater-than (Z == 0 && N == V).
    Gt,
    /// Unsigned higher (C == 1 && Z == 0).
    Hi,
    /// Signed less-or-equal (Z == 1 || N != V).
    Le,
    /// Unsigned lower-or-same (C == 0 || Z == 1).
    Ls,
    /// Signed greater-or-equal (N == V).
    Ge,
    /// Unsigned higher-or-same (C == 1).
    Hs,
}

impl CondCode {
    /// The `crate::rules::Condition` variant path this code renders to in the
    /// generated lowering function.
    pub const fn rust_name(self) -> &'static str {
        match self {
            CondCode::Eq => "Condition::EQ",
            CondCode::Ne => "Condition::NE",
            CondCode::Lt => "Condition::LT",
            CondCode::Lo => "Condition::LO",
            CondCode::Gt => "Condition::GT",
            CondCode::Hi => "Condition::HI",
            CondCode::Le => "Condition::LE",
            CondCode::Ls => "Condition::LS",
            CondCode::Ge => "Condition::GE",
            CondCode::Hs => "Condition::HS",
        }
    }
}

/// One ARM instruction template over register variables. Shapes cover exactly
/// what the increment-1 rules need; new op classes add shapes alongside their
/// rules (+ theorems).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TemplateOp {
    /// `ArmOp::Add { rd, rn, op2: Reg(rm) }`
    AddReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Sub { rd, rn, op2: Reg(rm) }`
    SubReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Mul { rd, rn, rm }`
    Mul { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::And { rd, rn, op2: Reg(rm) }`
    AndReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Orr { rd, rn, op2: Reg(rm) }`
    OrrReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Eor { rd, rn, op2: Reg(rm) }`
    EorReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Rsb { rd, rn, imm }` — `rd = imm - rn`
    RsbImm { rd: RegVar, rn: RegVar, imm: u32 },
    /// `ArmOp::RorReg { rd, rn, rm }`
    RorReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::LslReg { rd, rn, rm }`
    LslReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::LsrReg { rd, rn, rm }`
    LsrReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::AsrReg { rd, rn, rm }`
    AsrReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Cmp { rn, op2: Reg(rm) }` — flags only, no register written
    CmpReg { rn: RegVar, rm: RegVar },
    /// `ArmOp::SetCond { rd, cond }` — rd = if cond over current NZCV {1} else {0}
    SetCond { rd: RegVar, cond: CondCode },
    /// `ArmOp::Adds { rd, rn, op2: Reg(rm) }` — ADD setting flags (C = carry-out)
    AddsReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Adc { rd, rn, op2: Reg(rm) }` — ADD with carry-in from C
    AdcReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Subs { rd, rn, op2: Reg(rm) }` — SUB setting flags (C = no-borrow)
    SubsReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::Sbc { rd, rn, op2: Reg(rm) }` — SUB with borrow-in from NOT(C)
    SbcReg { rd: RegVar, rn: RegVar, rm: RegVar },
    /// `ArmOp::I64SetCondZ { rd, rn_lo, rn_hi }` — rd = if (rn_hi:rn_lo) == 0 {1} else {0}
    I64SetCondZ {
        rd: RegVar,
        rn_lo: RegVar,
        rn_hi: RegVar,
    },
}

/// One declarative lowering rule: `op → parameterized ARM sequence`.
#[derive(Debug, Clone, PartialEq)]
pub struct SelRule {
    /// Rule name. 1:1 with the Rocq theorem `<name>_correct` in
    /// `coq/Synth/Synth/VcrSelRules.v` and with the generated Rust function
    /// `generated::<name>`.
    pub name: &'static str,
    /// The WASM op this rule lowers.
    pub op: WasmOp,
    /// Register parameters of the generated function, in signature order.
    pub params: &'static [RegVar],
    /// Explicit side conditions (checked at runtime in the generated function,
    /// hypotheses of the Rocq theorem).
    pub side_conditions: &'static [SideCondition],
    /// The emitted instruction sequence, over register variables.
    pub seq: &'static [TemplateOp],
    /// Which hand-written selector arm delegates to this rule (mirror-pin
    /// target: the delegation must be byte-identical there).
    pub delegation: Delegation,
    /// One-line human description for the generated function's doc comment.
    pub doc: &'static str,
}

impl SelRule {
    /// The 1:1 paired Rocq theorem name.
    pub fn theorem(&self) -> String {
        format!("{}_correct", self.name)
    }
}

use RegVar::{Rd, RdHi, RdLo, Rm, RmHi, RmLo, Rn, RnHi, RnLo, Rs};

/// The three aliasing side conditions every two-instruction i64 pair rule
/// carries (increment 3 — the #632 lesson made explicit): the low-half
/// instruction writes `rd_lo` BEFORE the high-half instruction reads
/// `rn_hi`/`rm_hi` and writes `rd_hi`, so
///
/// - `rd_hi` must not alias `rd_lo` (the high write would destroy the low
///   result word),
/// - `rd_lo` must not alias `rn_hi` (the low write would clobber operand 1's
///   high half before it is read),
/// - `rd_lo` must not alias `rm_hi` (same for operand 2).
///
/// In-place lowering (`rd_lo = rn_lo`, `rd_hi = rn_hi` — `select_default`'s
/// fixed `R0:R1 += R2:R3` shape) satisfies all three; so does
/// `select_with_stack`'s `alloc_consecutive_pair` destination (avoids every
/// operand half, and a consecutive pair is never self-aliased). Each is a
/// hypothesis of the paired Rocq theorem and a runtime `Err` in the generated
/// lowering.
const I64_PAIR_SIDE_CONDITIONS: &[SideCondition] = &[
    SideCondition::NotAlias(RdHi, RdLo),
    SideCondition::NotAlias(RdLo, RnHi),
    SideCondition::NotAlias(RdLo, RmHi),
];

/// The parameter order shared by every binary i64 pair rule.
const I64_PAIR_PARAMS: &[RegVar] = &[RdLo, RdHi, RnLo, RnHi, RmLo, RmHi];

/// The increment-1 rule table: the tier-A six + tier-B `i32.rotl`.
///
/// Sequences are copied byte-for-byte from `select_default`'s hand-written
/// arms — increment 1 migrates *structure, never bytes* (mirror-pinned by
/// `sel_dsl_mirror_pin_generated_rules_match_handwritten_arms_242`).
pub const RULES: &[SelRule] = &[
    SelRule {
        name: "rule_i32_add",
        op: WasmOp::I32Add,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::AddReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::SelectDefault,
        doc: "`i32.add`: rd = rn + rm",
    },
    SelRule {
        name: "rule_i32_sub",
        op: WasmOp::I32Sub,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::SubReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::SelectDefault,
        doc: "`i32.sub`: rd = rn - rm",
    },
    SelRule {
        name: "rule_i32_mul",
        op: WasmOp::I32Mul,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::Mul {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::SelectDefault,
        doc: "`i32.mul`: rd = rn * rm",
    },
    SelRule {
        name: "rule_i32_and",
        op: WasmOp::I32And,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::AndReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::SelectDefault,
        doc: "`i32.and`: rd = rn & rm",
    },
    SelRule {
        name: "rule_i32_or",
        op: WasmOp::I32Or,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::OrrReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::SelectDefault,
        doc: "`i32.or`: rd = rn | rm",
    },
    SelRule {
        name: "rule_i32_xor",
        op: WasmOp::I32Xor,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::EorReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::SelectDefault,
        doc: "`i32.xor`: rd = rn ^ rm",
    },
    SelRule {
        name: "rule_i32_rotl",
        op: WasmOp::I32Rotl,
        params: &[Rd, Rn, Rm, Rs],
        side_conditions: &[SideCondition::NotAlias(Rs, Rn)],
        seq: &[
            TemplateOp::RsbImm {
                rd: Rs,
                rn: Rm,
                imm: 32,
            },
            TemplateOp::RorReg {
                rd: Rd,
                rn: Rn,
                rm: Rs,
            },
        ],
        delegation: Delegation::SelectDefault,
        doc: "`i32.rotl`: rotate left by rm = rotate right by (32 - rm), via scratch rs",
    },
    // ---- increment 2: i32 register shifts + rotr (all tier-A: single
    // instruction, no scratch, no side conditions) ----
    SelRule {
        name: "rule_i32_shl",
        op: WasmOp::I32Shl,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::LslReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::Both,
        doc: "`i32.shl`: rd = rn << rm",
    },
    SelRule {
        name: "rule_i32_shr_s",
        op: WasmOp::I32ShrS,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::AsrReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::Both,
        doc: "`i32.shr_s`: rd = rn >> rm (arithmetic)",
    },
    SelRule {
        name: "rule_i32_shr_u",
        op: WasmOp::I32ShrU,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::LsrReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::Both,
        doc: "`i32.shr_u`: rd = rn >> rm (logical)",
    },
    SelRule {
        name: "rule_i32_rotr",
        op: WasmOp::I32Rotr,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::RorReg {
            rd: Rd,
            rn: Rn,
            rm: Rm,
        }],
        delegation: Delegation::Both,
        doc: "`i32.rotr`: rd = rn rotated right by rm",
    },
    // ---- increment 2: i32 comparisons — the CMP+SetCond shape. NO side
    // conditions: CMP latches NZCV before SetCond writes rd, so every
    // rd/rn/rm aliasing is admitted (the flags transfer is not a register).
    // Delegated in select_with_stack (the load-bearing arm) ONLY:
    // select_default's blind bare-Cmp comparison arms never materialize the
    // 0/1 result and stay hand-written (unprovable-as-T1 holdout). ----
    SelRule {
        name: "rule_i32_eq",
        op: WasmOp::I32Eq,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Eq,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.eq`: rd = if rn == rm {1} else {0}",
    },
    SelRule {
        name: "rule_i32_ne",
        op: WasmOp::I32Ne,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Ne,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.ne`: rd = if rn != rm {1} else {0}",
    },
    SelRule {
        name: "rule_i32_lt_s",
        op: WasmOp::I32LtS,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Lt,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.lt_s`: rd = if rn < rm (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_lt_u",
        op: WasmOp::I32LtU,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Lo,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.lt_u`: rd = if rn < rm (unsigned) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_gt_s",
        op: WasmOp::I32GtS,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Gt,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.gt_s`: rd = if rn > rm (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_gt_u",
        op: WasmOp::I32GtU,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Hi,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.gt_u`: rd = if rn > rm (unsigned) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_le_s",
        op: WasmOp::I32LeS,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Le,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.le_s`: rd = if rn <= rm (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_le_u",
        op: WasmOp::I32LeU,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Ls,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.le_u`: rd = if rn <= rm (unsigned) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_ge_s",
        op: WasmOp::I32GeS,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Ge,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.ge_s`: rd = if rn >= rm (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i32_ge_u",
        op: WasmOp::I32GeU,
        params: &[Rd, Rn, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpReg { rn: Rn, rm: Rm },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Hs,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.ge_u`: rd = if rn >= rm (unsigned) {1} else {0}",
    },
    // ---- increment 3: the i64 register-pair family. An i64 value lives in
    // a (lo, hi) register pair; each binary rule is parameterized over SIX
    // registers and emits the two-instruction pair shape. All carry the
    // three explicit aliasing side conditions (I64_PAIR_SIDE_CONDITIONS) —
    // the low-half instruction writes rd_lo before the high-half
    // instruction reads rn_hi/rm_hi. Delegated in BOTH selectors:
    // select_default's fixed R0:R1 += R2:R3 arms and select_with_stack's
    // allocated-pair arms are instances of the same rule (both satisfy the
    // side conditions — see I64_PAIR_SIDE_CONDITIONS). ----
    SelRule {
        name: "rule_i64_add",
        op: WasmOp::I64Add,
        params: I64_PAIR_PARAMS,
        side_conditions: I64_PAIR_SIDE_CONDITIONS,
        seq: &[
            TemplateOp::AddsReg {
                rd: RdLo,
                rn: RnLo,
                rm: RmLo,
            },
            TemplateOp::AdcReg {
                rd: RdHi,
                rn: RnHi,
                rm: RmHi,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i64.add`: (rd_hi:rd_lo) = (rn_hi:rn_lo) + (rm_hi:rm_lo), carry via ADDS+ADC",
    },
    SelRule {
        name: "rule_i64_sub",
        op: WasmOp::I64Sub,
        params: I64_PAIR_PARAMS,
        side_conditions: I64_PAIR_SIDE_CONDITIONS,
        seq: &[
            TemplateOp::SubsReg {
                rd: RdLo,
                rn: RnLo,
                rm: RmLo,
            },
            TemplateOp::SbcReg {
                rd: RdHi,
                rn: RnHi,
                rm: RmHi,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i64.sub`: (rd_hi:rd_lo) = (rn_hi:rn_lo) - (rm_hi:rm_lo), borrow via SUBS+SBC",
    },
    SelRule {
        name: "rule_i64_and",
        op: WasmOp::I64And,
        params: I64_PAIR_PARAMS,
        side_conditions: I64_PAIR_SIDE_CONDITIONS,
        seq: &[
            TemplateOp::AndReg {
                rd: RdLo,
                rn: RnLo,
                rm: RmLo,
            },
            TemplateOp::AndReg {
                rd: RdHi,
                rn: RnHi,
                rm: RmHi,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i64.and`: (rd_hi:rd_lo) = (rn_hi:rn_lo) & (rm_hi:rm_lo), per-half AND",
    },
    SelRule {
        name: "rule_i64_or",
        op: WasmOp::I64Or,
        params: I64_PAIR_PARAMS,
        side_conditions: I64_PAIR_SIDE_CONDITIONS,
        seq: &[
            TemplateOp::OrrReg {
                rd: RdLo,
                rn: RnLo,
                rm: RmLo,
            },
            TemplateOp::OrrReg {
                rd: RdHi,
                rn: RnHi,
                rm: RmHi,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i64.or`: (rd_hi:rd_lo) = (rn_hi:rn_lo) | (rm_hi:rm_lo), per-half ORR",
    },
    SelRule {
        name: "rule_i64_xor",
        op: WasmOp::I64Xor,
        params: I64_PAIR_PARAMS,
        side_conditions: I64_PAIR_SIDE_CONDITIONS,
        seq: &[
            TemplateOp::EorReg {
                rd: RdLo,
                rn: RnLo,
                rm: RmLo,
            },
            TemplateOp::EorReg {
                rd: RdHi,
                rn: RnHi,
                rm: RmHi,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i64.xor`: (rd_hi:rd_lo) = (rn_hi:rn_lo) ^ (rm_hi:rm_lo), per-half EOR",
    },
    // i64.eqz — the SetCondZ shape: single pseudo-op, reads both operand
    // halves before writing the single i32 result register, so NO side
    // conditions (every rd/rn_lo/rn_hi aliasing is admitted by the
    // universal quantifier in rule_i64_eqz_correct).
    SelRule {
        name: "rule_i64_eqz",
        op: WasmOp::I64Eqz,
        params: &[Rd, RnLo, RnHi],
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCondZ {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
        }],
        delegation: Delegation::Both,
        doc: "`i64.eqz`: rd = if (rn_hi:rn_lo) == 0 {1} else {0}",
    },
];

/// Dispatch an i32 comparison op to its generated Rocq-proved rule
/// (increment 2). Returns `None` for non-comparison ops so the caller's
/// hand-written arm keeps ownership — the delegation is byte-identical
/// where it fires (mirror-pinned) and a no-op everywhere else.
pub fn i32_cmp_rule(
    op: &WasmOp,
    rd: crate::rules::Reg,
    rn: crate::rules::Reg,
    rm: crate::rules::Reg,
) -> Option<Vec<crate::rules::ArmOp>> {
    Some(match op {
        WasmOp::I32Eq => generated::rule_i32_eq(rd, rn, rm),
        WasmOp::I32Ne => generated::rule_i32_ne(rd, rn, rm),
        WasmOp::I32LtS => generated::rule_i32_lt_s(rd, rn, rm),
        WasmOp::I32LtU => generated::rule_i32_lt_u(rd, rn, rm),
        WasmOp::I32GtS => generated::rule_i32_gt_s(rd, rn, rm),
        WasmOp::I32GtU => generated::rule_i32_gt_u(rd, rn, rm),
        WasmOp::I32LeS => generated::rule_i32_le_s(rd, rn, rm),
        WasmOp::I32LeU => generated::rule_i32_le_u(rd, rn, rm),
        WasmOp::I32GeS => generated::rule_i32_ge_s(rd, rn, rm),
        WasmOp::I32GeU => generated::rule_i32_ge_u(rd, rn, rm),
        _ => return None,
    })
}

/// Dispatch an i32 register-shift/rotate op to its generated Rocq-proved rule
/// (increment 2). Same contract as [`i32_cmp_rule`].
pub fn i32_shift_rule(
    op: &WasmOp,
    rd: crate::rules::Reg,
    rn: crate::rules::Reg,
    rm: crate::rules::Reg,
) -> Option<Vec<crate::rules::ArmOp>> {
    Some(match op {
        WasmOp::I32Shl => generated::rule_i32_shl(rd, rn, rm),
        WasmOp::I32ShrS => generated::rule_i32_shr_s(rd, rn, rm),
        WasmOp::I32ShrU => generated::rule_i32_shr_u(rd, rn, rm),
        WasmOp::I32Rotr => generated::rule_i32_rotr(rd, rn, rm),
        _ => return None,
    })
}

/// Dispatch a binary i64 pair-family op (`add/sub/and/or/xor`) to its
/// generated Rocq-proved rule (increment 3). `None` for ops outside the
/// family (the caller's hand-written arm keeps ownership); `Some(Err(_))`
/// when the register assignment violates a pair aliasing side condition —
/// a loud error, never a silent misassemble.
#[allow(clippy::too_many_arguments)]
pub fn i64_pair_rule(
    op: &WasmOp,
    rd_lo: crate::rules::Reg,
    rd_hi: crate::rules::Reg,
    rn_lo: crate::rules::Reg,
    rn_hi: crate::rules::Reg,
    rm_lo: crate::rules::Reg,
    rm_hi: crate::rules::Reg,
) -> Option<Result<Vec<crate::rules::ArmOp>, &'static str>> {
    Some(match op {
        WasmOp::I64Add => generated::rule_i64_add(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64Sub => generated::rule_i64_sub(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64And => generated::rule_i64_and(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64Or => generated::rule_i64_or(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64Xor => generated::rule_i64_xor(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        _ => return None,
    })
}

/// Render a struct field, using field-init shorthand when the bound variable
/// name matches the field name (keeps the generated file rustfmt/clippy-clean).
fn field(name: &str, var: RegVar) -> String {
    if name == var.rust_name() {
        name.to_string()
    } else {
        format!("{name}: {}", var.rust_name())
    }
}

/// Render an `ArmOp` data-processing constructor whose second operand is
/// `op2: Operand2::Reg(..)`, in the exploded multi-line form rustfmt settles
/// on for these literals (the generated file must be rustfmt-stable so
/// `cargo fmt` never drifts it away from the pinned generator output).
fn dp_reg_expr(op: &str, rd: RegVar, rn: RegVar, rm: RegVar, indent: usize) -> String {
    let ind = " ".repeat(indent);
    let fld = " ".repeat(indent + 4);
    format!(
        "ArmOp::{op} {{\n{fld}{},\n{fld}{},\n{fld}op2: Operand2::Reg({}),\n{ind}}}",
        field("rd", rd),
        field("rn", rn),
        rm.rust_name()
    )
}

/// Render one instruction template as an `ArmOp` constructor expression,
/// starting at column `indent` (continuation lines are indented relative to
/// it). Shapes mirror what rustfmt emits for the equivalent hand-written
/// literal, so the committed file is a rustfmt fixpoint.
fn template_expr(t: &TemplateOp, indent: usize) -> String {
    match *t {
        TemplateOp::AddReg { rd, rn, rm } => dp_reg_expr("Add", rd, rn, rm, indent),
        TemplateOp::SubReg { rd, rn, rm } => dp_reg_expr("Sub", rd, rn, rm, indent),
        TemplateOp::AndReg { rd, rn, rm } => dp_reg_expr("And", rd, rn, rm, indent),
        TemplateOp::OrrReg { rd, rn, rm } => dp_reg_expr("Orr", rd, rn, rm, indent),
        TemplateOp::EorReg { rd, rn, rm } => dp_reg_expr("Eor", rd, rn, rm, indent),
        TemplateOp::AddsReg { rd, rn, rm } => dp_reg_expr("Adds", rd, rn, rm, indent),
        TemplateOp::AdcReg { rd, rn, rm } => dp_reg_expr("Adc", rd, rn, rm, indent),
        TemplateOp::SubsReg { rd, rn, rm } => dp_reg_expr("Subs", rd, rn, rm, indent),
        TemplateOp::SbcReg { rd, rn, rm } => dp_reg_expr("Sbc", rd, rn, rm, indent),
        TemplateOp::I64SetCondZ { rd, rn_lo, rn_hi } => format!(
            "ArmOp::I64SetCondZ {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn_lo", rn_lo),
            field("rn_hi", rn_hi)
        ),
        TemplateOp::Mul { rd, rn, rm } => format!(
            "ArmOp::Mul {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
        TemplateOp::RsbImm { rd, rn, imm } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::Rsb {{\n{fld}{},\n{fld}{},\n{fld}imm: {imm},\n{ind}}}",
                field("rd", rd),
                field("rn", rn)
            )
        }
        TemplateOp::RorReg { rd, rn, rm } => format!(
            "ArmOp::RorReg {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
        TemplateOp::LslReg { rd, rn, rm } => format!(
            "ArmOp::LslReg {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
        TemplateOp::LsrReg { rd, rn, rm } => format!(
            "ArmOp::LsrReg {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
        TemplateOp::AsrReg { rd, rn, rm } => format!(
            "ArmOp::AsrReg {{ {}, {}, {} }}",
            field("rd", rd),
            field("rn", rn),
            field("rm", rm)
        ),
        TemplateOp::CmpReg { rn, rm } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::Cmp {{\n{fld}{},\n{fld}op2: Operand2::Reg({}),\n{ind}}}",
                field("rn", rn),
                rm.rust_name()
            )
        }
        TemplateOp::SetCond { rd, cond } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::SetCond {{\n{fld}{},\n{fld}cond: {},\n{ind}}}",
                field("rd", rd),
                cond.rust_name()
            )
        }
    }
}

/// Generate the Rust source of `generated.rs` from [`RULES`].
///
/// The output is committed to the tree and pinned by
/// [`tests::generated_lowering_is_up_to_date`]; regenerate with
/// `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
pub fn generate_lowering_source() -> String {
    let mut out = String::new();
    out.push_str(
        "//! GENERATED FILE — DO NOT EDIT BY HAND.\n\
         //!\n\
         //! Emitted by `crate::sel_dsl::generate_lowering_source()` from the declarative\n\
         //! rule table [`crate::sel_dsl::RULES`] (VCR-SEL-001 increments 1+2+3, #242,\n\
         //! `docs/design/vcr-sel-001-first-increment.md` +\n\
         //! `docs/design/vcr-sel-001-increment-2.md` +\n\
         //! `docs/design/vcr-sel-001-increment-3.md`). Pinned up-to-date by the\n\
         //! `generated_lowering_is_up_to_date` test; regenerate with\n\
         //! `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.\n\
         //!\n\
         //! Every function here carries a 1:1 Rocq T1 theorem in\n\
         //! `coq/Synth/Synth/VcrSelRules.v` (all Qed — coverage-gated by\n\
         //! `//coq:vcr_sel_rules_coverage`): the emitted sequence computes the op's\n\
         //! result in `rd` (both words of the pair for the i64 pair rules) for EVERY\n\
         //! register assignment satisfying the stated side conditions.\n\n\
         use crate::rules::{ArmOp, Condition, Operand2, Reg};\n",
    );

    for rule in RULES {
        let params: Vec<String> = rule
            .params
            .iter()
            .map(|p| format!("{}: Reg", p.rust_name()))
            .collect();
        let params = params.join(", ");

        out.push('\n');
        out.push_str(&format!("/// {}\n", rule.doc));
        out.push_str("///\n");
        out.push_str(&format!(
            "/// Rocq obligation: `Synth.Synth.VcrSelRules.{}` (Qed).\n",
            rule.theorem()
        ));
        for sc in rule.side_conditions {
            let SideCondition::NotAlias(a, b) = sc;
            out.push_str(&format!(
                "///\n/// Side condition: `{}` must not alias `{}` (hypothesis of the theorem;\n\
                 /// violation is a loud `Err`, never a silent misassemble).\n",
                a.rust_name(),
                b.rust_name()
            ));
        }
        let ret = if rule.side_conditions.is_empty() {
            "Vec<ArmOp>"
        } else {
            "Result<Vec<ArmOp>, &'static str>"
        };
        // Emit the signature in whichever of rustfmt's two shapes it would
        // settle on (the committed file must be a rustfmt fixpoint): one line
        // when it fits max_width, otherwise one parameter per line.
        let one_line = format!("pub fn {}({params}) -> {ret} {{\n", rule.name);
        if one_line.len() <= 101 {
            // <= 100 chars + '\n'
            out.push_str(&one_line);
        } else {
            out.push_str(&format!("pub fn {}(\n", rule.name));
            for p in rule.params {
                out.push_str(&format!("    {}: Reg,\n", p.rust_name()));
            }
            out.push_str(&format!(") -> {ret} {{\n"));
        }
        for sc in rule.side_conditions {
            let SideCondition::NotAlias(a, b) = sc;
            out.push_str(&format!(
                "    if {a} == {b} {{\n        return Err(\"{name}: side condition violated: \
                 {a} must not alias {b}\");\n    }}\n",
                a = a.rust_name(),
                b = b.rust_name(),
                name = rule.name
            ));
        }
        let (open, close) = if rule.side_conditions.is_empty() {
            ("vec![", "]")
        } else {
            ("Ok(vec![", "])")
        };
        if rule.seq.len() == 1 {
            out.push_str(&format!(
                "    {open}{}{close}\n",
                template_expr(&rule.seq[0], 4)
            ));
        } else {
            out.push_str(&format!("    {open}\n"));
            for t in rule.seq {
                out.push_str(&format!("        {},\n", template_expr(t, 8)));
            }
            out.push_str(&format!("    {close}\n"));
        }
        out.push_str("}\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn crate_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    }

    /// The generated file is the committed output of the rule table — any edit
    /// to either without regenerating fails here. Regenerate with
    /// `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
    #[test]
    fn generated_lowering_is_up_to_date() {
        let path = crate_root().join("src/sel_dsl/generated.rs");
        let expected = generate_lowering_source();
        if std::env::var("SYNTH_SEL_DSL_REGEN").is_ok() {
            std::fs::write(&path, &expected).expect("write generated.rs");
        }
        let actual = std::fs::read_to_string(&path).expect("read generated.rs");
        assert_eq!(
            actual, expected,
            "src/sel_dsl/generated.rs is stale relative to the RULES table — \
             regenerate with SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl"
        );
    }

    /// Rule names are unique and follow the `rule_` prefix the 1:1 theorem
    /// naming convention builds on.
    #[test]
    fn rule_names_unique_and_theorem_named() {
        let mut seen = std::collections::HashSet::new();
        for rule in RULES {
            assert!(
                rule.name.starts_with("rule_"),
                "{}: rule names must start with rule_",
                rule.name
            );
            assert!(seen.insert(rule.name), "duplicate rule name {}", rule.name);
            assert_eq!(rule.theorem(), format!("{}_correct", rule.name));
        }
    }

    /// Cargo-side half of the coverage gate: every rule has its 1:1 Rocq
    /// theorem in `coq/Synth/Synth/VcrSelRules.v`, and the file carries no
    /// `Admitted`/`admit.` — so (with the file compiling under
    /// `//coq:verify_proofs`) every rule theorem is Qed.
    #[test]
    fn coq_coverage_every_rule_has_a_qed_theorem() {
        let v_path = crate_root().join("../../coq/Synth/Synth/VcrSelRules.v");
        let v = std::fs::read_to_string(&v_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", v_path.display()));
        for rule in RULES {
            assert!(
                v.contains(&format!("Definition {} ", rule.name)),
                "rule {} has no Definition in VcrSelRules.v",
                rule.name
            );
            assert!(
                v.contains(&format!("Theorem {} ", rule.theorem())),
                "rule {} lacks its theorem {} in VcrSelRules.v — a rule without \
                 a Qed cannot merge",
                rule.name,
                rule.theorem()
            );
        }
        assert!(
            !v.contains("Admitted") && !v.contains("admit."),
            "VcrSelRules.v contains Admitted/admit — every rule theorem must be Qed"
        );
    }

    /// The bazel-side coverage gate (`//coq:vcr_sel_rules_coverage`) reads
    /// `coq/vcr_sel_rules.manifest`; pin the manifest to this table so the
    /// Rust-table ↔ manifest ↔ Coq-theorem chain is closed.
    #[test]
    fn manifest_matches_rule_table() {
        let m_path = crate_root().join("../../coq/vcr_sel_rules.manifest");
        let manifest = std::fs::read_to_string(&m_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", m_path.display()));
        let listed: Vec<&str> = manifest
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .collect();
        let expected: Vec<&str> = RULES.iter().map(|r| r.name).collect();
        assert_eq!(
            listed, expected,
            "coq/vcr_sel_rules.manifest is out of sync with sel_dsl::RULES"
        );
    }

    /// The tier-B side condition is a loud Err, never a silent misassemble.
    #[test]
    fn rotl_side_condition_is_enforced() {
        use crate::rules::Reg;
        // Violating assignment: scratch aliases the value register.
        assert!(generated::rule_i32_rotl(Reg::R0, Reg::R1, Reg::R2, Reg::R1).is_err());
        // Satisfying assignment lowers to RSB scratch + ROR.
        let ops = generated::rule_i32_rotl(Reg::R0, Reg::R1, Reg::R2, Reg::R3).unwrap();
        assert_eq!(ops.len(), 2);
    }

    /// Increment 3: every i64 pair rule enforces all three aliasing side
    /// conditions as a loud Err (the #632 lesson: the rule format must be
    /// able to state "the destination must not be clobbered before use" —
    /// and the generated lowering must refuse an assignment that violates
    /// it, never silently misassemble).
    #[test]
    fn i64_pair_side_conditions_are_enforced() {
        use crate::rules::Reg;
        use synth_core::WasmOp;
        for op in [
            WasmOp::I64Add,
            WasmOp::I64Sub,
            WasmOp::I64And,
            WasmOp::I64Or,
            WasmOp::I64Xor,
        ] {
            // rd_hi aliases rd_lo: the high write destroys the low result.
            assert!(
                i64_pair_rule(&op, Reg::R0, Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4)
                    .unwrap()
                    .is_err(),
                "{op:?}: rd_hi == rd_lo must be rejected"
            );
            // rd_lo aliases rn_hi: the low write clobbers operand 1's high
            // half before the second instruction reads it.
            assert!(
                i64_pair_rule(&op, Reg::R2, Reg::R3, Reg::R1, Reg::R2, Reg::R4, Reg::R5)
                    .unwrap()
                    .is_err(),
                "{op:?}: rd_lo == rn_hi must be rejected"
            );
            // rd_lo aliases rm_hi: same for operand 2.
            assert!(
                i64_pair_rule(&op, Reg::R5, Reg::R6, Reg::R1, Reg::R2, Reg::R4, Reg::R5)
                    .unwrap()
                    .is_err(),
                "{op:?}: rd_lo == rm_hi must be rejected"
            );
            // The in-place shape select_default emits (R0:R1 += R2:R3)
            // satisfies all three and lowers to the two-instruction pair.
            let ops = i64_pair_rule(&op, Reg::R0, Reg::R1, Reg::R0, Reg::R1, Reg::R2, Reg::R3)
                .unwrap()
                .unwrap();
            assert_eq!(ops.len(), 2, "{op:?}: pair rule must emit two instructions");
        }
        // i64.eqz has no side conditions — single-instruction shape.
        let ops = generated::rule_i64_eqz(Reg::R0, Reg::R0, Reg::R1);
        assert_eq!(ops.len(), 1);
    }
}
