//! VCR-SEL-001 increments 1+2+3+4 (#242) — the Rocq-discharged selector rule DSL.
//!
//! Scope: `docs/design/vcr-sel-001-first-increment.md` (increment 1),
//! `docs/design/vcr-sel-001-increment-2.md` (increment 2),
//! `docs/design/vcr-sel-001-increment-3.md` (increment 3) and
//! `docs/design/vcr-sel-001-increment-4.md` (increment 4). This module is the
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
//! - increment 4: the scratch-using and multi-instruction tier the pilot
//!   called out — i32 bit-manipulation (`clz` single-`CLZ`; `ctz` the
//!   TWO-instruction `RBIT rd; CLZ rd, rd` shape with the scratch=dest trick,
//!   no extra register and no side condition; `popcnt` at pseudo-op tier)
//!   plus the binary i64 comparison family (`i64.eq/ne/lt_s/lt_u/gt_s/gt_u/
//!   le_s/le_u/ge_s/ge_u`, the single-`I64SetCond`-pseudo-op shape both
//!   selectors emit — the shape whose encoder expansion is the
//!   CMP-lo/SBCS-hi flags-chain #615 re-implemented on A32; the rules and
//!   theorems live at the pseudo-op tier the flat Rocq executor can express,
//!   see `docs/design/vcr-sel-001-increment-4.md` for the honest bound).
//!
//! The table is turned into plain Rust lowering functions by
//! [`generate_lowering_source`] and the output is **committed to the tree** at
//! [`generated`] (reviewable diffs, no build-time codegen). `select_default`
//! keeps dispatch ownership: a migrated arm delegates to the generated rule
//! behind `SYNTH_SEL_DSL` (default ON since v0.39.0; opt out with SYNTH_NO_SEL_DSL), so OFF ≡ baseline byte-identical by
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

    /// The Coq binder name this variable uses in `VcrSelRules.v`. Identical to
    /// [`RegVar::rust_name`] for the i32 shapes, but the i64 pair binders drop
    /// the underscore (`rd_lo` in Rust is `rdlo` in Coq) — this is the one
    /// spelling difference the Rocq generator must bridge.
    pub const fn coq_name(self) -> &'static str {
        match self {
            RegVar::Rd => "rd",
            RegVar::Rn => "rn",
            RegVar::Rm => "rm",
            RegVar::Rs => "rs",
            RegVar::RdLo => "rdlo",
            RegVar::RdHi => "rdhi",
            RegVar::RnLo => "rnlo",
            RegVar::RnHi => "rnhi",
            RegVar::RmLo => "rmlo",
            RegVar::RmHi => "rmhi",
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

    /// The conditional-`MOV` constructor the i32 `SetCond` shape expands to in
    /// the flat Rocq model (`ArmOp::SetCond` is modeled as
    /// `MOV rd #0; MOV<cc> rd #1`, following the Compilation.v convention).
    const fn coq_movcc(self) -> &'static str {
        match self {
            CondCode::Eq => "MOVEQ",
            CondCode::Ne => "MOVNE",
            CondCode::Lt => "MOVLT",
            CondCode::Lo => "MOVLO",
            CondCode::Gt => "MOVGT",
            CondCode::Hi => "MOVHI",
            CondCode::Le => "MOVLE",
            CondCode::Ls => "MOVLS",
            CondCode::Ge => "MOVGE",
            CondCode::Hs => "MOVHS",
        }
    }

    /// The `condition` constructor the i64 `I64SetCond` pseudo-op carries in
    /// the Rocq model. Note the unsigned codes map to the carry-flag names the
    /// ARM model uses: `Lo` (LO) is `Cond_CC`, `Hs` (HS) is `Cond_CS`.
    const fn coq_condition(self) -> &'static str {
        match self {
            CondCode::Eq => "Cond_EQ",
            CondCode::Ne => "Cond_NE",
            CondCode::Lt => "Cond_LT",
            CondCode::Lo => "Cond_CC",
            CondCode::Gt => "Cond_GT",
            CondCode::Hi => "Cond_HI",
            CondCode::Le => "Cond_LE",
            CondCode::Ls => "Cond_LS",
            CondCode::Ge => "Cond_GE",
            CondCode::Hs => "Cond_CS",
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
    /// `ArmOp::And { rd, rn, op2: Imm(imm) }` — `rd = rn & imm` (#682 mask)
    AndImm { rd: RegVar, rn: RegVar, imm: u32 },
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
    /// `ArmOp::Cmp { rn, op2: Imm(imm) }` — flags only, no register written
    /// (the `i32.eqz` compare-with-zero shape)
    CmpImm { rn: RegVar, imm: u32 },
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
    /// `ArmOp::Clz { rd, rm }` — count leading zeros
    Clz { rd: RegVar, rm: RegVar },
    /// `ArmOp::Rbit { rd, rm }` — reverse bits (the ctz shape's first step)
    Rbit { rd: RegVar, rm: RegVar },
    /// `ArmOp::Popcnt { rd, rm }` — population-count pseudo-op (encoder-expanded)
    Popcnt { rd: RegVar, rm: RegVar },
    /// `ArmOp::I64SetCond { rd, rn_lo, rn_hi, rm_lo, rm_hi, cond }` —
    /// rd = if (rn_hi:rn_lo) <cond> (rm_hi:rm_lo) {1} else {0}
    I64SetCond {
        rd: RegVar,
        rn_lo: RegVar,
        rn_hi: RegVar,
        rm_lo: RegVar,
        rm_hi: RegVar,
        cond: CondCode,
    },
    /// The single-pseudo-op i64 register-pair binary shapes
    /// (`I64Mul` / `I64Shl` / `I64ShrU` / `I64ShrS`). Each is ONE ArmOp that
    /// reads all four operand halves into locals BEFORE writing the (lo, hi)
    /// destination pair, so — unlike the increment-3 ADDS+ADC pair rules — the
    /// only aliasing constraint is `rd_hi <> rd_lo` (the high write must not
    /// destroy the low result word). Modeled by the corresponding
    /// `I64{Mul,Shl,ShrU,ShrS}Pseudo` constructor in the flat ARM model.
    I64PairBin {
        kind: I64PairBinKind,
        rd_lo: RegVar,
        rd_hi: RegVar,
        rn_lo: RegVar,
        rn_hi: RegVar,
        rm_lo: RegVar,
        rm_hi: RegVar,
    },
    /// The single-pseudo-op i64 rotate shapes (`I64Rotl` / `I64Rotr`). Like
    /// [`TemplateOp::I64PairBin`] but the rotate amount is a SINGLE register
    /// (`shift`, the low half of the i64 amount), matching the flat model's
    /// `I64{Rotl,Rotr}Pseudo` (5-register) constructor. Only aliasing
    /// constraint: `rd_hi <> rd_lo`.
    I64PairRot {
        left: bool,
        rd_lo: RegVar,
        rd_hi: RegVar,
        rn_lo: RegVar,
        rn_hi: RegVar,
        shift: RegVar,
    },
    /// The single-pseudo-op i64 unary bit-count shapes (`I64Clz` / `I64Ctz` /
    /// `I64Popcnt`). One ArmOp reads both operand halves and writes the single
    /// i32 count into `rd` — NO aliasing side condition (`rd` may alias `rn_lo`,
    /// the `R0, R0, R1` shape the selector emits). Modeled by the corresponding
    /// `I64{Clz,Ctz,Popcnt}Pseudo` constructor.
    I64UnaryCount {
        kind: I64CountKind,
        rd: RegVar,
        rn_lo: RegVar,
        rn_hi: RegVar,
    },
}

/// The binary i64 register-pair pseudo-op families that share the
/// [`TemplateOp::I64PairBin`] shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum I64PairBinKind {
    Mul,
    Shl,
    ShrU,
    ShrS,
}

/// The unary i64 bit-count pseudo-op families that share the
/// [`TemplateOp::I64UnaryCount`] shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum I64CountKind {
    Clz,
    Ctz,
    Popcnt,
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

/// The parameter order shared by every binary `I64SetCond` comparison rule
/// (increment 4): the single i32 result register plus the two operand pairs.
/// NO side conditions — the pseudo-op reads all four operand halves before
/// writing `rd`, so every aliasing is admitted by the universal quantifier.
const I64_SETCOND_PARAMS: &[RegVar] = &[Rd, RnLo, RnHi, RmLo, RmHi];

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
        params: &[Rd, Rn, Rm, Rs],
        side_conditions: &[SideCondition::NotAlias(Rs, Rn)],
        seq: &[
            TemplateOp::AndImm {
                rd: Rs,
                rn: Rm,
                imm: 31,
            },
            TemplateOp::LslReg {
                rd: Rd,
                rn: Rn,
                rm: Rs,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i32.shl`: rd = rn << (rm mod 32) — #682 mask via scratch rs",
    },
    SelRule {
        name: "rule_i32_shr_s",
        op: WasmOp::I32ShrS,
        params: &[Rd, Rn, Rm, Rs],
        side_conditions: &[SideCondition::NotAlias(Rs, Rn)],
        seq: &[
            TemplateOp::AndImm {
                rd: Rs,
                rn: Rm,
                imm: 31,
            },
            TemplateOp::AsrReg {
                rd: Rd,
                rn: Rn,
                rm: Rs,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i32.shr_s`: rd = rn >> (rm mod 32) (arithmetic) — #682 mask via scratch rs",
    },
    SelRule {
        name: "rule_i32_shr_u",
        op: WasmOp::I32ShrU,
        params: &[Rd, Rn, Rm, Rs],
        side_conditions: &[SideCondition::NotAlias(Rs, Rn)],
        seq: &[
            TemplateOp::AndImm {
                rd: Rs,
                rn: Rm,
                imm: 31,
            },
            TemplateOp::LsrReg {
                rd: Rd,
                rn: Rn,
                rm: Rs,
            },
        ],
        delegation: Delegation::Both,
        doc: "`i32.shr_u`: rd = rn >> (rm mod 32) (logical) — #682 mask via scratch rs",
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
    // i32.eqz — the unary compare-with-zero shape: CMP rn, #0; SetCond rd, EQ.
    // Same tier as the i32 comparisons (CMP latches NZCV before SetCond writes
    // rd, so NO aliasing side conditions), and the same holdout story:
    // select_default's I32Eqz arm is a *blind* bare-Cmp that never
    // materializes the 0/1 result (production-unreachable — select_with_stack
    // owns eqz), so this rule is delegated in select_with_stack ONLY.
    SelRule {
        name: "rule_i32_eqz",
        op: WasmOp::I32Eqz,
        params: &[Rd, Rn],
        side_conditions: &[],
        seq: &[
            TemplateOp::CmpImm { rn: Rn, imm: 0 },
            TemplateOp::SetCond {
                rd: Rd,
                cond: CondCode::Eq,
            },
        ],
        delegation: Delegation::SelectWithStack,
        doc: "`i32.eqz`: rd = if rn == 0 {1} else {0}",
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
    // ---- increment 4: i32 bit manipulation. `clz` is single-instruction
    // tier A; `ctz` is the TWO-instruction RBIT+CLZ shape with the
    // scratch=dest trick (instruction 1 writes the bit-reversed value into
    // rd itself, instruction 2 reads it back — no extra scratch register
    // and NO side condition: RBIT reads rm before writing rd, and the
    // second instruction only reads rd); `popcnt` is pseudo-op-tier (the
    // rule mirrors the single ArmOp::Popcnt the selector emits; the
    // encoder's shift-and-add expansion below the ArmOp boundary is
    // outside the Rocq model — same honest tier as i64.eqz/I64SetCond). ----
    SelRule {
        name: "rule_i32_clz",
        op: WasmOp::I32Clz,
        params: &[Rd, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::Clz { rd: Rd, rm: Rm }],
        delegation: Delegation::Both,
        doc: "`i32.clz`: rd = count of leading zero bits of rm",
    },
    SelRule {
        name: "rule_i32_ctz",
        op: WasmOp::I32Ctz,
        params: &[Rd, Rm],
        side_conditions: &[],
        seq: &[
            TemplateOp::Rbit { rd: Rd, rm: Rm },
            TemplateOp::Clz { rd: Rd, rm: Rd },
        ],
        delegation: Delegation::Both,
        doc: "`i32.ctz`: rd = count of trailing zero bits of rm, via RBIT + CLZ (scratch=dest)",
    },
    SelRule {
        name: "rule_i32_popcnt",
        op: WasmOp::I32Popcnt,
        params: &[Rd, Rm],
        side_conditions: &[],
        seq: &[TemplateOp::Popcnt { rd: Rd, rm: Rm }],
        delegation: Delegation::Both,
        doc: "`i32.popcnt`: rd = count of set bits of rm (pseudo-op, encoder-expanded)",
    },
    // ---- increment 4: the binary i64 comparison family — the
    // single-I64SetCond-pseudo-op shape BOTH selectors emit (the pseudo-op
    // whose encoder expansion is the CMP-lo/SBCS-hi dual-precision
    // flags-chain, with the GT/LE/HI/LS operand swap — the #615 A32 shape
    // where cond-mapping bugs live). The rules and their theorems are
    // pseudo-op-tier T1 against the i64_setcond_bits_spec axiom; the
    // expansion itself is below what the flat Rocq executor can express
    // (no SBCS, no conditional CMP — see
    // docs/design/vcr-sel-001-increment-4.md). No side conditions: the
    // pseudo-op reads all four operand halves before writing rd. ----
    SelRule {
        name: "rule_i64_eq",
        op: WasmOp::I64Eq,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Eq,
        }],
        delegation: Delegation::Both,
        doc: "`i64.eq`: rd = if (rn_hi:rn_lo) == (rm_hi:rm_lo) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_ne",
        op: WasmOp::I64Ne,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Ne,
        }],
        delegation: Delegation::Both,
        doc: "`i64.ne`: rd = if (rn_hi:rn_lo) != (rm_hi:rm_lo) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_lt_s",
        op: WasmOp::I64LtS,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Lt,
        }],
        delegation: Delegation::Both,
        doc: "`i64.lt_s`: rd = if (rn_hi:rn_lo) < (rm_hi:rm_lo) (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_lt_u",
        op: WasmOp::I64LtU,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Lo,
        }],
        delegation: Delegation::Both,
        doc: "`i64.lt_u`: rd = if (rn_hi:rn_lo) < (rm_hi:rm_lo) (unsigned) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_gt_s",
        op: WasmOp::I64GtS,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Gt,
        }],
        delegation: Delegation::Both,
        doc: "`i64.gt_s`: rd = if (rn_hi:rn_lo) > (rm_hi:rm_lo) (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_gt_u",
        op: WasmOp::I64GtU,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Hi,
        }],
        delegation: Delegation::Both,
        doc: "`i64.gt_u`: rd = if (rn_hi:rn_lo) > (rm_hi:rm_lo) (unsigned) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_le_s",
        op: WasmOp::I64LeS,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Le,
        }],
        delegation: Delegation::Both,
        doc: "`i64.le_s`: rd = if (rn_hi:rn_lo) <= (rm_hi:rm_lo) (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_le_u",
        op: WasmOp::I64LeU,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Ls,
        }],
        delegation: Delegation::Both,
        doc: "`i64.le_u`: rd = if (rn_hi:rn_lo) <= (rm_hi:rm_lo) (unsigned) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_ge_s",
        op: WasmOp::I64GeS,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Ge,
        }],
        delegation: Delegation::Both,
        doc: "`i64.ge_s`: rd = if (rn_hi:rn_lo) >= (rm_hi:rm_lo) (signed) {1} else {0}",
    },
    SelRule {
        name: "rule_i64_ge_u",
        op: WasmOp::I64GeU,
        params: I64_SETCOND_PARAMS,
        side_conditions: &[],
        seq: &[TemplateOp::I64SetCond {
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
            cond: CondCode::Hs,
        }],
        delegation: Delegation::Both,
        doc: "`i64.ge_u`: rd = if (rn_hi:rn_lo) >= (rm_hi:rm_lo) (unsigned) {1} else {0}",
    },
    // ---- VCR-ISA-001 wave-2 (v0.45): the single-pseudo-op i64 register-pair
    // shapes the selector already emits but were DSL-uncovered. Each is ONE
    // ArmOp modeled by a dedicated flat-model pseudo-op
    // (I64{Clz,Ctz,Popcnt,Mul,Shl,ShrU,ShrS,Rotl,Rotr}Pseudo), with a
    // fixed-register ancestor in CorrectnessI64.v — so the DSL rule is a pure
    // register-generalization + re-export, exactly like the increment-3/4
    // i64.eqz / I64SetCond families. ----
    //
    // i64.clz / i64.ctz / i64.popcnt — unary bit counts: ONE pseudo-op reads
    // both operand halves and writes the single i32 count into `rd`. NO
    // aliasing side condition (the pseudo-op reads rn_lo/rn_hi before writing
    // rd, so the selector's `rd = rn_lo = R0` in-place emit is admitted).
    SelRule {
        name: "rule_i64_clz",
        op: WasmOp::I64Clz,
        params: &[Rd, RnLo, RnHi],
        side_conditions: &[],
        seq: &[TemplateOp::I64UnaryCount {
            kind: I64CountKind::Clz,
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.clz`: rd = count-leading-zeros of (rn_hi:rn_lo), as i32",
    },
    SelRule {
        name: "rule_i64_ctz",
        op: WasmOp::I64Ctz,
        params: &[Rd, RnLo, RnHi],
        side_conditions: &[],
        seq: &[TemplateOp::I64UnaryCount {
            kind: I64CountKind::Ctz,
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.ctz`: rd = count-trailing-zeros of (rn_hi:rn_lo), as i32",
    },
    SelRule {
        name: "rule_i64_popcnt",
        op: WasmOp::I64Popcnt,
        params: &[Rd, RnLo, RnHi],
        side_conditions: &[],
        seq: &[TemplateOp::I64UnaryCount {
            kind: I64CountKind::Popcnt,
            rd: Rd,
            rn_lo: RnLo,
            rn_hi: RnHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.popcnt`: rd = population-count of (rn_hi:rn_lo), as i32",
    },
    // i64.mul / i64.shl / i64.shr_u / i64.shr_s — binary register-pair shapes:
    // ONE pseudo-op reads all four operand halves BEFORE writing the (lo, hi)
    // destination pair, so the only aliasing constraint is `rd_hi <> rd_lo`.
    SelRule {
        name: "rule_i64_mul",
        op: WasmOp::I64Mul,
        params: I64_PAIR_PARAMS,
        side_conditions: &[SideCondition::NotAlias(RdHi, RdLo)],
        seq: &[TemplateOp::I64PairBin {
            kind: I64PairBinKind::Mul,
            rd_lo: RdLo,
            rd_hi: RdHi,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.mul`: (rd_hi:rd_lo) = (rn_hi:rn_lo) * (rm_hi:rm_lo)",
    },
    SelRule {
        name: "rule_i64_shl",
        op: WasmOp::I64Shl,
        params: I64_PAIR_PARAMS,
        side_conditions: &[SideCondition::NotAlias(RdHi, RdLo)],
        seq: &[TemplateOp::I64PairBin {
            kind: I64PairBinKind::Shl,
            rd_lo: RdLo,
            rd_hi: RdHi,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.shl`: (rd_hi:rd_lo) = (rn_hi:rn_lo) << (rm_lo mod 64)",
    },
    SelRule {
        name: "rule_i64_shr_u",
        op: WasmOp::I64ShrU,
        params: I64_PAIR_PARAMS,
        side_conditions: &[SideCondition::NotAlias(RdHi, RdLo)],
        seq: &[TemplateOp::I64PairBin {
            kind: I64PairBinKind::ShrU,
            rd_lo: RdLo,
            rd_hi: RdHi,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.shr_u`: (rd_hi:rd_lo) = (rn_hi:rn_lo) >> (rm_lo mod 64) (logical)",
    },
    SelRule {
        name: "rule_i64_shr_s",
        op: WasmOp::I64ShrS,
        params: I64_PAIR_PARAMS,
        side_conditions: &[SideCondition::NotAlias(RdHi, RdLo)],
        seq: &[TemplateOp::I64PairBin {
            kind: I64PairBinKind::ShrS,
            rd_lo: RdLo,
            rd_hi: RdHi,
            rn_lo: RnLo,
            rn_hi: RnHi,
            rm_lo: RmLo,
            rm_hi: RmHi,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.shr_s`: (rd_hi:rd_lo) = (rn_hi:rn_lo) >> (rm_lo mod 64) (arithmetic)",
    },
    // i64.rotl / i64.rotr — rotate shapes: the amount is a SINGLE register
    // (`shift`, the low half of the i64 amount). Only aliasing constraint:
    // `rd_hi <> rd_lo`.
    SelRule {
        name: "rule_i64_rotl",
        op: WasmOp::I64Rotl,
        params: &[RdLo, RdHi, RnLo, RnHi, RmLo],
        side_conditions: &[SideCondition::NotAlias(RdHi, RdLo)],
        seq: &[TemplateOp::I64PairRot {
            left: true,
            rd_lo: RdLo,
            rd_hi: RdHi,
            rn_lo: RnLo,
            rn_hi: RnHi,
            shift: RmLo,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.rotl`: (rd_hi:rd_lo) = (rn_hi:rn_lo) rotate-left (shift mod 64)",
    },
    SelRule {
        name: "rule_i64_rotr",
        op: WasmOp::I64Rotr,
        params: &[RdLo, RdHi, RnLo, RnHi, RmLo],
        side_conditions: &[SideCondition::NotAlias(RdHi, RdLo)],
        seq: &[TemplateOp::I64PairRot {
            left: false,
            rd_lo: RdLo,
            rd_hi: RdHi,
            rn_lo: RnLo,
            rn_hi: RnHi,
            shift: RmLo,
        }],
        delegation: Delegation::SelectWithStack,
        doc: "`i64.rotr`: (rd_hi:rd_lo) = (rn_hi:rn_lo) rotate-right (shift mod 64)",
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

/// Dispatch `i32.eqz` (unary compare-with-zero) to its generated Rocq-proved
/// rule. Same contract as [`i32_cmp_rule`]: `None` for any other op so the
/// caller's hand-written arm keeps ownership; no side conditions, so infallible
/// where it fires.
pub fn i32_eqz_rule(
    op: &WasmOp,
    rd: crate::rules::Reg,
    rn: crate::rules::Reg,
) -> Option<Vec<crate::rules::ArmOp>> {
    Some(match op {
        WasmOp::I32Eqz => generated::rule_i32_eqz(rd, rn),
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
    rs: crate::rules::Reg,
) -> Option<Result<Vec<crate::rules::ArmOp>, &'static str>> {
    Some(match op {
        WasmOp::I32Shl => generated::rule_i32_shl(rd, rn, rm, rs),
        WasmOp::I32ShrS => generated::rule_i32_shr_s(rd, rn, rm, rs),
        WasmOp::I32ShrU => generated::rule_i32_shr_u(rd, rn, rm, rs),
        WasmOp::I32Rotr => Ok(generated::rule_i32_rotr(rd, rn, rm)),
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

/// Dispatch an i32 unary bit-manipulation op (`clz/ctz/popcnt`) to its
/// generated Rocq-proved rule (increment 4). Same contract as
/// [`i32_cmp_rule`]: `None` for ops outside the family so the caller's
/// hand-written arm keeps ownership.
pub fn i32_unary_rule(
    op: &WasmOp,
    rd: crate::rules::Reg,
    rm: crate::rules::Reg,
) -> Option<Vec<crate::rules::ArmOp>> {
    Some(match op {
        WasmOp::I32Clz => generated::rule_i32_clz(rd, rm),
        WasmOp::I32Ctz => generated::rule_i32_ctz(rd, rm),
        WasmOp::I32Popcnt => generated::rule_i32_popcnt(rd, rm),
        _ => return None,
    })
}

/// Dispatch a binary i64 comparison op to its generated Rocq-proved
/// `I64SetCond` rule (increment 4). Same contract as [`i32_cmp_rule`]; no
/// side conditions (the pseudo-op reads all four operand halves before
/// writing `rd`), so the return is infallible where it fires.
pub fn i64_setcond_rule(
    op: &WasmOp,
    rd: crate::rules::Reg,
    rn_lo: crate::rules::Reg,
    rn_hi: crate::rules::Reg,
    rm_lo: crate::rules::Reg,
    rm_hi: crate::rules::Reg,
) -> Option<Vec<crate::rules::ArmOp>> {
    Some(match op {
        WasmOp::I64Eq => generated::rule_i64_eq(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64Ne => generated::rule_i64_ne(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64LtS => generated::rule_i64_lt_s(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64LtU => generated::rule_i64_lt_u(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64GtS => generated::rule_i64_gt_s(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64GtU => generated::rule_i64_gt_u(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64LeS => generated::rule_i64_le_s(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64LeU => generated::rule_i64_le_u(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64GeS => generated::rule_i64_ge_s(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64GeU => generated::rule_i64_ge_u(rd, rn_lo, rn_hi, rm_lo, rm_hi),
        _ => return None,
    })
}

/// Dispatch a unary i64 bit-count op (`i64.clz/ctz/popcnt`) to its generated
/// Rocq-proved single-pseudo-op rule (VCR-ISA-001 wave-2). Same contract as
/// [`i32_unary_rule`]: `None` for ops outside the family; no side conditions
/// (the pseudo-op reads both operand halves before writing `rd`).
pub fn i64_unary_count_rule(
    op: &WasmOp,
    rd: crate::rules::Reg,
    rn_lo: crate::rules::Reg,
    rn_hi: crate::rules::Reg,
) -> Option<Vec<crate::rules::ArmOp>> {
    Some(match op {
        WasmOp::I64Clz => generated::rule_i64_clz(rd, rn_lo, rn_hi),
        WasmOp::I64Ctz => generated::rule_i64_ctz(rd, rn_lo, rn_hi),
        WasmOp::I64Popcnt => generated::rule_i64_popcnt(rd, rn_lo, rn_hi),
        _ => return None,
    })
}

/// Dispatch a binary i64 register-pair op (`i64.mul/shl/shr_u/shr_s`) to its
/// generated Rocq-proved single-pseudo-op rule (VCR-ISA-001 wave-2). Each
/// carries the single `rd_hi <> rd_lo` side condition (the high write must not
/// destroy the low result word); violation is a loud `Err`.
pub fn i64_pair_bin_rule(
    op: &WasmOp,
    rd_lo: crate::rules::Reg,
    rd_hi: crate::rules::Reg,
    rn_lo: crate::rules::Reg,
    rn_hi: crate::rules::Reg,
    rm_lo: crate::rules::Reg,
    rm_hi: crate::rules::Reg,
) -> Option<Result<Vec<crate::rules::ArmOp>, &'static str>> {
    Some(match op {
        WasmOp::I64Mul => generated::rule_i64_mul(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64Shl => generated::rule_i64_shl(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64ShrU => generated::rule_i64_shr_u(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        WasmOp::I64ShrS => generated::rule_i64_shr_s(rd_lo, rd_hi, rn_lo, rn_hi, rm_lo, rm_hi),
        _ => return None,
    })
}

/// Dispatch an i64 rotate op (`i64.rotl/rotr`) to its generated Rocq-proved
/// single-pseudo-op rule (VCR-ISA-001 wave-2). The rotate amount is a SINGLE
/// register (`shift`, the low half of the i64 amount). Single `rd_hi <> rd_lo`
/// side condition; violation is a loud `Err`.
pub fn i64_rot_rule(
    op: &WasmOp,
    rd_lo: crate::rules::Reg,
    rd_hi: crate::rules::Reg,
    rn_lo: crate::rules::Reg,
    rn_hi: crate::rules::Reg,
    shift: crate::rules::Reg,
) -> Option<Result<Vec<crate::rules::ArmOp>, &'static str>> {
    Some(match op {
        WasmOp::I64Rotl => generated::rule_i64_rotl(rd_lo, rd_hi, rn_lo, rn_hi, shift),
        WasmOp::I64Rotr => generated::rule_i64_rotr(rd_lo, rd_hi, rn_lo, rn_hi, shift),
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
        TemplateOp::Clz { rd, rm } => {
            format!("ArmOp::Clz {{ {}, {} }}", field("rd", rd), field("rm", rm))
        }
        TemplateOp::Rbit { rd, rm } => {
            format!("ArmOp::Rbit {{ {}, {} }}", field("rd", rd), field("rm", rm))
        }
        TemplateOp::Popcnt { rd, rm } => format!(
            "ArmOp::Popcnt {{ {}, {} }}",
            field("rd", rd),
            field("rm", rm)
        ),
        TemplateOp::I64SetCond {
            rd,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
            cond,
        } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::I64SetCond {{\n{fld}{},\n{fld}{},\n{fld}{},\n{fld}{},\n{fld}{},\n\
                 {fld}cond: {},\n{ind}}}",
                field("rd", rd),
                field("rn_lo", rn_lo),
                field("rn_hi", rn_hi),
                field("rm_lo", rm_lo),
                field("rm_hi", rm_hi),
                cond.rust_name()
            )
        }
        TemplateOp::I64PairBin {
            kind,
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        } => {
            let variant = match kind {
                I64PairBinKind::Mul => "I64Mul",
                I64PairBinKind::Shl => "I64Shl",
                I64PairBinKind::ShrU => "I64ShrU",
                I64PairBinKind::ShrS => "I64ShrS",
            };
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::{variant} {{\n{fld}{},\n{fld}{},\n{fld}{},\n{fld}{},\n{fld}{},\n\
                 {fld}{},\n{ind}}}",
                field("rd_lo", rd_lo),
                field("rd_hi", rd_hi),
                field("rn_lo", rn_lo),
                field("rn_hi", rn_hi),
                field("rm_lo", rm_lo),
                field("rm_hi", rm_hi),
            )
        }
        TemplateOp::I64PairRot {
            left,
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            shift,
        } => {
            let variant = if left { "I64Rotl" } else { "I64Rotr" };
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::{variant} {{\n{fld}{},\n{fld}{},\n{fld}{},\n{fld}{},\n{fld}{},\n{ind}}}",
                field("rdlo", rd_lo),
                field("rdhi", rd_hi),
                field("rnlo", rn_lo),
                field("rnhi", rn_hi),
                field("shift", shift),
            )
        }
        TemplateOp::I64UnaryCount {
            kind,
            rd,
            rn_lo,
            rn_hi,
        } => {
            let variant = match kind {
                I64CountKind::Clz => "I64Clz",
                I64CountKind::Ctz => "I64Ctz",
                I64CountKind::Popcnt => "I64Popcnt",
            };
            // The ArmOp field names (`rnlo`/`rnhi`) differ from the RegVar
            // rust_names (`rn_lo`/`rn_hi`), so the fields render as
            // `rnlo: rn_lo` (not shorthand) — rustfmt explodes the literal, so
            // emit the exploded multi-line form directly to stay a fixpoint.
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::{variant} {{\n{fld}{},\n{fld}{},\n{fld}{},\n{ind}}}",
                field("rd", rd),
                field("rnlo", rn_lo),
                field("rnhi", rn_hi),
            )
        }
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
        TemplateOp::AndImm { rd, rn, imm } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::And {{\n{fld}{},\n{fld}{},\n{fld}op2: Operand2::Imm({imm}),\n{ind}}}",
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
        TemplateOp::CmpImm { rn, imm } => {
            let ind = " ".repeat(indent);
            let fld = " ".repeat(indent + 4);
            format!(
                "ArmOp::Cmp {{\n{fld}{},\n{fld}op2: Operand2::Imm({imm}),\n{ind}}}",
                field("rn", rn)
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
         //! rule table [`crate::sel_dsl::RULES`] (VCR-SEL-001 increments 1+2+3+4, #242,\n\
         //! `docs/design/vcr-sel-001-first-increment.md` +\n\
         //! `docs/design/vcr-sel-001-increment-2.md` +\n\
         //! `docs/design/vcr-sel-001-increment-3.md` +\n\
         //! `docs/design/vcr-sel-001-increment-4.md`). Pinned up-to-date by the\n\
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
        // rustfmt collapses a multi-element `vec![..]` onto one line when it
        // fits max_width and every element is itself single-line — mirror
        // that so the committed file stays a rustfmt fixpoint.
        let one_line_body: Vec<String> = rule.seq.iter().map(|t| template_expr(t, 4)).collect();
        let one_line = format!("    {open}{}{close}\n", one_line_body.join(", "));
        // `one_line` is single-line iff its only '\n' is the trailing one
        // (an element with an exploded rendering embeds more).
        let fits_one_line = one_line.matches('\n').count() == 1 && one_line.len() <= 101;
        if rule.seq.len() == 1 {
            out.push_str(&format!(
                "    {open}{}{close}\n",
                template_expr(&rule.seq[0], 4)
            ));
        } else if fits_one_line {
            out.push_str(&one_line);
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

// ─── VCR-ISA-001 (#667): generate the Rocq model from the shipped selector ────
//
// The function below turns the SAME [`RULES`] table into the Rocq lowering
// `Definition`s that `coq/Synth/Synth/VcrSelRules.v` proves correct. The
// generated `Module Gen` (`VcrSelRulesGenerated.v`) is the SINGLE SOURCE of
// those definitions: `VcrSelRules.v` re-exports them (`Definition rule_X :=
// Gen.rule_X`) and states the 40 correctness theorems directly about them —
// there is no hand-written copy of the sequences left to diverge from the
// shipped selector (the #682 vacuous-proof incident: a Qed certified a
// hardware-wrong program because the model had drifted; the
// `//coq:vcr_sel_rules_coverage` gate only pins the rule NAMES).
//
// The divergence gate is Coq's kernel — not a Rust text normalizer — so the
// fiddly spots (the `SetCond` → two-instruction expansion, the i32 `MOV<cc>`
// vs i64 `Cond_*` mapping) cannot hide a false green: change `RULES`,
// regenerate, and the matching correctness Qed in `VcrSelRules.v` stops
// compiling under `//coq:verify_proofs`. (The former `VcrSelRulesGenCheck.v`
// reflexivity cross-check compared `Gen.rule_X` against a hand-written mirror;
// with the mirror gone it is subsumed by the correctness proofs themselves.)
// The `.v` artifact is committed and pinned up-to-date by the tests below.

/// Render one [`TemplateOp`] as the Coq `arm_instr` term(s) it denotes. A
/// `SetCond` expands to the TWO-instruction `MOV rd #0; MOV<cc> rd #1` shape
/// the flat model uses; every other shape is a single instruction.
fn coq_instrs(t: &TemplateOp) -> Vec<String> {
    let r = |v: RegVar| v.coq_name();
    match *t {
        TemplateOp::AddReg { rd, rn, rm } => {
            vec![format!("ADD {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::SubReg { rd, rn, rm } => {
            vec![format!("SUB {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::Mul { rd, rn, rm } => vec![format!("MUL {} {} {}", r(rd), r(rn), r(rm))],
        TemplateOp::AndReg { rd, rn, rm } => {
            vec![format!("AND {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::OrrReg { rd, rn, rm } => {
            vec![format!("ORR {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::EorReg { rd, rn, rm } => {
            vec![format!("EOR {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::RsbImm { rd, rn, imm } => {
            vec![format!("RSB {} {} (Imm (I32.repr {}))", r(rd), r(rn), imm)]
        }
        TemplateOp::AndImm { rd, rn, imm } => {
            vec![format!("AND {} {} (Imm (I32.repr {}))", r(rd), r(rn), imm)]
        }
        TemplateOp::RorReg { rd, rn, rm } => {
            vec![format!("ROR_reg {} {} {}", r(rd), r(rn), r(rm))]
        }
        TemplateOp::LslReg { rd, rn, rm } => {
            vec![format!("LSL_reg {} {} {}", r(rd), r(rn), r(rm))]
        }
        TemplateOp::LsrReg { rd, rn, rm } => {
            vec![format!("LSR_reg {} {} {}", r(rd), r(rn), r(rm))]
        }
        TemplateOp::AsrReg { rd, rn, rm } => {
            vec![format!("ASR_reg {} {} {}", r(rd), r(rn), r(rm))]
        }
        TemplateOp::CmpReg { rn, rm } => vec![format!("CMP {} (Reg {})", r(rn), r(rm))],
        // The compare-with-zero shape models the immediate as [I32.zero]
        // (definitionally [I32.repr 0]) to match the flat model's I32Eqz
        // lowering and the [z_flag_sub_eq] flag lemma verbatim.
        TemplateOp::CmpImm { rn, imm } => {
            let operand = if imm == 0 {
                "I32.zero".to_string()
            } else {
                format!("(I32.repr {imm})")
            };
            vec![format!("CMP {} (Imm {operand})", r(rn))]
        }
        TemplateOp::SetCond { rd, cond } => vec![
            format!("MOV {} (Imm I32.zero)", r(rd)),
            format!("{} {} (Imm I32.one)", cond.coq_movcc(), r(rd)),
        ],
        TemplateOp::AddsReg { rd, rn, rm } => {
            vec![format!("ADDS {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::AdcReg { rd, rn, rm } => {
            vec![format!("ADC {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::SubsReg { rd, rn, rm } => {
            vec![format!("SUBS {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::SbcReg { rd, rn, rm } => {
            vec![format!("SBC {} {} (Reg {})", r(rd), r(rn), r(rm))]
        }
        TemplateOp::I64SetCondZ { rd, rn_lo, rn_hi } => {
            vec![format!("I64SetCondZ {} {} {}", r(rd), r(rn_lo), r(rn_hi))]
        }
        TemplateOp::Clz { rd, rm } => vec![format!("CLZ {} {}", r(rd), r(rm))],
        TemplateOp::Rbit { rd, rm } => vec![format!("RBIT {} {}", r(rd), r(rm))],
        TemplateOp::Popcnt { rd, rm } => vec![format!("POPCNT {} {}", r(rd), r(rm))],
        TemplateOp::I64SetCond {
            rd,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
            cond,
        } => vec![format!(
            "I64SetCond {} {} {} {} {} {}",
            r(rd),
            r(rn_lo),
            r(rn_hi),
            r(rm_lo),
            r(rm_hi),
            cond.coq_condition()
        )],
        TemplateOp::I64PairBin {
            kind,
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        } => {
            let ctor = match kind {
                I64PairBinKind::Mul => "I64MulPseudo",
                I64PairBinKind::Shl => "I64ShlPseudo",
                I64PairBinKind::ShrU => "I64ShrUPseudo",
                I64PairBinKind::ShrS => "I64ShrSPseudo",
            };
            vec![format!(
                "{ctor} {} {} {} {} {} {}",
                r(rd_lo),
                r(rd_hi),
                r(rn_lo),
                r(rn_hi),
                r(rm_lo),
                r(rm_hi)
            )]
        }
        TemplateOp::I64PairRot {
            left,
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            shift,
        } => {
            let ctor = if left {
                "I64RotlPseudo"
            } else {
                "I64RotrPseudo"
            };
            vec![format!(
                "{ctor} {} {} {} {} {}",
                r(rd_lo),
                r(rd_hi),
                r(rn_lo),
                r(rn_hi),
                r(shift)
            )]
        }
        TemplateOp::I64UnaryCount {
            kind,
            rd,
            rn_lo,
            rn_hi,
        } => {
            let ctor = match kind {
                I64CountKind::Clz => "I64ClzPseudo",
                I64CountKind::Ctz => "I64CtzPseudo",
                I64CountKind::Popcnt => "I64PopcntPseudo",
            };
            vec![format!("{ctor} {} {} {}", r(rd), r(rn_lo), r(rn_hi))]
        }
    }
}

/// Emit the Coq `Definition <name> (<binders> : arm_reg) : arm_program := [..].`
/// for one rule — the register-polymorphic ARM sequence the shipped selector
/// emits, as it appears inside `Module Gen` of the generated
/// `VcrSelRulesGenerated.v` (the single source `VcrSelRules.v` re-exports).
pub fn emit_rocq_definition(rule: &SelRule) -> String {
    let binders: Vec<&str> = rule.params.iter().map(|p| p.coq_name()).collect();
    let instrs: Vec<String> = rule.seq.iter().flat_map(coq_instrs).collect();
    format!(
        "Definition {} ({} : arm_reg) : arm_program :=\n  [{}].",
        rule.name,
        binders.join(" "),
        instrs.join("; "),
    )
}

/// Generate `coq/Synth/Synth/VcrSelRulesGenerated.v` from [`RULES`] — the whole
/// rule table's lowerings wrapped in a `Module Gen`. This is the SINGLE SOURCE
/// of the Rocq model definitions: `VcrSelRules.v` re-exports every rule
/// (`Definition rule_X := Gen.rule_X`) and proves the correctness theorems
/// directly about the generated sequences.
///
/// Committed to the tree and pinned by
/// [`tests::rocq_generated_lowering_is_up_to_date`]; regenerate with
/// `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
pub fn generate_rocq_lowering_source() -> String {
    let mut out = String::new();
    out.push_str(
        "(** * VCR-ISA-001 (#667): the selector rule table's Rocq lowerings, GENERATED.\n\
         \n\
         GENERATED FILE — DO NOT EDIT BY HAND.\n\
         \n\
         Emitted by [crate::sel_dsl::generate_rocq_lowering_source] from the\n\
         shipped rule table [crates/synth-synthesis/src/sel_dsl/mod.rs] (RULES),\n\
         the SAME table that produces the shipped Rust lowering\n\
         ([sel_dsl/generated.rs]). This module is the SINGLE SOURCE of the Rocq\n\
         model definitions: [VcrSelRules.v] re-exports every rule\n\
         ([Definition rule_X := Gen.rule_X]) and states the correctness theorems\n\
         directly about these generated sequences — so the model the theorems\n\
         are ABOUT cannot silently diverge from the shipped selector for the\n\
         covered ops (the #682 vacuous-proof failure mode, closed at the\n\
         instruction-sequence level: a RULES change regenerates this file and\n\
         the matching correctness Qed stops compiling).\n\
         \n\
         Pinned up-to-date by the [rocq_generated_lowering_is_up_to_date] cargo\n\
         test; regenerate with\n\
         [SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl]. *)\n\
         \n\
         From Stdlib Require Import List.\n\
         From Stdlib Require Import ZArith.\n\
         Require Import Synth.Common.Base.\n\
         Require Import Synth.Common.Integers.\n\
         Require Import Synth.ARM.ArmState.\n\
         Require Import Synth.ARM.ArmInstructions.\n\
         Import ListNotations.\n\
         Open Scope Z_scope.\n\
         \n\
         Module Gen.\n",
    );
    for rule in RULES {
        out.push('\n');
        out.push_str(&emit_rocq_definition(rule));
        out.push('\n');
    }
    out.push_str("\nEnd Gen.\n");
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

    /// VCR-ISA-001 (#667): the generated Rocq lowerings
    /// (`coq/Synth/Synth/VcrSelRulesGenerated.v`) are the committed output of
    /// the SAME rule table, emitted straight from `RULES` — and the SINGLE
    /// SOURCE of the model definitions `VcrSelRules.v` re-exports and proves
    /// correct. Any edit to the table (or the file) without regenerating
    /// fails here. Regenerate with
    /// `SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl`.
    #[test]
    fn rocq_generated_lowering_is_up_to_date() {
        let path = crate_root().join("../../coq/Synth/Synth/VcrSelRulesGenerated.v");
        let expected = generate_rocq_lowering_source();
        if std::env::var("SYNTH_SEL_DSL_REGEN").is_ok() {
            std::fs::write(&path, &expected).expect("write VcrSelRulesGenerated.v");
        }
        let actual = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        assert_eq!(
            actual, expected,
            "coq/Synth/Synth/VcrSelRulesGenerated.v is stale relative to the RULES \
             table — regenerate with SYNTH_SEL_DSL_REGEN=1 cargo test -p synth-synthesis sel_dsl"
        );
    }

    /// VCR-ISA-001 (#667) "generate, don't mirror": `VcrSelRules.v` carries NO
    /// hand-written copy of any rule's instruction sequence — every rule is a
    /// re-export of the generated model (`Definition rule_X := Gen.rule_X.`),
    /// so the correctness theorems are stated directly about the sequences
    /// [`RULES`] emits. This is the fast Rust-side smoke of the single-source
    /// property; the real gate is Coq's kernel (a RULES change regenerates
    /// `VcrSelRulesGenerated.v` and the matching correctness Qed stops
    /// compiling under `//coq:verify_proofs`).
    #[test]
    fn vcr_sel_rules_reexports_generated_model() {
        let v_path = crate_root().join("../../coq/Synth/Synth/VcrSelRules.v");
        let v = std::fs::read_to_string(&v_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", v_path.display()));
        assert!(
            v.contains("Require Import Synth.Synth.VcrSelRulesGenerated."),
            "VcrSelRules.v must import the generated model (VcrSelRulesGenerated)"
        );
        // Collapse whitespace runs so alignment padding doesn't matter.
        let norm = |s: &str| s.split_whitespace().collect::<Vec<_>>().join(" ");
        let v_norm = norm(&v);
        for rule in RULES {
            let reexport = format!("Definition {name} := Gen.{name}.", name = rule.name);
            assert!(
                v_norm.contains(&reexport),
                "rule {} is not a re-export of the generated model — expected \
                 `{reexport}` in VcrSelRules.v (no hand-written sequence copies; \
                 VCR-ISA-001 single-source)",
                rule.name
            );
            // A second `Definition <name> ` occurrence would be a shadowing
            // hand-written copy sneaking back in.
            let needle = format!("Definition {} ", rule.name);
            assert_eq!(
                v_norm.matches(&needle).count(),
                1,
                "rule {} must have exactly one Definition (the Gen re-export)",
                rule.name
            );
        }
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
