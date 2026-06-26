//! #498 / #242 (VCR-ORACLE-001) — estimator↔encoder agreement oracle.
//!
//! The optimized ARM path (`synth_synthesis::optimizer_bridge::ir_to_arm`)
//! resolves branch displacements by summing a hand-maintained *byte-size
//! estimator* (`estimate_arm_byte_size`) over the instruction stream. That
//! estimator is a mirror of the Thumb-2 encoder
//! (`synth_backend::ArmEncoder::encode`), kept by hand only because
//! synth-synthesis cannot depend on synth-backend (the encoder lives
//! downstream) — the structural cause behind #498. When the mirror drifts from
//! the encoder, a forward branch spanning the drifting op lands at the wrong
//! byte: under-estimate → short (the #483-class miscompile), over-estimate →
//! long.
//!
//! This crate sits downstream of synth-synthesis and so can see BOTH the
//! estimator and the real encoder. This oracle pins one against the other for
//! every op the optimized path emits, at the operand shapes it emits them in.
//!
//! ## Scope — this is a gap-documenting REGRESSION GUARD, not a #498 fix.
//!
//! Several estimator entries diverge from the encoder today; this test does not
//! correct them (that is byte-changing codegen, a separately-gated step — it
//! shifts every branch displacement on the optimized path and must be re-frozen,
//! execution-differentialed, and silicon-checked). Instead it freezes the
//! divergence as a measured `KNOWN_GAP`, so:
//!
//! - a NEW estimator drift (an added op left at the `_ => 2` default, or a
//!   changed encoding) fails the agreement assertion loudly, and
//! - a future #498 fix that closes a gap fails the `assert_ne!` "still
//!   diverges" check, forcing the gap to be removed from the list.
//!
//! ## Findings recorded here (correct + extend #498's original report)
//! - #498 claimed `Cmp` high-reg drifts. It does NOT: the 16-bit CMP (T2,
//!   `0x45xx`) encodes high registers, so `cmp r10, r8` is 2 bytes and the
//!   estimator's default is right. The real high-reg drifts are `Cmn`/`Adds`/
//!   `Subs` (no 16-bit high-reg form / flag-setting) → 4 bytes, est 2.
//! - `Popcnt` is absent from the estimator entirely → `_ => 2`, but the
//!   encoder expands it to a 21-instruction sequence = 86 bytes. An 84-byte
//!   hole — the largest single drift.
//! - The i64 long-sequence estimates `I64DivU/RemU/DivS/RemS`, `I64Popcnt`
//!   and `I64Extend32S` OVER-estimate (e.g. DivU est 100 vs 74) — branch
//!   lands long.
//! - Far branches (`BOffset`/`BCondOffset` with a large displacement) need
//!   the 4-byte `.w` form but the estimator (which runs BEFORE displacements
//!   are known, with a 0-offset placeholder) sizes them 2 — a chicken-and-egg
//!   the single-pass estimator cannot resolve.
//! - `Mov` with a small NEGATIVE immediate: estimator sizes 4 (prudent), but
//!   the encoder's `if *imm <= 255` is a *signed* test and emits a 2-byte
//!   `MOVS Rd, #(imm & 0xFF)` — a wrong-value 0xFF, a latent ENCODER bug for
//!   negative imm8, surfaced here as a side effect. Tracked separately.

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmOp, Condition, MemAddr, Operand2, Reg, estimate_arm_byte_size};

/// A documented divergence: the optimized-path estimator and the encoder
/// disagree on this op's size today. Pinned to the exact measured pair so a
/// regression (new drift) or a fix (gap closed) both trip the oracle.
struct Gap {
    est: usize,
    enc: usize,
    /// Why it diverges and which direction the branch lands.
    _reason: &'static str,
}

fn mem(base: Reg) -> MemAddr {
    MemAddr {
        base,
        offset: 0,
        offset_reg: None,
    }
}

/// One oracle case: a representative instruction at an operand shape the
/// optimized path actually emits, and whether agreement is expected (`None`) or
/// a documented `KNOWN_GAP` (`Some`).
struct Case {
    label: &'static str,
    op: ArmOp,
    gap: Option<Gap>,
}

fn agree(label: &'static str, op: ArmOp) -> Case {
    Case {
        label,
        op,
        gap: None,
    }
}

fn gap(label: &'static str, op: ArmOp, est: usize, enc: usize, reason: &'static str) -> Case {
    Case {
        label,
        op,
        gap: Some(Gap {
            est,
            enc,
            _reason: reason,
        }),
    }
}

/// The agreement cases. Operand shapes mirror what `ir_to_arm` emits: sub-word
/// memory ops use a HIGH base (`r11`/`ip`, the #483 invariant), data-processing
/// ops appear in both low- and high-reg forms, branches in near and far forms.
fn cases() -> Vec<Case> {
    use ArmOp::*;
    let r0 = Reg::R0;
    vec![
        // --- data-processing, agreement (low-reg + always-32-bit forms) ---
        agree(
            "Add_lo",
            Add {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Add_hi",
            Add {
                rd: Reg::R10,
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            },
        ),
        agree(
            "Sub_lo",
            Sub {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Sub_hi",
            Sub {
                rd: Reg::R10,
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            },
        ),
        agree(
            "Adds_lo",
            Adds {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Subs_lo",
            Subs {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Adc",
            Adc {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Sbc",
            Sbc {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "And",
            And {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Orr",
            Orr {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Eor",
            Eor {
                rd: r0,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Mul",
            Mul {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "Mls",
            Mls {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
                ra: Reg::R3,
            },
        ),
        agree(
            "Sdiv",
            Sdiv {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "Udiv",
            Udiv {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "Rsb",
            Rsb {
                rd: r0,
                rn: Reg::R1,
                imm: 32,
            },
        ),
        agree(
            "AsrReg",
            AsrReg {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "LslReg",
            LslReg {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "LsrReg",
            LsrReg {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "RorReg",
            RorReg {
                rd: r0,
                rn: Reg::R1,
                rm: Reg::R2,
            },
        ),
        agree(
            "Clz",
            Clz {
                rd: r0,
                rm: Reg::R1,
            },
        ),
        agree(
            "Rbit",
            Rbit {
                rd: r0,
                rm: Reg::R1,
            },
        ),
        agree(
            "Sxtb_lo",
            Sxtb {
                rd: r0,
                rm: Reg::R1,
            },
        ),
        agree(
            "Sxtb_hi",
            Sxtb {
                rd: Reg::R9,
                rm: Reg::R10,
            },
        ),
        agree(
            "Sxth_lo",
            Sxth {
                rd: r0,
                rm: Reg::R1,
            },
        ),
        agree(
            "Uxtb_lo",
            Uxtb {
                rd: r0,
                rm: Reg::R1,
            },
        ),
        agree(
            "Uxth_lo",
            Uxth {
                rd: r0,
                rm: Reg::R1,
            },
        ),
        // --- moves ---
        agree(
            "Mov_lo_imm",
            Mov {
                rd: r0,
                op2: Operand2::Imm(5),
            },
        ),
        agree(
            "Mov_hi",
            Mov {
                rd: Reg::R10,
                op2: Operand2::Imm(5),
            },
        ),
        agree(
            "Mov_imm_big",
            Mov {
                rd: r0,
                op2: Operand2::Imm(300),
            },
        ),
        agree(
            "Mov_reg",
            Mov {
                rd: r0,
                op2: Operand2::Reg(Reg::R1),
            },
        ),
        agree(
            "Movw",
            Movw {
                rd: r0,
                imm16: 0x1234,
            },
        ),
        agree(
            "Movt",
            Movt {
                rd: r0,
                imm16: 0x1234,
            },
        ),
        // --- compares ---
        agree(
            "Cmp_lo",
            Cmp {
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        agree(
            "Cmp_hi",
            Cmp {
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            },
        ),
        agree(
            "Cmp_imm",
            Cmp {
                rn: Reg::R1,
                op2: Operand2::Imm(5),
            },
        ),
        agree(
            "Cmn_lo",
            Cmn {
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            },
        ),
        // --- loads/stores: word (offset/base shapes) + sub-word (HIGH base) ---
        agree(
            "Ldr_lo",
            Ldr {
                rd: r0,
                addr: mem(Reg::R1),
            },
        ),
        agree(
            "Ldr_hibase",
            Ldr {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Ldr_offbig",
            Ldr {
                rd: r0,
                addr: MemAddr {
                    base: Reg::R1,
                    offset: 200,
                    offset_reg: None,
                },
            },
        ),
        agree(
            "Str_lo",
            Str {
                rd: r0,
                addr: mem(Reg::R1),
            },
        ),
        agree(
            "Str_hibase",
            Str {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Ldrb_hi",
            Ldrb {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Ldrh_hi",
            Ldrh {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Ldrsb_hi",
            Ldrsb {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Ldrsh_hi",
            Ldrsh {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Strb_hi",
            Strb {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        agree(
            "Strh_hi",
            Strh {
                rd: r0,
                addr: mem(Reg::R11),
            },
        ),
        // --- branches/control + select ---
        agree("BOffset_near", BOffset { offset: 4 }),
        agree(
            "BCondOffset_near",
            BCondOffset {
                cond: Condition::EQ,
                offset: 4,
            },
        ),
        agree("Bx", Bx { rm: Reg::LR }),
        agree(
            "Bl",
            Bl {
                label: "f".to_string(),
            },
        ),
        agree("Udf", Udf { imm: 0 }),
        agree(
            "SetCond",
            SetCond {
                rd: r0,
                cond: Condition::EQ,
            },
        ),
        agree(
            "SelectMove",
            SelectMove {
                rd: r0,
                rm: Reg::R1,
                cond: Condition::EQ,
            },
        ),
        // --- i64 long sequences that the estimator sizes EXACTLY ---
        agree(
            "I64SetCond",
            I64SetCond {
                rd: r0,
                rn_lo: Reg::R1,
                rn_hi: Reg::R2,
                rm_lo: Reg::R3,
                rm_hi: Reg::R4,
                cond: Condition::EQ,
            },
        ),
        agree(
            "I64SetCondZ",
            I64SetCondZ {
                rd: r0,
                rn_lo: Reg::R1,
                rn_hi: Reg::R2,
            },
        ),
        agree(
            "I64Mul",
            I64Mul {
                rd_lo: r0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
        ),
        agree(
            "I64Shl",
            I64Shl {
                rd_lo: r0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
        ),
        agree(
            "I64ShrU",
            I64ShrU {
                rd_lo: r0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
        ),
        agree(
            "I64ShrS",
            I64ShrS {
                rd_lo: r0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
        ),
        agree(
            "I64Rotl",
            I64Rotl {
                rdlo: r0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
                rnhi: Reg::R3,
                shift: Reg::R4,
            },
        ),
        agree(
            "I64Rotr",
            I64Rotr {
                rdlo: r0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
                rnhi: Reg::R3,
                shift: Reg::R4,
            },
        ),
        agree(
            "I64Clz",
            I64Clz {
                rd: r0,
                rnlo: Reg::R1,
                rnhi: Reg::R2,
            },
        ),
        agree(
            "I64Ctz",
            I64Ctz {
                rd: r0,
                rnlo: Reg::R1,
                rnhi: Reg::R2,
            },
        ),
        agree(
            "I64Extend8S",
            I64Extend8S {
                rdlo: r0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
            },
        ),
        agree(
            "I64Extend16S",
            I64Extend16S {
                rdlo: r0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
            },
        ),
        // ============================ KNOWN GAPS ============================
        // High-reg flag-setting / no-16-bit-form ops: estimator default 2, but
        // the encoder must use the 32-bit `.w` form (4 bytes). The #498 core.
        gap(
            "Cmn_hi",
            Cmn {
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            },
            2,
            4,
            "CMN has no 16-bit high-reg form → CMN.W (4); estimator _=>2. Under-estimate.",
        ),
        gap(
            "Adds_hi",
            Adds {
                rd: Reg::R10,
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            },
            2,
            4,
            "flag-setting ADDS high-reg → ADDS.W (4); estimator _=>2. Under-estimate.",
        ),
        gap(
            "Subs_hi",
            Subs {
                rd: Reg::R10,
                rn: Reg::R10,
                op2: Operand2::Reg(Reg::R8),
            },
            2,
            4,
            "flag-setting SUBS high-reg → SUBS.W (4); estimator _=>2. Under-estimate.",
        ),
        // Popcnt: absent from the estimator entirely; encoder expands it.
        gap(
            "Popcnt",
            Popcnt {
                rd: Reg::R0,
                rm: Reg::R1,
            },
            2,
            86,
            "Popcnt absent from estimator (_=>2); encoder emits a 21-insn sequence (86). 84-byte under-estimate.",
        ),
        // i64 long sequences whose hand-counted estimate is too large.
        gap(
            "I64Popcnt",
            I64Popcnt {
                rd: Reg::R0,
                rnlo: Reg::R1,
                rnhi: Reg::R2,
            },
            200,
            172,
            "estimate 200 (~180 guess) vs real 172. Over-estimate.",
        ),
        gap(
            "I64Extend32S",
            I64Extend32S {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
            },
            8,
            6,
            "estimate 8 vs real 6 (MOV + ASR). Over-estimate.",
        ),
        gap(
            "I64DivU",
            I64DivU {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
                rnhi: Reg::R3,
                rmlo: Reg::R4,
                rmhi: Reg::R5,
            },
            100,
            74,
            "estimate 100 (~80-150 guess) vs real 74. Over-estimate.",
        ),
        gap(
            "I64RemU",
            I64RemU {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
                rnhi: Reg::R3,
                rmlo: Reg::R4,
                rmhi: Reg::R5,
            },
            100,
            78,
            "estimate 100 vs real 78. Over-estimate.",
        ),
        gap(
            "I64DivS",
            I64DivS {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
                rnhi: Reg::R3,
                rmlo: Reg::R4,
                rmhi: Reg::R5,
            },
            150,
            126,
            "estimate 150 vs real 126. Over-estimate.",
        ),
        gap(
            "I64RemS",
            I64RemS {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                rnlo: Reg::R2,
                rnhi: Reg::R3,
                rmlo: Reg::R4,
                rmhi: Reg::R5,
            },
            150,
            124,
            "estimate 150 vs real 124. Over-estimate.",
        ),
        // Far branches: the estimator sizes the 0-offset placeholder (it runs
        // before displacements are resolved) as 2, but a far target needs the
        // 4-byte form. Chicken-and-egg in the single-pass estimator.
        gap(
            "BOffset_far",
            BOffset { offset: 5000 },
            2,
            4,
            "far B needs T4 (4); estimator _=>2 on the pre-resolution placeholder. Under-estimate.",
        ),
        gap(
            "BCondOffset_far",
            BCondOffset {
                cond: Condition::EQ,
                offset: 5000,
            },
            2,
            4,
            "far Bcc needs T3 (4); estimator _=>2 on the pre-resolution placeholder. Under-estimate.",
        ),
        // Negative small immediate: estimator prudently sizes 4; the encoder's
        // signed `imm <= 255` test wrongly emits a 2-byte MOVS #(imm&0xFF).
        // Latent ENCODER bug (wrong value), surfaced here. Tracked separately.
        gap(
            "Mov_imm_neg",
            Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(-1),
            },
            4,
            2,
            "estimator 4 (prudent); encoder emits wrong-value 2-byte MOVS #0xFF (signed imm<=255 bug).",
        ),
    ]
}

/// Every `ArmOp` variant, classified as emitted by the optimized path
/// (`OnPath`) or not (`OffPath`). NO wildcard: a newly-added `ArmOp` variant
/// will fail to compile here until it is *consciously classified* — the
/// tripwire that puts a new op in front of a human instead of letting it default
/// to the estimator's `_ => 2`.
///
/// What this guarantees and what it does NOT:
/// - It DOES force every new `ArmOp` variant to be classified OnPath/OffPath.
/// - It does NOT force an agreement case: a variant classified `OnPath` with
///   nothing added to `cases()` still passes vacuously. Adding the OnPath
///   variant's agreement case is a *manual* step this match cannot enforce
///   (closing that would mean restructuring so the per-variant match itself
///   returns the sample + expectation — out of scope here).
/// - It cannot catch an existing `OffPath` op later being wired into
///   `ir_to_arm` (the classification is a hand-asserted claim).
///
/// So: a compile-time prompt to classify, not a proof of coverage.
#[derive(PartialEq, Debug)]
enum Coverage {
    OnPath,
    OffPath,
}

fn coverage(op: &ArmOp) -> Coverage {
    use ArmOp::*;
    use Coverage::*;
    match op {
        // Emitted by ir_to_arm into arm_instrs (flows through byte_offsets).
        Add { .. }
        | Sub { .. }
        | Adds { .. }
        | Subs { .. }
        | Adc { .. }
        | Sbc { .. }
        | Mul { .. }
        | Mls { .. }
        | Sdiv { .. }
        | Udiv { .. }
        | And { .. }
        | Orr { .. }
        | Eor { .. }
        | Asr { .. }
        | AsrReg { .. }
        | LslReg { .. }
        | LsrReg { .. }
        | RorReg { .. }
        | Rsb { .. }
        | Clz { .. }
        | Rbit { .. }
        | Popcnt { .. }
        | Sxtb { .. }
        | Sxth { .. }
        | Uxtb { .. }
        | Uxth { .. }
        | Mov { .. }
        | Movw { .. }
        | Movt { .. }
        | Cmp { .. }
        | Cmn { .. }
        | Ldr { .. }
        | Str { .. }
        | Ldrb { .. }
        | Ldrh { .. }
        | Ldrsb { .. }
        | Ldrsh { .. }
        | Strb { .. }
        | Strh { .. }
        | BOffset { .. }
        | BCondOffset { .. }
        | Bx { .. }
        | Bl { .. }
        | Udf { .. }
        | SetCond { .. }
        | SelectMove { .. }
        | I64SetCond { .. }
        | I64SetCondZ { .. }
        | I64Mul { .. }
        | I64Shl { .. }
        | I64ShrU { .. }
        | I64ShrS { .. }
        | I64Rotl { .. }
        | I64Rotr { .. }
        | I64Clz { .. }
        | I64Ctz { .. }
        | I64Popcnt { .. }
        | I64Extend8S { .. }
        | I64Extend16S { .. }
        | I64Extend32S { .. }
        | I64DivU { .. }
        | I64RemU { .. }
        | I64DivS { .. }
        | I64RemS { .. } => OnPath,

        // NOT emitted by ir_to_arm:
        //  - imm shifts / Mvn / Umull / Mla: direct-selector-only (#209/#257) or
        //    folded by peephole; not produced by the optimized lowering.
        //  - sym-loads (--native-pointer-abi), Memory*, Push/Pop (inserted
        //    post-resolution), Label/Nop/B/Bcc/Bhs/Blo/Blx (path uses the
        //    resolved BOffset/BCondOffset forms), pseudo Local*/Global*/Select/
        //    Call*/BrTable (lowered to primitives upstream).
        //  - i64 BINOPS (Add/Sub/And/Or/Xor/Eq..GeU/Const/Ldr/Str/ExtendI32*/
        //    I32WrapI64): lowered to 32-bit op pairs upstream, never appear as
        //    I64* in arm_instrs (which is why the estimator lists only the
        //    SURVIVING i64 ops above).
        //  - all F32*/F64* scalar VFP (dropped at the decoder today, #369) and
        //    all Mve* vector ops (not on the scalar integer path).
        Lsl { .. }
        | Lsr { .. }
        | Ror { .. }
        | Mvn { .. }
        | Umull { .. }
        | Mla { .. }
        | MovwSym { .. }
        | MovtSym { .. }
        | LdrSym { .. }
        | MemorySize { .. }
        | MemoryGrow { .. }
        | Label { .. }
        | Nop
        | Push { .. }
        | Pop { .. }
        | B { .. }
        | Bcc { .. }
        | Bhs { .. }
        | Blo { .. }
        | Blx { .. }
        | Select { .. }
        | LocalGet { .. }
        | LocalSet { .. }
        | LocalTee { .. }
        | GlobalGet { .. }
        | GlobalSet { .. }
        | Call { .. }
        | CallIndirect { .. }
        | BrTable { .. }
        | I64Add { .. }
        | I64Sub { .. }
        | I64And { .. }
        | I64Or { .. }
        | I64Xor { .. }
        | I64Eqz { .. }
        | I64Eq { .. }
        | I64Ne { .. }
        | I64LtS { .. }
        | I64LtU { .. }
        | I64LeS { .. }
        | I64LeU { .. }
        | I64GtS { .. }
        | I64GtU { .. }
        | I64GeS { .. }
        | I64GeU { .. }
        | I64Const { .. }
        | I64Ldr { .. }
        | I64Str { .. }
        | I64ExtendI32S { .. }
        | I64ExtendI32U { .. }
        | I32WrapI64 { .. }
        | F32Add { .. }
        | F32Sub { .. }
        | F32Mul { .. }
        | F32Div { .. }
        | F32Abs { .. }
        | F32Neg { .. }
        | F32Sqrt { .. }
        | F32Ceil { .. }
        | F32Floor { .. }
        | F32Trunc { .. }
        | F32Nearest { .. }
        | F32Min { .. }
        | F32Max { .. }
        | F32Copysign { .. }
        | F32Eq { .. }
        | F32Ne { .. }
        | F32Lt { .. }
        | F32Le { .. }
        | F32Gt { .. }
        | F32Ge { .. }
        | F32Const { .. }
        | F32Load { .. }
        | F32Store { .. }
        | F32ConvertI32S { .. }
        | F32ConvertI32U { .. }
        | F32ConvertI64S { .. }
        | F32ConvertI64U { .. }
        | F32ReinterpretI32 { .. }
        | I32ReinterpretF32 { .. }
        | I32TruncF32S { .. }
        | I32TruncF32U { .. }
        | F64Add { .. }
        | F64Sub { .. }
        | F64Mul { .. }
        | F64Div { .. }
        | F64Abs { .. }
        | F64Neg { .. }
        | F64Sqrt { .. }
        | F64Ceil { .. }
        | F64Floor { .. }
        | F64Trunc { .. }
        | F64Nearest { .. }
        | F64Min { .. }
        | F64Max { .. }
        | F64Copysign { .. }
        | F64Eq { .. }
        | F64Ne { .. }
        | F64Lt { .. }
        | F64Le { .. }
        | F64Gt { .. }
        | F64Ge { .. }
        | F64Const { .. }
        | F64Load { .. }
        | F64Store { .. }
        | F64ConvertI32S { .. }
        | F64ConvertI32U { .. }
        | F64ConvertI64S { .. }
        | F64ConvertI64U { .. }
        | F64PromoteF32 { .. }
        | F64ReinterpretI64 { .. }
        | I64ReinterpretF64 { .. }
        | I64TruncF64S { .. }
        | I64TruncF64U { .. }
        | I32TruncF64S { .. }
        | I32TruncF64U { .. }
        | MveLoad { .. }
        | MveStore { .. }
        | MveConst { .. }
        | MveAnd { .. }
        | MveOrr { .. }
        | MveEor { .. }
        | MveMvn { .. }
        | MveBic { .. }
        | MveAddI { .. }
        | MveSubI { .. }
        | MveMulI { .. }
        | MveNegI { .. }
        | MveCmpEqI { .. }
        | MveCmpNeI { .. }
        | MveCmpLtS { .. }
        | MveCmpLtU { .. }
        | MveCmpGtS { .. }
        | MveCmpGtU { .. }
        | MveCmpLeS { .. }
        | MveCmpLeU { .. }
        | MveCmpGeS { .. }
        | MveCmpGeU { .. }
        | MveDup { .. }
        | MveExtractLane { .. }
        | MveInsertLane { .. }
        | MveAddF32 { .. }
        | MveSubF32 { .. }
        | MveMulF32 { .. }
        | MveNegF32 { .. }
        | MveAbsF32 { .. }
        | MveCmpEqF32 { .. }
        | MveCmpNeF32 { .. }
        | MveCmpLtF32 { .. }
        | MveCmpLeF32 { .. }
        | MveCmpGtF32 { .. }
        | MveCmpGeF32 { .. }
        | MveDupF32 { .. }
        | MveExtractLaneF32 { .. }
        | MveReplaceLaneF32 { .. }
        | MveDivF32 { .. }
        | MveSqrtF32 { .. } => OffPath,
    }
}

/// The estimator must agree with the encoder for every op the optimized path
/// emits — or the divergence must be a documented `KNOWN_GAP` pinned to its
/// exact measured (estimate, encoder) pair.
#[test]
fn estimator_encoder_agreement() {
    let enc = ArmEncoder::new_thumb2();
    let mut surprises = Vec::new();

    for case in cases() {
        // Every case must be an op the optimized path actually emits.
        assert_eq!(
            coverage(&case.op),
            Coverage::OnPath,
            "{}: oracle case is for an OffPath op — remove it or reclassify",
            case.label
        );

        let est = estimate_arm_byte_size(&case.op);
        let real = enc
            .encode(&case.op)
            .unwrap_or_else(|e| panic!("{}: encoder rejected the op: {e:?}", case.label))
            .len();

        match case.gap {
            None => {
                if est != real {
                    surprises.push(format!(
                        "NEW DRIFT {}: estimator {est} != encoder {real} \
                         (fix the estimator, or add a documented KNOWN_GAP)",
                        case.label
                    ));
                }
            }
            Some(g) => {
                if (est, real) != (g.est, g.enc) {
                    surprises.push(format!(
                        "KNOWN_GAP CHANGED {}: was (est {}, enc {}), now (est {est}, enc {real}) \
                         — update or remove the gap",
                        case.label, g.est, g.enc
                    ));
                }
                if est == real {
                    surprises.push(format!(
                        "GAP CLOSED {}: estimator and encoder now agree ({est}) \
                         — remove it from KNOWN_GAP",
                        case.label
                    ));
                }
            }
        }
    }

    assert!(
        surprises.is_empty(),
        "estimator↔encoder drift:\n{}",
        surprises.join("\n")
    );
}
