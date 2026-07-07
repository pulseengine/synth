//! #615 tripwire — no silent-NOP arm survives in the A32 encoder.
//!
//! History of the class: the A32 (`--target arm` / `cortex-r5`) match carried
//! "encode as NOP for now" arms from the verification era. Each became a
//! user-reachable silent miscompile once a real target selected ARM mode:
//! #594 (`call_indirect` → NOP, call never happened), #610/#613 (i64 rot/div
//! silently zero on Thumb), #615 (every i64 op → NOP on cortex-r5: the value
//! silently vanished, functions returned garbage).
//!
//! This test stops the class from regrowing, structurally:
//!
//! 1. `classify` is an exhaustive `match` over `ArmOp` with NO wildcard arm —
//!    adding a new `ArmOp` variant fails compilation here until the author
//!    states how the A32 encoder must treat it.
//! 2. `representatives()` constructs a non-degenerate instance of EVERY
//!    variant (completeness enforced by the variant-count check), and the
//!    test asserts each one's `encode` result matches its classification:
//!    a real encoding is never the bare NOP word `0xE1A00000`; an op with no
//!    A32 encoding must be a typed `Err` (loud), never `Ok(NOP)`.
//!
//! Allowlisted genuine no-ops (`a32_genuine_noops_are_allowed`): `ArmOp::Nop`
//! itself, and true reg-to-same-reg moves (`Mov rd, rd`; `I32WrapI64` with
//! `rd == rnlo`; `Lsl rd, rd, #0`), where `MOV R0, R0` is the correct code.

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmOp, Condition, MemAddr, MveSize, Operand2, QReg, Reg, VfpReg};

/// The bare A32 NOP word: `MOV R0, R0` (`0xE1A00000`, little-endian).
const NOP_WORD: [u8; 4] = [0x00, 0x00, 0xA0, 0xE1];

/// Bump when adding an `ArmOp` variant — and add a representative instance to
/// `representatives()` (the completeness check below counts unique variants).
const ARM_OP_VARIANT_COUNT: usize = 221;

/// How the A32 encoder must treat each op.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Expect {
    /// `Ok(bytes)`: non-empty and NOT the bare NOP word.
    Real,
    /// `Err(_)`: no A32 encoding exists — the failure must be loud.
    LoudErr,
    /// `Ok(vec![])`: structural pseudo-op that emits no code (`Label`).
    NoBytes,
    /// `Ok(NOP_WORD)`: genuinely a no-op (`ArmOp::Nop` itself).
    Nop,
}

/// COMPILE-TIME TRIPWIRE — exhaustive, NO wildcard arm. A new `ArmOp` variant
/// does not compile until it is classified here (and given a representative).
fn classify(op: &ArmOp) -> Expect {
    use Expect::*;
    match op {
        // Real single-word / multi-word A32 encodings.
        ArmOp::Add { .. }
        | ArmOp::Sub { .. }
        | ArmOp::Adds { .. }
        | ArmOp::Adc { .. }
        | ArmOp::Subs { .. }
        | ArmOp::Sbc { .. }
        | ArmOp::Mul { .. }
        | ArmOp::Umull { .. }
        | ArmOp::Sdiv { .. }
        | ArmOp::Udiv { .. }
        | ArmOp::Mls { .. }
        | ArmOp::Mla { .. }
        | ArmOp::And { .. }
        | ArmOp::Orr { .. }
        | ArmOp::Eor { .. }
        | ArmOp::Lsl { .. }
        | ArmOp::Lsr { .. }
        | ArmOp::Asr { .. }
        | ArmOp::Ror { .. }
        | ArmOp::LslReg { .. }
        | ArmOp::LsrReg { .. }
        | ArmOp::AsrReg { .. }
        | ArmOp::RorReg { .. }
        | ArmOp::Rsb { .. }
        | ArmOp::Clz { .. }
        | ArmOp::Rbit { .. }
        | ArmOp::Sxtb { .. }
        | ArmOp::Sxth { .. }
        | ArmOp::Uxtb { .. }
        | ArmOp::Uxth { .. }
        | ArmOp::Mov { .. }
        | ArmOp::Mvn { .. }
        | ArmOp::Movw { .. }
        | ArmOp::Movt { .. }
        | ArmOp::MovwSym { .. }
        | ArmOp::MovtSym { .. }
        | ArmOp::Cmp { .. }
        | ArmOp::Cmn { .. }
        | ArmOp::Ldr { .. }
        | ArmOp::Str { .. }
        | ArmOp::Ldrb { .. }
        | ArmOp::Ldrsb { .. }
        | ArmOp::Ldrh { .. }
        | ArmOp::Ldrsh { .. }
        | ArmOp::Strb { .. }
        | ArmOp::Strh { .. }
        | ArmOp::MemorySize { .. }
        | ArmOp::MemoryGrow { .. }
        | ArmOp::B { .. }
        | ArmOp::BOffset { .. }
        | ArmOp::BCondOffset { .. }
        | ArmOp::Bhs { .. }
        | ArmOp::Blo { .. }
        | ArmOp::Bcc { .. }
        | ArmOp::Bl { .. }
        | ArmOp::Bx { .. }
        | ArmOp::Blx { .. }
        | ArmOp::Push { .. }
        | ArmOp::Pop { .. }
        | ArmOp::Udf { .. } => Real,

        // #615: formerly "NOP for now" — now real A32 expansions.
        ArmOp::Popcnt { .. }
        | ArmOp::SetCond { .. }
        | ArmOp::SelectMove { .. }
        | ArmOp::I64SetCond { .. }
        | ArmOp::I64SetCondZ { .. }
        | ArmOp::I64Mul { .. }
        | ArmOp::I64Shl { .. }
        | ArmOp::I64ShrS { .. }
        | ArmOp::I64ShrU { .. }
        | ArmOp::I64Add { .. }
        | ArmOp::I64Sub { .. }
        | ArmOp::I64DivS { .. }
        | ArmOp::I64DivU { .. }
        | ArmOp::I64RemS { .. }
        | ArmOp::I64RemU { .. }
        | ArmOp::I64And { .. }
        | ArmOp::I64Or { .. }
        | ArmOp::I64Xor { .. }
        | ArmOp::I64Rotl { .. }
        | ArmOp::I64Rotr { .. }
        | ArmOp::I64Clz { .. }
        | ArmOp::I64Ctz { .. }
        | ArmOp::I64Popcnt { .. }
        | ArmOp::I64Eqz { .. }
        | ArmOp::I64Eq { .. }
        | ArmOp::I64Ne { .. }
        | ArmOp::I64LtS { .. }
        | ArmOp::I64LtU { .. }
        | ArmOp::I64LeS { .. }
        | ArmOp::I64LeU { .. }
        | ArmOp::I64GtS { .. }
        | ArmOp::I64GtU { .. }
        | ArmOp::I64GeS { .. }
        | ArmOp::I64GeU { .. }
        | ArmOp::I64Const { .. }
        | ArmOp::I64Ldr { .. }
        | ArmOp::I64Str { .. }
        | ArmOp::I64ExtendI32S { .. }
        | ArmOp::I64ExtendI32U { .. }
        | ArmOp::I64Extend8S { .. }
        | ArmOp::I64Extend16S { .. }
        | ArmOp::I64Extend32S { .. }
        | ArmOp::I32WrapI64 { .. } => Real,

        // #594: expanded to MOV/LDR/BLX.
        ArmOp::CallIndirect { .. } => Real,

        // Structural pseudo-op: marks a branch target, emits no code.
        ArmOp::Label { .. } => NoBytes,

        // The one op whose encoding IS the NOP word.
        ArmOp::Nop => Nop,

        // Verification-only pseudo-ops (synth-verify's ArmSemantics models
        // them; no codegen path constructs them) — must be a loud Err (#615).
        ArmOp::Select { .. }
        | ArmOp::LocalGet { .. }
        | ArmOp::LocalSet { .. }
        | ArmOp::LocalTee { .. }
        | ArmOp::GlobalGet { .. }
        | ArmOp::GlobalSet { .. }
        | ArmOp::BrTable { .. }
        | ArmOp::Call { .. } => LoudErr,

        // Thumb-2-only literal-pool address load (#345).
        ArmOp::LdrSym { .. } => LoudErr,

        // VFP encodings are shared between A32 and Thumb-2 (same words).
        ArmOp::F32Add { .. }
        | ArmOp::F32Sub { .. }
        | ArmOp::F32Mul { .. }
        | ArmOp::F32Div { .. }
        | ArmOp::F32Abs { .. }
        | ArmOp::F32Neg { .. }
        | ArmOp::F32Sqrt { .. }
        | ArmOp::F32Ceil { .. }
        | ArmOp::F32Floor { .. }
        | ArmOp::F32Trunc { .. }
        | ArmOp::F32Nearest { .. }
        | ArmOp::F32Min { .. }
        | ArmOp::F32Max { .. }
        | ArmOp::F32Copysign { .. }
        | ArmOp::F32Eq { .. }
        | ArmOp::F32Ne { .. }
        | ArmOp::F32Lt { .. }
        | ArmOp::F32Le { .. }
        | ArmOp::F32Gt { .. }
        | ArmOp::F32Ge { .. }
        | ArmOp::F32Const { .. }
        | ArmOp::F32Load { .. }
        | ArmOp::F32Store { .. }
        | ArmOp::F32ConvertI32S { .. }
        | ArmOp::F32ConvertI32U { .. }
        | ArmOp::F32ReinterpretI32 { .. }
        | ArmOp::I32ReinterpretF32 { .. }
        | ArmOp::I32TruncF32S { .. }
        | ArmOp::I32TruncF32U { .. }
        | ArmOp::F64Add { .. }
        | ArmOp::F64Sub { .. }
        | ArmOp::F64Mul { .. }
        | ArmOp::F64Div { .. }
        | ArmOp::F64Abs { .. }
        | ArmOp::F64Neg { .. }
        | ArmOp::F64Sqrt { .. }
        | ArmOp::F64Ceil { .. }
        | ArmOp::F64Floor { .. }
        | ArmOp::F64Trunc { .. }
        | ArmOp::F64Nearest { .. }
        | ArmOp::F64Min { .. }
        | ArmOp::F64Max { .. }
        | ArmOp::F64Copysign { .. }
        | ArmOp::F64Eq { .. }
        | ArmOp::F64Ne { .. }
        | ArmOp::F64Lt { .. }
        | ArmOp::F64Le { .. }
        | ArmOp::F64Gt { .. }
        | ArmOp::F64Ge { .. }
        | ArmOp::F64Const { .. }
        | ArmOp::F64Load { .. }
        | ArmOp::F64Store { .. }
        | ArmOp::F64ConvertI32S { .. }
        | ArmOp::F64ConvertI32U { .. }
        | ArmOp::F64PromoteF32 { .. }
        | ArmOp::F64ReinterpretI64 { .. }
        | ArmOp::I64ReinterpretF64 { .. }
        | ArmOp::I32TruncF64S { .. }
        | ArmOp::I32TruncF64U { .. } => Real,

        // i64<->float conversions need register pairs — typed Err on ARM32.
        ArmOp::F32ConvertI64S { .. }
        | ArmOp::F32ConvertI64U { .. }
        | ArmOp::F64ConvertI64S { .. }
        | ArmOp::F64ConvertI64U { .. }
        | ArmOp::I64TruncF64S { .. }
        | ArmOp::I64TruncF64U { .. } => LoudErr,

        // MVE (Helium) is Thumb-2-only (Cortex-M55) — loud Err on A32 (#615).
        ArmOp::MveLoad { .. }
        | ArmOp::MveStore { .. }
        | ArmOp::MveConst { .. }
        | ArmOp::MveAnd { .. }
        | ArmOp::MveOrr { .. }
        | ArmOp::MveEor { .. }
        | ArmOp::MveMvn { .. }
        | ArmOp::MveBic { .. }
        | ArmOp::MveAddI { .. }
        | ArmOp::MveSubI { .. }
        | ArmOp::MveMulI { .. }
        | ArmOp::MveNegI { .. }
        | ArmOp::MveCmpEqI { .. }
        | ArmOp::MveCmpNeI { .. }
        | ArmOp::MveCmpLtS { .. }
        | ArmOp::MveCmpLtU { .. }
        | ArmOp::MveCmpGtS { .. }
        | ArmOp::MveCmpGtU { .. }
        | ArmOp::MveCmpLeS { .. }
        | ArmOp::MveCmpLeU { .. }
        | ArmOp::MveCmpGeS { .. }
        | ArmOp::MveCmpGeU { .. }
        | ArmOp::MveDup { .. }
        | ArmOp::MveExtractLane { .. }
        | ArmOp::MveInsertLane { .. }
        | ArmOp::MveAddF32 { .. }
        | ArmOp::MveSubF32 { .. }
        | ArmOp::MveMulF32 { .. }
        | ArmOp::MveNegF32 { .. }
        | ArmOp::MveAbsF32 { .. }
        | ArmOp::MveCmpEqF32 { .. }
        | ArmOp::MveCmpNeF32 { .. }
        | ArmOp::MveCmpLtF32 { .. }
        | ArmOp::MveCmpLeF32 { .. }
        | ArmOp::MveCmpGtF32 { .. }
        | ArmOp::MveCmpGeF32 { .. }
        | ArmOp::MveDupF32 { .. }
        | ArmOp::MveExtractLaneF32 { .. }
        | ArmOp::MveReplaceLaneF32 { .. }
        | ArmOp::MveDivF32 { .. }
        | ArmOp::MveSqrtF32 { .. } => LoudErr,
    }
}

/// One non-degenerate representative per variant (rd != rm, non-zero shifts,
/// in-range offsets) so a `Real` op can never be the bare NOP by accident.
#[allow(clippy::too_many_lines)]
fn representatives() -> Vec<ArmOp> {
    use ArmOp::*;
    let m = MemAddr::imm(Reg::R11, 8);
    let pair6 = (Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5);
    let (dl, dh, nl, nh, ml, mh) = pair6;
    vec![
        Add {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Imm(4),
        },
        Sub {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Imm(4),
        },
        Adds {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Reg(Reg::R3),
        },
        Adc {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Reg(Reg::R3),
        },
        Subs {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Reg(Reg::R3),
        },
        Sbc {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Reg(Reg::R3),
        },
        Mul {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        Umull {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        Sdiv {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        Udiv {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        Mls {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
            ra: Reg::R4,
        },
        Mla {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
            ra: Reg::R4,
        },
        And {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Imm(0xFF),
        },
        Orr {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Imm(0xFF),
        },
        Eor {
            rd: Reg::R1,
            rn: Reg::R2,
            op2: Operand2::Imm(0xFF),
        },
        Lsl {
            rd: Reg::R1,
            rn: Reg::R2,
            shift: 3,
        },
        Lsr {
            rd: Reg::R1,
            rn: Reg::R2,
            shift: 3,
        },
        Asr {
            rd: Reg::R1,
            rn: Reg::R2,
            shift: 3,
        },
        Ror {
            rd: Reg::R1,
            rn: Reg::R2,
            shift: 3,
        },
        LslReg {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        LsrReg {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        AsrReg {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        RorReg {
            rd: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        },
        Rsb {
            rd: Reg::R1,
            rn: Reg::R2,
            imm: 32,
        },
        Clz {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Rbit {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Popcnt {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Sxtb {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Sxth {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Uxtb {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Uxth {
            rd: Reg::R1,
            rm: Reg::R2,
        },
        Mov {
            rd: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        },
        Mvn {
            rd: Reg::R1,
            op2: Operand2::Imm(0),
        },
        Movw {
            rd: Reg::R1,
            imm16: 0x1234,
        },
        Movt {
            rd: Reg::R1,
            imm16: 0x1234,
        },
        MovwSym {
            rd: Reg::R1,
            symbol: "__synth_wasm_data".into(),
            addend: 4,
        },
        MovtSym {
            rd: Reg::R1,
            symbol: "__synth_wasm_data".into(),
            addend: 4,
        },
        LdrSym {
            rd: Reg::R1,
            symbol: "__synth_globals".into(),
            addend: 0,
        },
        Cmp {
            rn: Reg::R1,
            op2: Operand2::Imm(1),
        },
        Cmn {
            rn: Reg::R1,
            op2: Operand2::Imm(1),
        },
        Ldr {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Str {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Ldrb {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Ldrsb {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Ldrh {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Ldrsh {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Strb {
            rd: Reg::R1,
            addr: m.clone(),
        },
        Strh {
            rd: Reg::R1,
            addr: m.clone(),
        },
        MemorySize { rd: Reg::R1 },
        MemoryGrow {
            rd: Reg::R1,
            rn: Reg::R2,
        },
        Label { name: "L0".into() },
        B { label: "L0".into() },
        BOffset { offset: 4 },
        BCondOffset {
            cond: Condition::NE,
            offset: 4,
        },
        Bhs { label: "L0".into() },
        Blo { label: "L0".into() },
        Bcc {
            cond: Condition::EQ,
            label: "L0".into(),
        },
        Bl { label: "f".into() },
        Bx { rm: Reg::LR },
        Blx { rm: Reg::R3 },
        Push {
            regs: vec![Reg::R4, Reg::LR],
        },
        Pop {
            regs: vec![Reg::R4, Reg::PC],
        },
        Nop,
        Udf { imm: 0 },
        SetCond {
            rd: Reg::R2,
            cond: Condition::NE,
        },
        I64SetCond {
            rd: Reg::R0,
            rn_lo: Reg::R2,
            rn_hi: Reg::R3,
            rm_lo: Reg::R4,
            rm_hi: Reg::R5,
            cond: Condition::LT,
        },
        I64SetCondZ {
            rd: Reg::R0,
            rn_lo: Reg::R2,
            rn_hi: Reg::R3,
        },
        I64Mul {
            rd_lo: dl,
            rd_hi: dh,
            rn_lo: nl,
            rn_hi: nh,
            rm_lo: ml,
            rm_hi: mh,
        },
        I64Shl {
            rd_lo: dl,
            rd_hi: dh,
            rn_lo: nl,
            rn_hi: nh,
            rm_lo: ml,
            rm_hi: mh,
        },
        I64ShrS {
            rd_lo: dl,
            rd_hi: dh,
            rn_lo: nl,
            rn_hi: nh,
            rm_lo: ml,
            rm_hi: mh,
        },
        I64ShrU {
            rd_lo: dl,
            rd_hi: dh,
            rn_lo: nl,
            rn_hi: nh,
            rm_lo: ml,
            rm_hi: mh,
        },
        SelectMove {
            rd: Reg::R1,
            rm: Reg::R2,
            cond: Condition::EQ,
        },
        Select {
            rd: Reg::R0,
            rval1: Reg::R1,
            rval2: Reg::R2,
            rcond: Reg::R3,
        },
        LocalGet {
            rd: Reg::R0,
            index: 0,
        },
        LocalSet {
            rs: Reg::R0,
            index: 0,
        },
        LocalTee {
            rd: Reg::R0,
            rs: Reg::R1,
            index: 0,
        },
        GlobalGet {
            rd: Reg::R0,
            index: 0,
        },
        GlobalSet {
            rs: Reg::R0,
            index: 0,
        },
        BrTable {
            rd: Reg::R0,
            index_reg: Reg::R1,
            targets: vec![0, 1],
            default: 2,
        },
        Call {
            rd: Reg::R0,
            func_idx: 1,
        },
        CallIndirect {
            rd: Reg::R0,
            type_idx: 0,
            table_index_reg: Reg::R2,
        },
        I64Add {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64Sub {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64DivS {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64DivU {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64RemS {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64RemU {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64And {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64Or {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64Xor {
            rdlo: dl,
            rdhi: dh,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64Rotl {
            rdlo: Reg::R4,
            rdhi: Reg::R5,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            shift: Reg::R2,
        },
        I64Rotr {
            rdlo: Reg::R4,
            rdhi: Reg::R5,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            shift: Reg::R2,
        },
        I64Clz {
            rd: Reg::R0,
            rnlo: Reg::R1,
            rnhi: Reg::R2,
        },
        I64Ctz {
            rd: Reg::R0,
            rnlo: Reg::R1,
            rnhi: Reg::R2,
        },
        I64Popcnt {
            rd: Reg::R0,
            rnlo: Reg::R1,
            rnhi: Reg::R2,
        },
        I64Eqz {
            rd: Reg::R0,
            rnlo: Reg::R1,
            rnhi: Reg::R2,
        },
        I64Eq {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64Ne {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64LtS {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64LtU {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64LeS {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64LeU {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64GtS {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64GtU {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64GeS {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64GeU {
            rd: Reg::R0,
            rnlo: nl,
            rnhi: nh,
            rmlo: ml,
            rmhi: mh,
        },
        I64Const {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            value: 0x1234_5678_9ABC_DEF0u64 as i64,
        },
        I64Ldr {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            addr: m.clone(),
        },
        I64Str {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            addr: m.clone(),
        },
        I64ExtendI32S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R2,
        },
        I64ExtendI32U {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R2,
        },
        I64Extend8S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R2,
        },
        I64Extend16S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R2,
        },
        I64Extend32S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R2,
        },
        I32WrapI64 {
            rd: Reg::R0,
            rnlo: Reg::R1,
        },
        F32Add {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Sub {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Mul {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Div {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Abs {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Neg {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Sqrt {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Ceil {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Floor {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Trunc {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Nearest {
            sd: VfpReg::S0,
            sm: VfpReg::S1,
        },
        F32Min {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Max {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Copysign {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Eq {
            rd: Reg::R0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Ne {
            rd: Reg::R0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Lt {
            rd: Reg::R0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Le {
            rd: Reg::R0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Gt {
            rd: Reg::R0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Ge {
            rd: Reg::R0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        },
        F32Const {
            sd: VfpReg::S0,
            value: 1.5,
        },
        F32Load {
            sd: VfpReg::S0,
            addr: m.clone(),
        },
        F32Store {
            sd: VfpReg::S0,
            addr: m.clone(),
        },
        F32ConvertI32S {
            sd: VfpReg::S0,
            rm: Reg::R1,
        },
        F32ConvertI32U {
            sd: VfpReg::S0,
            rm: Reg::R1,
        },
        F32ConvertI64S {
            sd: VfpReg::S0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        },
        F32ConvertI64U {
            sd: VfpReg::S0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        },
        F32ReinterpretI32 {
            sd: VfpReg::S0,
            rm: Reg::R1,
        },
        I32ReinterpretF32 {
            rd: Reg::R0,
            sm: VfpReg::S1,
        },
        I32TruncF32S {
            rd: Reg::R0,
            sm: VfpReg::S1,
        },
        I32TruncF32U {
            rd: Reg::R0,
            sm: VfpReg::S1,
        },
        F64Add {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Sub {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Mul {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Div {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Abs {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Neg {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Sqrt {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Ceil {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Floor {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Trunc {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Nearest {
            dd: VfpReg::D0,
            dm: VfpReg::D1,
        },
        F64Min {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Max {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Copysign {
            dd: VfpReg::D0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Eq {
            rd: Reg::R0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Ne {
            rd: Reg::R0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Lt {
            rd: Reg::R0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Le {
            rd: Reg::R0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Gt {
            rd: Reg::R0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Ge {
            rd: Reg::R0,
            dn: VfpReg::D1,
            dm: VfpReg::D2,
        },
        F64Const {
            dd: VfpReg::D0,
            value: 1.5,
        },
        F64Load {
            dd: VfpReg::D0,
            addr: m.clone(),
        },
        F64Store {
            dd: VfpReg::D0,
            addr: m.clone(),
        },
        F64ConvertI32S {
            dd: VfpReg::D0,
            rm: Reg::R1,
        },
        F64ConvertI32U {
            dd: VfpReg::D0,
            rm: Reg::R1,
        },
        F64ConvertI64S {
            dd: VfpReg::D0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        },
        F64ConvertI64U {
            dd: VfpReg::D0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        },
        F64PromoteF32 {
            dd: VfpReg::D0,
            sm: VfpReg::S1,
        },
        F64ReinterpretI64 {
            dd: VfpReg::D0,
            rmlo: Reg::R0,
            rmhi: Reg::R1,
        },
        I64ReinterpretF64 {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            dm: VfpReg::D1,
        },
        I64TruncF64S {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            dm: VfpReg::D1,
        },
        I64TruncF64U {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            dm: VfpReg::D1,
        },
        I32TruncF64S {
            rd: Reg::R0,
            dm: VfpReg::D1,
        },
        I32TruncF64U {
            rd: Reg::R0,
            dm: VfpReg::D1,
        },
        MveLoad {
            qd: QReg::Q0,
            addr: m.clone(),
        },
        MveStore {
            qd: QReg::Q0,
            addr: m.clone(),
        },
        MveConst {
            qd: QReg::Q0,
            bytes: [0u8; 16],
        },
        MveAnd {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveOrr {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveEor {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveMvn {
            qd: QReg::Q0,
            qm: QReg::Q1,
        },
        MveBic {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveAddI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveSubI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveMulI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveNegI {
            qd: QReg::Q0,
            qm: QReg::Q1,
            size: MveSize::S32,
        },
        MveCmpEqI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpNeI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpLtS {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpLtU {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpGtS {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpGtU {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpLeS {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpLeU {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpGeS {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveCmpGeU {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        },
        MveDup {
            qd: QReg::Q0,
            rn: Reg::R1,
            size: MveSize::S32,
        },
        MveExtractLane {
            rd: Reg::R0,
            qn: QReg::Q1,
            lane: 0,
            size: MveSize::S32,
        },
        MveInsertLane {
            qd: QReg::Q0,
            rn: Reg::R1,
            lane: 0,
            size: MveSize::S32,
        },
        MveAddF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveSubF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveMulF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveNegF32 {
            qd: QReg::Q0,
            qm: QReg::Q1,
        },
        MveAbsF32 {
            qd: QReg::Q0,
            qm: QReg::Q1,
        },
        MveCmpEqF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveCmpNeF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveCmpLtF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveCmpLeF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveCmpGtF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveCmpGeF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveDupF32 {
            qd: QReg::Q0,
            rn: Reg::R1,
        },
        MveExtractLaneF32 {
            rd: Reg::R0,
            qn: QReg::Q1,
            lane: 0,
        },
        MveReplaceLaneF32 {
            qd: QReg::Q0,
            rn: Reg::R1,
            lane: 0,
        },
        MveDivF32 {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
        },
        MveSqrtF32 {
            qd: QReg::Q0,
            qm: QReg::Q1,
        },
    ]
}

/// The variant name of an op (`"Add"` from `Add { rd: R1, ... }`).
fn variant_name(op: &ArmOp) -> String {
    let dbg = format!("{op:?}");
    dbg.split([' ', '{']).next().unwrap_or(&dbg).to_string()
}

#[test]
fn a32_encoder_has_no_silent_nop_arm() {
    let enc = ArmEncoder::new_arm32();
    // Completeness: one representative per ArmOp variant.
    let reps = representatives();
    let mut names: Vec<String> = reps.iter().map(variant_name).collect();
    names.sort();
    names.dedup();
    assert_eq!(
        names.len(),
        ARM_OP_VARIANT_COUNT,
        "representatives() must cover every ArmOp variant exactly once \
         (did you add a variant to classify() without a representative?)"
    );

    for op in &reps {
        let expect = classify(op);
        let result = enc.encode(op);
        match expect {
            Expect::Real => {
                let bytes = result.unwrap_or_else(|e| {
                    panic!("{op:?}: expected a real A32 encoding, got Err({e})")
                });
                assert!(!bytes.is_empty(), "{op:?}: expected code, got no bytes");
                assert_ne!(
                    bytes.as_slice(),
                    NOP_WORD,
                    "{op:?}: A32 encoding is the bare NOP word — a silent NOP arm \
                     regrew (#615 class)"
                );
            }
            Expect::LoudErr => {
                assert!(
                    result.is_err(),
                    "{op:?}: expected a loud Err (no A32 encoding), got Ok({:02x?})",
                    result.unwrap()
                );
            }
            Expect::NoBytes => {
                assert_eq!(
                    result.expect("Label must encode Ok"),
                    Vec::<u8>::new(),
                    "{op:?}: structural pseudo-op must emit no code"
                );
            }
            Expect::Nop => {
                assert_eq!(
                    result.expect("Nop must encode Ok").as_slice(),
                    NOP_WORD,
                    "{op:?}: ArmOp::Nop must encode as the NOP word"
                );
            }
        }
    }
}

/// The documented allowlist: cases where the bare NOP word IS the correct
/// encoding — a genuine no-op, not a dropped operation.
#[test]
fn a32_genuine_noops_are_allowed() {
    let enc = ArmEncoder::new_arm32();
    for op in [
        ArmOp::Nop,
        // MOV rd, rd — a true register-to-same-register move.
        ArmOp::Mov {
            rd: Reg::R0,
            op2: Operand2::Reg(Reg::R0),
        },
        // i32.wrap_i64 with rd == rnlo: the low word is already in place.
        ArmOp::I32WrapI64 {
            rd: Reg::R0,
            rnlo: Reg::R0,
        },
        // LSL #0 of a register onto itself.
        ArmOp::Lsl {
            rd: Reg::R0,
            rn: Reg::R0,
            shift: 0,
        },
    ] {
        let bytes = enc.encode(&op).expect("genuine no-op must encode Ok");
        assert_eq!(
            bytes.as_slice(),
            NOP_WORD,
            "{op:?}: expected the (genuine) NOP encoding"
        );
    }
}
