//! RQ-65-ALIASCLASS (#1189) — the home-register write audit.
//!
//! THE MECHANISM, stated once. On the ARM direct selector
//! (`select_with_stack`) `local.get` of a REGISTER-HOMED local — an AAPCS
//! param in r0–r3 (call-free function), a #390-promoted local in r4–r8, or
//! an f32/f64 param homed in an S/D register on a hard-float target — pushes
//! THE HOME REGISTER ITSELF onto the operand stack, uncopied. Every consumer
//! that later WRITES that register through any path other than a
//! `local.set`/`local.tee` of that same local has silently overwritten the
//! local. Three consumers were found one at a time, each as a silent wrong
//! answer: the bulk-memory walking pointer (#677), the get→set→use WAR
//! hazard (#989), the if/else join (#1189). Each got a guard; none of them
//! answered the question "how many others are there?".
//!
//! THIS MODULE answers it mechanically, over the EMITTED STREAM rather than
//! over the selector's source arms — a wildcard `_ =>` an author did not walk
//! is a hole in a source-level enumeration (the `writes_sp` 175-of-222 hole,
//! #946), but it cannot hide an instruction that was actually emitted:
//!
//!   for every emitted instruction attributed to wasm op `idx`
//!     for every GP/VFP register it WRITES ([`gp_defs`] / [`vfp_defs`],
//!         exhaustive over `ArmOp` with NO wildcard arm)
//!       if that register is the HOME of local `p`
//!          and `p` is still READ at some op `> idx` (loop-back-edge
//!              extended, the #663 rule — a read inside a loop is re-executed
//!              by every iteration)
//!          and the op at `idx` is not `local.set p` / `local.tee p`
//!       then this instruction is a #1189-class write.
//!
//! The liveness here is deliberately CONSERVATIVE and INDEPENDENT of the
//! selector's own `param_last_read`: it treats no `local.set` as a kill (a
//! set on one arm of a branch does not dominate the merge read, #990), so a
//! false positive is possible in principle and a false negative is not —
//! every hit is then either a miscompile or a shape to explain and pin.
//!
//! WHAT IT CANNOT SEE, stated so it is not over-claimed: (1) instructions
//! with `source_line: None` (prologue/epilogue and any mid-body emission an
//! author forgot to attribute — [`audit`] reports their count so a corpus run
//! can pin it); (2) HIDDEN scratch inside an encoder expansion (the #1021
//! `POPCNT`→R11 class, VCVT's transit S-register) — those never name a home
//! register in the `ArmOp` and are the expansion-canary gates' domain;
//! (3) the optimized selector (`ir_to_arm`, no per-op attribution) — pinned
//! by the execution half of the oracle instead.
//!
//! The audit is BYTE-INVISIBLE: it reads the finished stream and either
//! returns nothing or turns the compile into a loud decline (under
//! `SYNTH_HOME_ALIAS_AUDIT`). It never rewrites an instruction.

use crate::ArmInstruction;
use crate::rules::{ArmOp, Reg, VfpReg};
use synth_core::WasmOp;

/// The AAPCS caller-saved core registers a `BL`/`BLX`/`Call` may clobber.
/// None of them is ever a promoted-local home (r4–r8) and a call-containing
/// function frame-backs its params (#193/#204), so listing them costs nothing
/// and states the clobber where a future "keep a param in r0 across a leaf
/// call" change would trip it.
const CALL_CLOBBERS: [Reg; 6] = [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R12, Reg::LR];

/// Every CORE register `op` writes. Exhaustive over `ArmOp` — a new variant
/// fails compilation here until its writes are stated. Explicit destination
/// fields only (plus the documented fixed clobbers of a call): a hidden
/// expansion scratch is outside this table by design (see module doc).
pub fn gp_defs(op: &ArmOp) -> Vec<Reg> {
    use ArmOp::*;
    match op {
        // ── rd = rn <op> op2 / rm ─────────────────────────────────────────
        Add { rd, .. }
        | Sub { rd, .. }
        | Adds { rd, .. }
        | Adc { rd, .. }
        | Subs { rd, .. }
        | Sbc { rd, .. }
        | Mul { rd, .. }
        | Sdiv { rd, .. }
        | Udiv { rd, .. }
        | Mls { rd, .. }
        | Mla { rd, .. }
        | And { rd, .. }
        | Orr { rd, .. }
        | Eor { rd, .. }
        | Lsl { rd, .. }
        | Lsr { rd, .. }
        | Asr { rd, .. }
        | Ror { rd, .. }
        | LslReg { rd, .. }
        | LsrReg { rd, .. }
        | AsrReg { rd, .. }
        | RorReg { rd, .. }
        | Rsb { rd, .. }
        | Clz { rd, .. }
        | Rbit { rd, .. }
        | Popcnt { rd, .. }
        | Sxtb { rd, .. }
        | Sxth { rd, .. }
        | Uxtb { rd, .. }
        | Uxth { rd, .. }
        | Mov { rd, .. }
        | Mvn { rd, .. }
        | Movw { rd, .. }
        | Movt { rd, .. }
        | MovwSym { rd, .. }
        | MovtSym { rd, .. }
        | LdrSym { rd, .. } => vec![*rd],
        Umull { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],

        // ── compares / stores / pure control flow: no core register written ─
        Cmp { .. } | Cmn { .. } => vec![],
        Str { .. } | Strb { .. } | Strh { .. } => vec![],
        Label { .. }
        | B { .. }
        | BOffset { .. }
        | BCondOffset { .. }
        | Bhs { .. }
        | Blo { .. }
        | Bcc { .. }
        | Bx { .. }
        | Push { .. }
        | Nop
        | Udf { .. } => vec![],

        // ── loads ─────────────────────────────────────────────────────────
        Ldr { rd, .. }
        | Ldrb { rd, .. }
        | Ldrsb { rd, .. }
        | Ldrh { rd, .. }
        | Ldrsh { rd, .. } => {
            vec![*rd]
        }
        MemorySize { rd } => vec![*rd],
        MemoryGrow { rd, .. } => vec![*rd],

        // ── calls: the named result register plus the AAPCS clobber set ───
        Bl { .. } | Blx { .. } => CALL_CLOBBERS.to_vec(),
        Call { rd, .. } | CallIndirect { rd, .. } => {
            let mut v = CALL_CLOBBERS.to_vec();
            if !v.contains(rd) {
                v.push(*rd);
            }
            v
        }
        Pop { regs } => regs.clone(),

        // ── flag materialisation / selects ────────────────────────────────
        SetCond { rd, .. } | I64SetCond { rd, .. } | I64SetCondZ { rd, .. } => vec![*rd],
        SelectMove { rd, .. } | Select { rd, .. } => vec![*rd],

        // ── high-level pseudo-ops ─────────────────────────────────────────
        LocalGet { rd, .. } | LocalTee { rd, .. } | GlobalGet { rd, .. } => vec![*rd],
        LocalSet { .. } | GlobalSet { .. } => vec![],
        BrTable { rd, .. } => vec![*rd],

        // ── i64 pair results ──────────────────────────────────────────────
        I64Mul { rd_lo, rd_hi, .. }
        | I64Shl { rd_lo, rd_hi, .. }
        | I64ShrS { rd_lo, rd_hi, .. }
        | I64ShrU { rd_lo, rd_hi, .. } => vec![*rd_lo, *rd_hi],
        I64Add { rdlo, rdhi, .. }
        | I64Sub { rdlo, rdhi, .. }
        | I64DivS { rdlo, rdhi, .. }
        | I64DivU { rdlo, rdhi, .. }
        | I64RemS { rdlo, rdhi, .. }
        | I64RemU { rdlo, rdhi, .. }
        | I64And { rdlo, rdhi, .. }
        | I64Or { rdlo, rdhi, .. }
        | I64Xor { rdlo, rdhi, .. }
        | I64Rotl { rdlo, rdhi, .. }
        | I64Rotr { rdlo, rdhi, .. }
        | I64Const { rdlo, rdhi, .. }
        | I64Ldr { rdlo, rdhi, .. }
        | I64ExtendI32S { rdlo, rdhi, .. }
        | I64ExtendI32U { rdlo, rdhi, .. }
        | I64Extend8S { rdlo, rdhi, .. }
        | I64Extend16S { rdlo, rdhi, .. }
        | I64Extend32S { rdlo, rdhi, .. }
        | I64ReinterpretF64 { rdlo, rdhi, .. }
        | I64TruncF64S { rdlo, rdhi, .. }
        | I64TruncF64U { rdlo, rdhi, .. } => vec![*rdlo, *rdhi],
        I64Str { .. } => vec![],
        I64Clz { rd, .. }
        | I64Ctz { rd, .. }
        | I64Popcnt { rd, .. }
        | I64Eqz { rd, .. }
        | I64Eq { rd, .. }
        | I64Ne { rd, .. }
        | I64LtS { rd, .. }
        | I64LtU { rd, .. }
        | I64LeS { rd, .. }
        | I64LeU { rd, .. }
        | I64GtS { rd, .. }
        | I64GtU { rd, .. }
        | I64GeS { rd, .. }
        | I64GeU { rd, .. }
        | I32WrapI64 { rd, .. } => vec![*rd],

        // ── f32: VFP-file results (see `vfp_defs`); core only for compares
        //    and float→int moves ──────────────────────────────────────────
        F32Add { .. }
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
        | F32Const { .. }
        | F32Load { .. }
        | F32Store { .. }
        | F32ConvertI32S { .. }
        | F32ConvertI32U { .. }
        | F32ConvertI64S { .. }
        | F32ConvertI64U { .. }
        | F32ReinterpretI32 { .. } => vec![],
        F32Eq { rd, .. }
        | F32Ne { rd, .. }
        | F32Lt { rd, .. }
        | F32Le { rd, .. }
        | F32Gt { rd, .. }
        | F32Ge { rd, .. }
        | I32ReinterpretF32 { rd, .. }
        | I32TruncF32S { rd, .. }
        | I32TruncF32U { rd, .. } => vec![*rd],

        // ── f64 ───────────────────────────────────────────────────────────
        F64Add { .. }
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
        | F64Const { .. }
        | F64Load { .. }
        | F64Store { .. }
        | F64ConvertI32S { .. }
        | F64ConvertI32U { .. }
        | F64ConvertI64S { .. }
        | F64ConvertI64U { .. }
        | F64PromoteF32 { .. }
        | F32DemoteF64 { .. }
        | F64ReinterpretI64 { .. } => vec![],
        F64Eq { rd, .. }
        | F64Ne { rd, .. }
        | F64Lt { rd, .. }
        | F64Le { rd, .. }
        | F64Gt { rd, .. }
        | F64Ge { rd, .. }
        | I32TruncF64S { rd, .. }
        | I32TruncF64U { rd, .. } => vec![*rd],

        // ── MVE/Helium: Q-file results; core only for lane extraction ─────
        MveLoad { .. }
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
        | MveReplaceLaneF32 { .. }
        | MveDivF32 { .. }
        | MveSqrtF32 { .. } => vec![],
        MveExtractLane { rd, .. } | MveExtractLaneF32 { rd, .. } => vec![*rd],
    }
}

/// Every VFP register `op` writes, as the S-register SLOTS it covers
/// (`S(n)` → `{n}`, `D(n)` → `{2n, 2n+1}` — the VFP aliasing rule, so an f64
/// write into `D1` is seen to clobber an f32 param homed in `S2` or `S3`).
/// Exhaustive over `ArmOp`, no wildcard. Transit registers inside a
/// conversion's expansion (`VCVT … Sd` scratch) are NOT named by the op and
/// are outside this table (module doc, item 2).
pub fn vfp_defs(op: &ArmOp) -> Vec<u8> {
    use ArmOp::*;
    let d = |r: &VfpReg| -> Vec<u8> { vfp_slots(*r) };
    match op {
        F32Add { sd, .. }
        | F32Sub { sd, .. }
        | F32Mul { sd, .. }
        | F32Div { sd, .. }
        | F32Abs { sd, .. }
        | F32Neg { sd, .. }
        | F32Sqrt { sd, .. }
        | F32Ceil { sd, .. }
        | F32Floor { sd, .. }
        | F32Trunc { sd, .. }
        | F32Nearest { sd, .. }
        | F32Min { sd, .. }
        | F32Max { sd, .. }
        | F32Copysign { sd, .. }
        | F32Const { sd, .. }
        | F32Load { sd, .. }
        | F32ConvertI32S { sd, .. }
        | F32ConvertI32U { sd, .. }
        | F32ConvertI64S { sd, .. }
        | F32ConvertI64U { sd, .. }
        | F32ReinterpretI32 { sd, .. }
        | F32DemoteF64 { sd, .. } => d(sd),
        F64Add { dd, .. }
        | F64Sub { dd, .. }
        | F64Mul { dd, .. }
        | F64Div { dd, .. }
        | F64Abs { dd, .. }
        | F64Neg { dd, .. }
        | F64Sqrt { dd, .. }
        | F64Ceil { dd, .. }
        | F64Floor { dd, .. }
        | F64Trunc { dd, .. }
        | F64Nearest { dd, .. }
        | F64Min { dd, .. }
        | F64Max { dd, .. }
        | F64Copysign { dd, .. }
        | F64Const { dd, .. }
        | F64Load { dd, .. }
        | F64ConvertI32S { dd, .. }
        | F64ConvertI32U { dd, .. }
        | F64ConvertI64S { dd, .. }
        | F64ConvertI64U { dd, .. }
        | F64PromoteF32 { dd, .. }
        | F64ReinterpretI64 { dd, .. } => d(dd),
        // Reads of the VFP file only (stores, compares, float→int).
        F32Store { .. }
        | F64Store { .. }
        | F32Eq { .. }
        | F32Ne { .. }
        | F32Lt { .. }
        | F32Le { .. }
        | F32Gt { .. }
        | F32Ge { .. }
        | F64Eq { .. }
        | F64Ne { .. }
        | F64Lt { .. }
        | F64Le { .. }
        | F64Gt { .. }
        | F64Ge { .. }
        | I32ReinterpretF32 { .. }
        | I32TruncF32S { .. }
        | I32TruncF32U { .. }
        | I64ReinterpretF64 { .. }
        | I64TruncF64S { .. }
        | I64TruncF64U { .. }
        | I32TruncF64S { .. }
        | I32TruncF64U { .. } => vec![],
        // Everything that never touches the VFP file.
        Add { .. }
        | Sub { .. }
        | Adds { .. }
        | Adc { .. }
        | Subs { .. }
        | Sbc { .. }
        | Mul { .. }
        | Umull { .. }
        | Sdiv { .. }
        | Udiv { .. }
        | Mls { .. }
        | Mla { .. }
        | And { .. }
        | Orr { .. }
        | Eor { .. }
        | Lsl { .. }
        | Lsr { .. }
        | Asr { .. }
        | Ror { .. }
        | LslReg { .. }
        | LsrReg { .. }
        | AsrReg { .. }
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
        | Mvn { .. }
        | Movw { .. }
        | Movt { .. }
        | MovwSym { .. }
        | MovtSym { .. }
        | LdrSym { .. }
        | Cmp { .. }
        | Cmn { .. }
        | Ldr { .. }
        | Str { .. }
        | Ldrb { .. }
        | Ldrsb { .. }
        | Ldrh { .. }
        | Ldrsh { .. }
        | Strb { .. }
        | Strh { .. }
        | MemorySize { .. }
        | MemoryGrow { .. }
        | Label { .. }
        | B { .. }
        | BOffset { .. }
        | BCondOffset { .. }
        | Bhs { .. }
        | Blo { .. }
        | Bcc { .. }
        | Bl { .. }
        | Bx { .. }
        | Blx { .. }
        | Push { .. }
        | Pop { .. }
        | Nop
        | Udf { .. }
        | SetCond { .. }
        | I64SetCond { .. }
        | I64SetCondZ { .. }
        | I64Mul { .. }
        | I64Shl { .. }
        | I64ShrS { .. }
        | I64ShrU { .. }
        | SelectMove { .. }
        | Select { .. }
        | LocalGet { .. }
        | LocalSet { .. }
        | LocalTee { .. }
        | GlobalGet { .. }
        | GlobalSet { .. }
        | BrTable { .. }
        | Call { .. }
        | CallIndirect { .. }
        | I64Add { .. }
        | I64Sub { .. }
        | I64DivS { .. }
        | I64DivU { .. }
        | I64RemS { .. }
        | I64RemU { .. }
        | I64And { .. }
        | I64Or { .. }
        | I64Xor { .. }
        | I64Rotl { .. }
        | I64Rotr { .. }
        | I64Clz { .. }
        | I64Ctz { .. }
        | I64Popcnt { .. }
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
        | I64Extend8S { .. }
        | I64Extend16S { .. }
        | I64Extend32S { .. }
        | I32WrapI64 { .. }
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
        | MveSqrtF32 { .. } => vec![],
    }
}

/// The S-register slot(s) a VFP register covers: `S(n)` → `[n]`,
/// `D(n)` → `[2n, 2n+1]`. Relies on the enum's declaration order
/// (`S0..=S31` then `D0..=D15`), which `vfp_slots_follow_the_aliasing_rule`
/// pins.
pub fn vfp_slots(r: VfpReg) -> Vec<u8> {
    let k = r as u8;
    if k < 32 {
        vec![k]
    } else {
        vec![2 * (k - 32), 2 * (k - 32) + 1]
    }
}

/// One register-homed local: which register file, which slot, which local,
/// and from which op index the register IS that local's home (`since`). A
/// param or a promoted local is homed from op 0; a non-param f32/f64 local
/// acquires its S/D home at its FIRST `local.set`/`local.tee` (#1069), and
/// the register is an ordinary temp before that — a write there is not a
/// write to the local.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Home {
    /// A core register (param in r0–r3, both halves of an i64 pair, or a
    /// promoted local in r4–r8).
    Gp(Reg, u32),
    /// A VFP S-register slot (an f32 param's S-register, or each half of an
    /// f64 param's D-register), valid from op `since`.
    Vfp(u8, u32, usize),
}

/// Does the write at `instrs[k]` (attributed to op `idx`) sit on a path that
/// LEAVES THE FUNCTION before any later op can run? True iff the
/// instructions attributed to the same op, from `k` onward, run STRAIGHT-LINE
/// — no label, no branch of any kind — into an inline epilogue terminator
/// (`pop {…, pc}` or `bx lr`). That is exactly how `Return` and the
/// function-level `br` are lowered (`mov r0, v; add sp; pop {r4-r8, pc}`), so
/// their result move into R0 (a param's home) can never reach a later read.
/// A `br_if` that wrote R0 BEFORE its conditional branch would not satisfy
/// this (a `Bcc` intervenes) and stays a hit — the exemption is checked on
/// the stream, not assumed from the op name.
fn write_is_terminal(instrs: &[ArmInstruction], k: usize, idx: usize) -> bool {
    for ins in &instrs[k + 1..] {
        if ins.source_line != Some(idx) {
            return false;
        }
        match &ins.op {
            ArmOp::Pop { regs } if regs.contains(&Reg::PC) => return true,
            ArmOp::Bx { rm } if *rm == Reg::LR => return true,
            ArmOp::Label { .. }
            | ArmOp::B { .. }
            | ArmOp::BOffset { .. }
            | ArmOp::BCondOffset { .. }
            | ArmOp::Bhs { .. }
            | ArmOp::Blo { .. }
            | ArmOp::Bcc { .. }
            | ArmOp::Bx { .. }
            | ArmOp::Bl { .. }
            | ArmOp::Blx { .. }
            | ArmOp::Call { .. }
            | ArmOp::CallIndirect { .. }
            | ArmOp::BrTable { .. } => return false,
            _ => {}
        }
    }
    false
}

/// A #1189-class write: instruction `instr` (index into the stream),
/// attributed to wasm op `idx`, wrote `home` while local `local` is still
/// read at op `next_read`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HomeWrite {
    pub instr: usize,
    pub idx: usize,
    pub op: String,
    pub arm: String,
    pub home: String,
    pub local: u32,
    pub last_read: usize,
}

/// What an audit run saw, so a corpus sweep can pin non-vacuity: a run that
/// audited zero attributed instructions is not evidence of anything.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AuditReport {
    pub hits: Vec<HomeWrite>,
    /// Instructions carrying a `source_line` (the audited population).
    pub attributed: usize,
    /// Instructions with `source_line: None` — NOT audited (prologue,
    /// epilogue, and any unattributed mid-body emission).
    pub unattributed: usize,
    /// Homes the audit watched (a function with none is trivially clean).
    pub homes: usize,
}

/// Last op index at which each local is read (`local.get`/`local.tee`),
/// extended to the `End` of every enclosing `Loop` to fixpoint (#663: a read
/// inside a loop is re-executed by every iteration, so the value is live
/// until the loop exits). A loop left open at stream end extends to the last
/// op. Independent re-derivation — the selector's own `param_last_read` is
/// part of what is being checked.
pub fn last_reads(wasm_ops: &[WasmOp]) -> std::collections::HashMap<u32, usize> {
    let mut last: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    for (i, op) in wasm_ops.iter().enumerate() {
        if let WasmOp::LocalGet(p) | WasmOp::LocalTee(p) = op {
            last.insert(*p, i);
        }
    }
    let mut spans: Vec<(usize, usize)> = Vec::new();
    let mut open: Vec<(bool, usize)> = Vec::new();
    for (i, op) in wasm_ops.iter().enumerate() {
        match op {
            WasmOp::Loop => open.push((true, i)),
            WasmOp::Block | WasmOp::If => open.push((false, i)),
            WasmOp::End => {
                if let Some((true, start)) = open.pop() {
                    spans.push((start, i));
                }
            }
            _ => {}
        }
    }
    for (is_loop, start) in open {
        if is_loop {
            spans.push((start, wasm_ops.len().saturating_sub(1)));
        }
    }
    for v in last.values_mut() {
        let mut changed = true;
        while changed {
            changed = false;
            for &(start, end) in &spans {
                if *v > start && *v < end {
                    *v = end;
                    changed = true;
                }
            }
        }
    }
    last
}

/// Run the audit (module doc) over a finished `select_with_stack` stream.
pub fn audit(instrs: &[ArmInstruction], wasm_ops: &[WasmOp], homes: &[Home]) -> AuditReport {
    let last = last_reads(wasm_ops);
    let mut report = AuditReport {
        homes: homes.len(),
        ..Default::default()
    };
    for (k, ins) in instrs.iter().enumerate() {
        let Some(idx) = ins.source_line else {
            report.unattributed += 1;
            continue;
        };
        report.attributed += 1;
        let op = wasm_ops.get(idx);
        let gp = gp_defs(&ins.op);
        let vfp = vfp_defs(&ins.op);
        for h in homes {
            let (written, local, home_str) = match *h {
                Home::Gp(r, p) => (gp.contains(&r), p, format!("{r:?}")),
                Home::Vfp(s, p, since) => (idx >= since && vfp.contains(&s), p, format!("S{s}")),
            };
            if !written {
                continue;
            }
            let Some(&last_read) = last.get(&local) else {
                continue;
            };
            if last_read <= idx {
                continue; // dead past this op: a harmless clobber
            }
            // The one legitimate writer of a home: the local's own set/tee.
            if matches!(op, Some(WasmOp::LocalSet(p) | WasmOp::LocalTee(p)) if *p == local) {
                continue;
            }
            // A write on a path that leaves the function (inline epilogue
            // straight ahead) cannot reach the later read.
            if write_is_terminal(instrs, k, idx) {
                continue;
            }
            report.hits.push(HomeWrite {
                instr: k,
                idx,
                op: op
                    .map(|o| format!("{o:?}"))
                    .unwrap_or_else(|| "<out of range>".into()),
                arm: format!("{:?}", ins.op),
                home: home_str,
                local,
                last_read,
            });
        }
    }
    report
}

/// The env var that arms the audit inside `select_with_stack`. Any hit turns
/// the compile into a loud decline naming the write; `verbose` additionally
/// prints one `home-alias-audit:` line per audited function to stderr so a
/// corpus sweep can pin the number of functions it actually audited (#1113:
/// a floor on work done, not on green).
pub const AUDIT_ENV: &str = "SYNTH_HOME_ALIAS_AUDIT";

/// The stderr needle every hit carries (ci grep + the corpus sweep).
pub const HIT_NEEDLE: &str = "#1189-class home-register write";

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::{MemAddr, Operand2};

    fn mov(rd: Reg, rs: Reg, line: Option<usize>) -> ArmInstruction {
        ArmInstruction {
            op: ArmOp::Mov {
                rd,
                op2: Operand2::Reg(rs),
            },
            source_line: line,
        }
    }

    /// POTENCY: the #1189 shape itself, as main emitted it — `mov r0, r1` on
    /// the else path (op 4 = `I32Const 9`… attributed to the join at `End`,
    /// op 5) while local 0 (home R0) is read again at op 6. Exactly one hit,
    /// naming the register, the local and the later read.
    #[test]
    fn planted_join_write_is_reported_1189() {
        use WasmOp::*;
        let ops = vec![
            LocalGet(0),
            If,
            LocalGet(0),
            Else,
            I32Const(9),
            End,
            LocalGet(0),
            I32Add,
        ];
        let stream = vec![
            ArmInstruction {
                op: ArmOp::Movw {
                    rd: Reg::R1,
                    imm16: 9,
                },
                source_line: Some(4),
            },
            mov(Reg::R0, Reg::R1, Some(5)), // the join writes the home
            ArmInstruction {
                op: ArmOp::Adds {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R0),
                },
                source_line: Some(7),
            },
        ];
        let r = audit(&stream, &ops, &[Home::Gp(Reg::R0, 0)]);
        assert_eq!(r.hits.len(), 1, "{r:?}");
        let h = &r.hits[0];
        assert_eq!((h.instr, h.idx, h.local, h.last_read), (1, 5, 0, 6));
        assert_eq!(h.home, "R0");
        assert_eq!(r.attributed, 3);
        assert_eq!(r.unattributed, 0);
    }

    /// A write to a home whose local is DEAD past that op is not a hit —
    /// the selector legitimately reuses a dead home (yesterday's bytes).
    #[test]
    fn dead_home_write_is_not_a_hit() {
        use WasmOp::*;
        let ops = vec![LocalGet(0), I32Const(1), I32Add];
        let stream = vec![ArmInstruction {
            op: ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            },
            source_line: Some(2),
        }];
        let r = audit(&stream, &ops, &[Home::Gp(Reg::R0, 0)]);
        assert!(r.hits.is_empty(), "{r:?}");
    }

    /// The local's OWN `local.set`/`local.tee` is the one legitimate writer.
    /// A set of a DIFFERENT local that lands on this home is still a hit.
    #[test]
    fn own_set_is_exempt_other_locals_set_is_not() {
        use WasmOp::*;
        let ops = vec![
            I32Const(5),
            LocalSet(0),
            LocalGet(0),
            LocalSet(1),
            LocalGet(0),
        ];
        let own = vec![mov(Reg::R0, Reg::R4, Some(1))];
        assert!(audit(&own, &ops, &[Home::Gp(Reg::R0, 0)]).hits.is_empty());
        let other = vec![mov(Reg::R0, Reg::R4, Some(3))]; // `local.set 1` wrote R0
        let r = audit(&other, &ops, &[Home::Gp(Reg::R0, 0)]);
        assert_eq!(r.hits.len(), 1, "{r:?}");
        assert_eq!(r.hits[0].idx, 3);
    }

    /// #663: a read INSIDE a loop is live until the loop's End, so a write to
    /// the home later in the same loop body (linearly after the last read) is
    /// a hit — the back-edge re-executes the read.
    #[test]
    fn loop_back_edge_extends_liveness() {
        use WasmOp::*;
        //           0     1           2         3          4     5        6
        let ops = vec![Loop, LocalGet(0), I32Eqz, BrIf(0), I32Const(1), Drop, End];
        let stream = vec![mov(Reg::R0, Reg::R4, Some(4))];
        let r = audit(&stream, &ops, &[Home::Gp(Reg::R0, 0)]);
        assert_eq!(r.hits.len(), 1, "{r:?}");
        assert_eq!(r.hits[0].last_read, 6, "extended to the loop End");
        // The same write AFTER the loop is dead.
        let after = vec![Loop, LocalGet(0), I32Eqz, BrIf(0), End, I32Const(1), Drop];
        let stream = vec![mov(Reg::R0, Reg::R4, Some(5))];
        assert!(
            audit(&stream, &after, &[Home::Gp(Reg::R0, 0)])
                .hits
                .is_empty()
        );
    }

    /// An i64 pair home: writing the HI half through an unrelated op is a hit
    /// on the pair's local; an f64 D-register home is hit by an f32 write to
    /// either of its S halves.
    #[test]
    fn pair_and_vfp_halves_are_watched() {
        use WasmOp::*;
        let ops = vec![LocalGet(0), I64Const(1), I64Add, LocalGet(0), Drop];
        let hi_write = vec![ArmInstruction {
            op: ArmOp::Movw {
                rd: Reg::R1,
                imm16: 1,
            },
            source_line: Some(1),
        }];
        let homes = [Home::Gp(Reg::R0, 0), Home::Gp(Reg::R1, 0)];
        let r = audit(&hi_write, &ops, &homes);
        assert_eq!(r.hits.len(), 1, "{r:?}");
        assert_eq!(r.hits[0].home, "R1");

        let fops = vec![LocalGet(0), F32Const(1.0), F32Add, LocalGet(0), Drop];
        let s3_write = vec![ArmInstruction {
            op: ArmOp::F32Const {
                sd: VfpReg::S3,
                value: 1.0,
            },
            source_line: Some(1),
        }];
        let dhomes: Vec<Home> = vfp_slots(VfpReg::D1)
            .into_iter()
            .map(|s| Home::Vfp(s, 0, 0))
            .collect();
        let r = audit(&s3_write, &fops, &dhomes);
        assert_eq!(r.hits.len(), 1, "{r:?}");
        assert_eq!(r.hits[0].home, "S3");
    }

    /// #1069: a non-param float local acquires its S-home at its FIRST def.
    /// Before `since` the register is a plain temp — `f32.epsilon` in the
    /// spec suite materialises `f32.const 1.0` into S0 at op 0 and only later
    /// homes local 1 there; that is not a write to local 1. From `since` on,
    /// the same write IS a hit.
    #[test]
    fn vfp_home_is_watched_only_from_its_first_def() {
        use WasmOp::*;
        //             0              1           2              3           4
        let ops = vec![F32Const(1.0), LocalSet(1), F32Const(2.0), LocalGet(1), Drop];
        let early = vec![ArmInstruction {
            op: ArmOp::F32Const {
                sd: VfpReg::S0,
                value: 1.0,
            },
            source_line: Some(0),
        }];
        assert!(audit(&early, &ops, &[Home::Vfp(0, 1, 1)]).hits.is_empty());
        let late = vec![ArmInstruction {
            op: ArmOp::F32Const {
                sd: VfpReg::S0,
                value: 2.0,
            },
            source_line: Some(2),
        }];
        assert_eq!(audit(&late, &ops, &[Home::Vfp(0, 1, 1)]).hits.len(), 1);
    }

    /// A `Return` (or function-level `br`) moves its result into R0 and runs
    /// straight into an INLINE epilogue — that write cannot reach a later
    /// read, and the audit proves it on the stream (`pop {…, pc}` ahead with
    /// nothing in between) rather than trusting the op name: the same move
    /// followed by a CONDITIONAL branch (a `br_if` shape) stays a hit.
    #[test]
    fn terminal_return_write_is_exempt_conditional_is_not() {
        use WasmOp::*;
        //             0            1   2            3        4    5           6
        let ops = vec![
            LocalGet(0),
            If,
            I32Const(-1),
            Return,
            End,
            LocalGet(0),
            Drop,
        ];
        let pop = ArmInstruction {
            op: ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            },
            source_line: Some(3),
        };
        let terminal = vec![
            mov(Reg::R0, Reg::R4, Some(3)),
            ArmInstruction {
                op: ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(8),
                },
                source_line: Some(3),
            },
            pop.clone(),
        ];
        assert!(
            audit(&terminal, &ops, &[Home::Gp(Reg::R0, 0)])
                .hits
                .is_empty()
        );

        // The move, then a conditional branch, then the epilogue: the
        // fall-through path keeps running with R0 clobbered — a hit.
        let conditional = vec![
            mov(Reg::R0, Reg::R4, Some(3)),
            ArmInstruction {
                op: ArmOp::Bcc {
                    cond: crate::rules::Condition::EQ,
                    label: "skip".into(),
                },
                source_line: Some(3),
            },
            pop.clone(),
        ];
        assert_eq!(
            audit(&conditional, &ops, &[Home::Gp(Reg::R0, 0)])
                .hits
                .len(),
            1
        );

        // The move with the epilogue attributed to a DIFFERENT op (not the
        // same lowering) is not proven terminal either.
        let mut other = terminal.clone();
        other[2].source_line = Some(4);
        assert_eq!(audit(&other, &ops, &[Home::Gp(Reg::R0, 0)]).hits.len(), 1);
    }

    /// Unattributed instructions are counted, never audited — the report
    /// says so, so a sweep can pin that the population did not quietly
    /// shrink.
    #[test]
    fn unattributed_instructions_are_counted_not_audited() {
        use WasmOp::*;
        let ops = vec![LocalGet(0), LocalGet(0), I32Add];
        let stream = vec![
            ArmInstruction {
                op: ArmOp::Push {
                    regs: vec![Reg::R4, Reg::LR],
                },
                source_line: None,
            },
            mov(Reg::R0, Reg::R4, None), // an unattributed home write
            ArmInstruction {
                op: ArmOp::Str {
                    rd: Reg::R0,
                    addr: MemAddr::imm(Reg::SP, 0),
                },
                source_line: Some(2),
            },
        ];
        let r = audit(&stream, &ops, &[Home::Gp(Reg::R0, 0)]);
        assert!(r.hits.is_empty());
        assert_eq!((r.attributed, r.unattributed, r.homes), (1, 2, 1));
    }

    #[test]
    fn vfp_slots_follow_the_aliasing_rule() {
        assert_eq!(vfp_slots(VfpReg::S0), vec![0]);
        assert_eq!(vfp_slots(VfpReg::S31), vec![31]);
        assert_eq!(vfp_slots(VfpReg::D0), vec![0, 1]);
        assert_eq!(vfp_slots(VfpReg::D1), vec![2, 3]);
        assert_eq!(vfp_slots(VfpReg::D15), vec![30, 31]);
    }

    /// Stores are SOURCES, not defs — the `rd` field name must not be read as
    /// a write. Calls carry the AAPCS clobber set. A `Pop` writes its list.
    #[test]
    fn defs_table_spot_checks() {
        assert!(
            gp_defs(&ArmOp::Str {
                rd: Reg::R0,
                addr: MemAddr::imm(Reg::SP, 0)
            })
            .is_empty()
        );
        assert!(
            gp_defs(&ArmOp::I64Str {
                rdlo: Reg::R0,
                rdhi: Reg::R1,
                addr: MemAddr::imm(Reg::SP, 0)
            })
            .is_empty()
        );
        assert_eq!(
            gp_defs(&ArmOp::Umull {
                rdlo: Reg::R2,
                rdhi: Reg::R3,
                rn: Reg::R0,
                rm: Reg::R1
            }),
            vec![Reg::R2, Reg::R3]
        );
        let call = gp_defs(&ArmOp::Call {
            rd: Reg::R0,
            func_idx: 1,
        });
        assert!(call.contains(&Reg::R0) && call.contains(&Reg::R3) && call.contains(&Reg::LR));
        assert_eq!(
            gp_defs(&ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC]
            }),
            vec![Reg::R4, Reg::PC]
        );
        assert!(
            gp_defs(&ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0)
            })
            .is_empty()
        );
        assert_eq!(
            gp_defs(&ArmOp::F32Eq {
                rd: Reg::R5,
                sn: VfpReg::S0,
                sm: VfpReg::S1
            }),
            vec![Reg::R5]
        );
        assert_eq!(
            vfp_defs(&ArmOp::F64Add {
                dd: VfpReg::D2,
                dn: VfpReg::D0,
                dm: VfpReg::D1
            }),
            vec![4, 5]
        );
        assert!(
            vfp_defs(&ArmOp::F32Store {
                sd: VfpReg::S0,
                addr: MemAddr::imm(Reg::SP, 0)
            })
            .is_empty()
        );
    }

    /// #946 discipline: the two tables are exhaustive `match`es with NO
    /// wildcard and NO bare-identifier catch-all — the compiler enforces
    /// exhaustiveness, this pins that nobody re-adds `_ =>` to satisfy it.
    #[test]
    fn defs_tables_have_no_wildcard_arm() {
        let src = include_str!("home_alias.rs");
        let code: String = src
            .lines()
            .map(|l| l.split("//").next().unwrap_or(l))
            .collect::<Vec<_>>()
            .join("\n");
        for name in ["pub fn gp_defs", "pub fn vfp_defs"] {
            let start = code.find(name).expect(name);
            let body = &code[start..];
            let open = body.find('{').unwrap();
            let mut depth = 0i32;
            let mut end = open;
            for (i, c) in body[open..].char_indices() {
                match c {
                    '{' => depth += 1,
                    '}' => {
                        depth -= 1;
                        if depth == 0 {
                            end = open + i;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let fn_body = &body[open..=end];
            assert!(
                !fn_body.contains("_ =>") && !fn_body.contains("_=>"),
                "{name}: a wildcard arm regrew — state the effect per variant"
            );
            // Every variant name of the enum must be spelled out in the body.
            let rules = include_str!("rules.rs");
            let enum_start = rules.find("pub enum ArmOp {").unwrap();
            let enum_body = &rules[enum_start..];
            let enum_end = enum_body.find("\n}\n").unwrap();
            let mut variants = 0usize;
            for line in enum_body[..enum_end].lines().skip(1) {
                let t = line.trim();
                if t.starts_with("//") || t.is_empty() {
                    continue;
                }
                // A variant line starts at 4-space indent with a capital.
                if line.starts_with("    ")
                    && !line.starts_with("     ")
                    && t.chars().next().is_some_and(|c| c.is_ascii_uppercase())
                {
                    let vname: String = t
                        .chars()
                        .take_while(|c| c.is_ascii_alphanumeric())
                        .collect();
                    variants += 1;
                    assert!(
                        fn_body.contains(&format!("{vname} {{"))
                            || fn_body.contains(&format!("{vname}\n"))
                            || fn_body.contains(&format!("| {vname}")),
                        "{name}: variant {vname} not named in the table"
                    );
                }
            }
            assert_eq!(
                variants, 222,
                "ArmOp variant count drifted from the #615/#946 pin"
            );
        }
    }
}
