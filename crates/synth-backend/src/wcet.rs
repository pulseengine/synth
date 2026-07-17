//! #778 (v0.46 Wave-1 Lane 2) — sound static WCET-bound computation over the
//! final Thumb-2 instruction stream.
//!
//! This module owns the two soundness-critical pieces the [`synth_core::wcet`]
//! schema is populated from:
//!
//! 1. [`op_worst_case_cycles`] — a per-`ArmOp` DOCUMENTED WORST-CASE cycle count
//!    for the Cortex-M3 / Cortex-M4(F) in-order pipeline under a zero-wait-state
//!    instruction memory. Every data-dependent op takes its MAXIMUM (`SDIV`/`UDIV`
//!    → 12, not the 2-cycle best case). The match is EXHAUSTIVE with NO wildcard,
//!    so a newly-added `ArmOp` variant fails to compile until it is consciously
//!    given a worst-case number or classified as a looped expansion — the same
//!    tripwire discipline as `estimator_encoder_agreement.rs`.
//!
//! 2. [`function_wcet`] — the classifier + summation. It reconstructs byte
//!    positions over the final `arm_instrs` list (the same list the encoder
//!    consumes), detects any residual label branch, any call, and any op whose
//!    encoder expansion contains an internal runtime loop; on any of these it
//!    DECLINES. Backward branches (loops) are handed to the
//!    [`crate::wcet_loops`] analyzer (#778 phase 2): a loop whose trip count is
//!    STATICALLY PROVEN (const-initialized counter, const step, const bound,
//!    canonical single-backward-branch shape) multiplies its instructions'
//!    worst cases by the proven execution count; anything unproven keeps the
//!    loud `loop` decline. `--wcet-hints` entries are verified there (and
//!    rejected with machine reasons when wrong/unverifiable — never trusted).
//!
//! The whole computation is a pure observation of an already-decided instruction
//! list: it touches no `.text`, so the emitted bytes are byte-identical whether or
//! not a bound is computed (frozen-safe).
//!
//! ## Cycle numbers — provenance
//!
//! The per-instruction worst cases below are the MAX over the documented
//! Cortex-M3 and Cortex-M4 figures (ARM Cortex-M3 / Cortex-M4 Technical Reference
//! Manuals, "Instruction timings"), because a SINGLE shared table serves both
//! cover cores (STM32F100 = M3, NUCLEO-G474RE = M4). Where the two diverge the M3
//! (slower) number wins: `MLA`/`MLS` = 2 (M3; 1 on M4), `UMULL` = 5 (M3 3–5; 1 on
//! M4). Loads/stores are 2 cycles (pipelined single access), taken branches add a
//! pipeline-refill penalty (up to 3 → we use the worst), `SDIV`/`UDIV` are 2–12
//! (we use 12). Where an op EXPANDS to a fixed straight-line
//! sequence (Popcnt SWAR, i64 shift/rotate/clz/ctz/setcond), the entry is a
//! conservative over-estimate of that sequence's summed worst case; each such
//! entry is justified inline. Since a loop-free function executes every
//! instruction at most once, a per-instruction over-estimate keeps the SUM sound.

use synth_core::wcet::{
    WcetCallSite, WcetDecline, WcetFunction, WcetFunctionHints, WcetIntermediate,
};
use synth_synthesis::{ArmInstruction, ArmOp};

use crate::wcet_loops::{LoopAnalysis, analyze_loops};

/// The worst-case cycle cost of a DIRECT `BL`/`BLX` call instruction itself
/// (the branch-with-link, EXCLUDING the callee body which is composed separately).
///
/// PROVENANCE — MAX over {Cortex-M3, Cortex-M4}. Both TRMs time `BL`/`BLX` as
/// `1 + P` where `P` is the pipeline-refill penalty, "1 to 3 depending on the
/// alignment and width of the target instruction, and whether the processor manages
/// to speculate the address early" (ARM Cortex-M3 / Cortex-M4 Technical Reference
/// Manuals, instruction-timing summary). The worst case is `1 + 3 = 4`. This is the
/// SAME branch-with-refill class the table already prices for `Bx`/`BOffset`/
/// `BCondOffset` (also 4), so a direct call's branch overhead is 4 cycles. The
/// callee's own return (`BX LR` / `POP {PC}`) is already counted inside the
/// callee's own bound, so NO return penalty is added here (that would double-count).
///
/// SOUND-CRITICAL: pinned in `claims.yaml` (SYNTH-WCET-CYCLE-MODEL). Editing it
/// reddens the claim-check and forces a conscious re-derivation against the TRM.
const BL_BLX_CALL_OVERHEAD_CYCLES: u64 = 4;

/// A conservative per-16-bit-halfword ceiling for a straight-line multi-byte
/// encoder expansion built from ALU/shift/compare/move/short-multiply plus the
/// occasional small register-list `PUSH`/`POP`. It is sound iff EVERY instruction
/// in a priced expansion has a worst case ≤ `CEIL × (its halfword span)`:
///
///  - a 16-bit (1-halfword) ALU/shift/mov/cmp/forward-branch is ≤ 3 cycles → ≤ 5;
///  - a 32-bit (2-halfword) op — including UMULL/MLA (M3 worst ≈ 5) — is priced at
///    2×5 = 10 ≥ its worst;
///  - a 16-bit `PUSH`/`POP` of up to 4 registers is 1+4 = 5 cycles → exactly ≤ 5
///    (the audited expansions push at most 3 registers, so this holds with margin;
///    the i64 software div/rem, which pushes 4, is a LoopedExpansion decline and
///    is never priced here).
///
/// Hardware `SDIV`/`UDIV` (up to 12) do NOT appear in any priced expansion — the
/// only i64 division is the looped-expansion decline — so no single instruction
/// exceeds the ceiling. 5 cycles/halfword is therefore a sound over-estimate of any
/// priced straight-line block; the block executes exactly once in a loop-free
/// function, so summing the ceiling stays sound. Audited against `arm_encoder.rs`
/// (#778): the only 16-bit `PUSH`/`POP` in a priced arm is I64Popcnt's 3-register
/// `0xB438`/`0xBC38`.
const STRAIGHTLINE_CEIL_PER_HALFWORD: u64 = 5;

/// Worst-case cycles for a straight-line multi-byte expansion, sized from the
/// op's ENCODER byte length (via `estimate_arm_byte_size`, which the
/// `estimator_encoder_agreement` oracle pins exactly to the real encoder). Using
/// the estimator rather than a hand literal makes the bound provably ≥ the real
/// straight-line cost and self-maintaining: a future encoder change to a priced
/// expansion moves the estimator and the bound rides it.
fn straightline_expansion(op: &ArmOp) -> u64 {
    let byte_len = synth_synthesis::estimate_arm_byte_size(op) as u64;
    (byte_len / 2) * STRAIGHTLINE_CEIL_PER_HALFWORD
}

/// Classification of an `ArmOp` for the cycle model.
enum OpCost {
    /// A single-execution op with this documented worst-case cycle count.
    Cycles(u64),
    /// The op's encoder expansion contains an internal RUNTIME loop (emitted once,
    /// executed many times). A straight sum of its body bytes would undercount, so
    /// any function containing it is declined.
    LoopedExpansion,
    /// The op is not lowered onto the sound Thumb-2 scalar-integer path this model
    /// covers (VFP scalar/MVE vector/off-path pseudo-ops). A function containing it
    /// is declined rather than guessed.
    Unmodeled,
}

/// The DOCUMENTED WORST-CASE cycle cost of one `ArmOp`, or a decline classification.
///
/// EXHAUSTIVE — no wildcard. A new `ArmOp` variant will not compile until it is
/// consciously classified here.
#[allow(clippy::match_same_arms)] // grouping by cycle count is clearer than merging
fn op_cost(op: &ArmOp) -> OpCost {
    use ArmOp::*;
    use OpCost::{Cycles, LoopedExpansion, Unmodeled};

    match op {
        // --- 1-cycle data-processing (register/immediate ALU, moves, extends) ---
        Add { .. }
        | Sub { .. }
        | Adds { .. }
        | Subs { .. }
        | Adc { .. }
        | Sbc { .. }
        | And { .. }
        | Orr { .. }
        | Eor { .. }
        | Rsb { .. }
        | Mvn { .. } => Cycles(1),
        Mov { .. } | Movw { .. } | Movt { .. } | MovwSym { .. } | MovtSym { .. } => Cycles(1),
        Clz { .. } | Rbit { .. } => Cycles(1),
        Sxtb { .. } | Sxth { .. } | Uxtb { .. } | Uxth { .. } => Cycles(1),
        Cmp { .. } | Cmn { .. } => Cycles(1),
        // Shifts: immediate and register forms both retire in 1 cycle on M4.
        Lsl { .. }
        | Lsr { .. }
        | Asr { .. }
        | Ror { .. }
        | LslReg { .. }
        | LsrReg { .. }
        | AsrReg { .. }
        | RorReg { .. } => Cycles(1),

        // --- multiply / multiply-accumulate: MAX over {M3, M4} ---
        // MUL is single-cycle on M3 and M4. MLA/MLS: 1 on M4E, but 2 on M3
        // (ARMv7-M) — take 2 so the single shared table is sound on both cover
        // cores (STM32F100 = M3, NUCLEO-G474RE = M4).
        Mul { .. } => Cycles(1),
        Mls { .. } | Mla { .. } => Cycles(2),
        // UMULL long multiply: 1 cycle on M4, but 3–5 (data-dependent) on M3.
        // Take the M3 MAX (5). REACHABLE: synth emits UMULL for the
        // reciprocal-multiply divide-by-constant (the cost-gate was deleted, PR
        // #322), so `x / 10` on `-t cortex-m3` must not undercount.
        Umull { .. } => Cycles(5),

        // --- hardware divide: DATA-DEPENDENT 2..12, take the MAX (12) ---
        Sdiv { .. } | Udiv { .. } => Cycles(12),

        // --- loads / stores: 2 cycles (pipelined single access) ---
        Ldr { .. }
        | Str { .. }
        | Ldrb { .. }
        | Ldrh { .. }
        | Ldrsb { .. }
        | Ldrsh { .. }
        | Strb { .. }
        | Strh { .. }
        | LdrSym { .. } => Cycles(2),

        // --- branches: 1 (not taken) + up to 3 pipeline-refill on taken → 4 ---
        // We use the worst case (taken) unconditionally; a not-taken conditional is
        // strictly cheaper, so the over-estimate is sound.
        BOffset { .. } | BCondOffset { .. } | Bx { .. } => Cycles(4),

        // --- calls: the BRANCH-WITH-LINK overhead only (1 + up-to-3 refill = 4).
        // The callee body is composed in separately over the direct call graph
        // (#778 phase 3); a DIRECT `Bl func_N` to a local bounded callee is priced
        // as this overhead + callee bound. An INDIRECT `Blx <reg>` still declines
        // (callee not statically known) — that classification is made in
        // `classify_call` / the intermediate builder, not here. ---
        Bl { .. } | Blx { .. } => Cycles(BL_BLX_CALL_OVERHEAD_CYCLES),

        // --- select / predication ---
        // SetCond = IT + MOV + MOV (6 B, 3 insns); SelectMove = IT + MOV (4 B).
        SetCond { .. } => Cycles(3),
        SelectMove { .. } => Cycles(2),
        Select { .. } => Unmodeled, // pseudo, lowered upstream — never in final stream

        // --- Popcnt: fixed SWAR bit-twiddle, straight-line. Sized by the
        // estimator (encoder-pinned, below) — never a hand literal. ---
        Popcnt { .. } => Cycles(straightline_expansion(op)),
        // UDF trap: 1 cycle to fault (worst-case reach; execution ends there).
        Udf { .. } => Cycles(1),

        // === i64 SOFTWARE div/rem: internal 64-iteration runtime loop → decline ===
        I64DivU { .. } | I64DivS { .. } | I64RemU { .. } | I64RemS { .. } => LoopedExpansion,

        // === i64 straight-line expansions (fixed byte size, NO internal loop) ===
        // Sized by `estimate_arm_byte_size` — NOT a hand-transcribed literal. That
        // estimator is pinned EXACTLY to the real encoder length for every one of
        // these ops by the `estimator_encoder_agreement` oracle, so
        // `(len/2) × CEIL` is provably ≥ the real straight-line cost AND cannot go
        // stale: a future encoder change to any of these expansions moves the
        // estimator (or breaks the oracle) and the bound tracks it automatically —
        // exactly the drift a hand literal could not catch.
        I64SetCond { .. }
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
        | I64Extend32S { .. } => Cycles(straightline_expansion(op)),

        // === prologue/epilogue stack ops: real, straight-line, single-execution ===
        // Cortex-M4 STM/LDM (PUSH/POP) = 1 + N cycles for N registers. A POP that
        // writes PC is also a branch (pipeline refill up to 3). We price BOTH as
        // `1 + N + 3` — a sound over-estimate for PUSH (no refill) and the exact
        // worst case for POP-to-PC (function return, the common epilogue).
        Push { regs } => Cycles(1 + regs.len() as u64 + 3),
        Pop { regs } => Cycles(1 + regs.len() as u64 + 3),

        // === off-path pseudo-ops ===
        // Label/Nop are zero-cost real placeholders. The rest are verification-only
        // pseudo-ops the encoder REFUSES (Ok-or-Err, #615): a compile that reached
        // one would already have errored, so they cannot appear in a stream we are
        // pricing. Classified Unmodeled = decline as a belt-and-braces guard.
        Label { .. } | Nop => Cycles(0),
        B { .. } | Bcc { .. } | Bhs { .. } | Blo { .. } => Unmodeled, // residual label branch
        LocalGet { .. }
        | LocalSet { .. }
        | LocalTee { .. }
        | GlobalGet { .. }
        | GlobalSet { .. } => Unmodeled,
        Call { .. } | CallIndirect { .. } | BrTable { .. } => Unmodeled,
        MemorySize { .. } | MemoryGrow { .. } => Unmodeled,

        // === i64 pseudo binops lowered to 32-bit pairs upstream (never in stream) ===
        I64Add { .. }
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
        | I32WrapI64 { .. } => Unmodeled,

        // === all F32/F64 scalar VFP + all MVE vector: not on the sound integer path ===
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
        | F32DemoteF64 { .. }
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
        | MveSqrtF32 { .. } => Unmodeled,
    }
}

/// The documented worst-case cycle cost of `op`, for the fixture gate and any
/// straight-line summation. Panics if `op` is not a straight-line priced op
/// (looped/unmodeled) — callers on the sound path must classify first via
/// [`function_wcet`], which declines before it would sum such an op.
pub fn op_worst_case_cycles(op: &ArmOp) -> u64 {
    match op_cost(op) {
        OpCost::Cycles(c) => c,
        OpCost::LoopedExpansion | OpCost::Unmodeled => {
            panic!("op_worst_case_cycles called on a non-straight-line op: {op:?}")
        }
    }
}

/// Map a target `triple` to the SOUND core class the zero-wait per-op table holds
/// for, or `None` if the core is not soundly summable and must be declined.
///
/// SOUNDNESS NOTE — the `-eabihf` ambiguity: the Cortex-M4F, Cortex-M7 and
/// Cortex-M7dp `TargetSpec`s ALL carry the triple `thumbv7em-none-eabihf`, so once
/// inside compilation the triple alone CANNOT distinguish the in-order M4F (sound
/// to sum) from the dual-issue M7 (NOT sound: cache wait-states can make actual
/// cycles exceed a zero-wait sum). Rather than risk pricing an M7 with the M4
/// table, this DECLINES the ambiguous `-eabihf` triple entirely. Only the two
/// unambiguous integer triples are accepted: `thumbv7m-none-eabi` → Cortex-M3
/// (ARMv7-M, in-order, no FPU) and `thumbv7em-none-eabi` → Cortex-M4 no-FPU
/// (ARMv7E-M, in-order). This is conservative for M4F (which is soundly summable)
/// but never unsound — distinguishing M4F from M7 needs a discriminator the config
/// does not carry here (a named follow-up: thread the `CortexMVariant` so M4F is
/// bounded too).
pub fn sound_core_class(triple: &str) -> Option<&'static str> {
    match triple {
        "thumbv7m-none-eabi" | "cortex-m3" => Some("cortex-m3"),
        "thumbv7em-none-eabi" | "cortex-m4" => Some("cortex-m4"),
        _ => None,
    }
}

/// The classification of a call-shaped instruction for composition (#778 phase 3).
enum CallClass {
    /// A DIRECT `BL func_<idx>` to a callee that may be a local/bounded function —
    /// resolved against the module by the composer. Carries the target label.
    Direct(String),
    /// An INDIRECT call (`Blx <reg>`, `call_indirect`, or a function-pointer
    /// dispatch label such as `__meld_dispatch_import`): callee not statically
    /// known → the function DECLINES [`WcetDecline::IndirectCall`].
    Indirect,
    /// A DIRECT `BL <label>` to a runtime helper / external symbol that has NO
    /// per-function body in this module (`__aeabi_*`, a bridge, an import trampoline
    /// other than the dispatch above): cannot compose a bound → the function
    /// DECLINES [`WcetDecline::Call`].
    External,
}

/// Classify a call-shaped `ArmOp`, or `None` if `op` is not a call.
///
/// A `BL func_<idx>` is the selector's shape for a direct local call (or a direct
/// relocatable-import call, whose `func_N` symbol the ELF builder retargets to the
/// import name — that import has no body here, so the composer resolves it to
/// External and declines). `__meld_dispatch_import` is a runtime function-pointer
/// dispatch (indirect). `Blx`/`CallIndirect` are indirect by construction.
fn classify_call(op: &ArmOp) -> Option<CallClass> {
    match op {
        ArmOp::Bl { label } => {
            if label == "__meld_dispatch_import" {
                Some(CallClass::Indirect)
            } else if is_local_func_label(label) {
                Some(CallClass::Direct(label.clone()))
            } else {
                Some(CallClass::External)
            }
        }
        ArmOp::Blx { .. } | ArmOp::CallIndirect { .. } => Some(CallClass::Indirect),
        // `Call` is a pseudo-op lowered upstream; if one survived, treat it as a
        // direct call by name so composition can still resolve it (its label is a
        // function name). CallIndirect handled above.
        ArmOp::Call { func_idx, .. } => Some(CallClass::Direct(format!("func_{func_idx}"))),
        _ => None,
    }
}

/// Is `label` the selector's DIRECT-local-call shape `func_<decimal index>`?
fn is_local_func_label(label: &str) -> bool {
    label
        .strip_prefix("func_")
        .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
}

/// Scan for op-class declines that are INDEPENDENT of inter-procedural composition:
/// residual label branches, looped expansions, indirect calls, external direct
/// calls, and unmodeled ops. Direct local calls (`BL func_N`) are NOT a decline
/// here — they are recorded as call sites and resolved by the composer. Backward
/// branches (loops) are NOT a decline here either; they go to [`crate::wcet_loops`].
///
/// Returns the first composition-independent decline reason, or `None`.
fn scan_for_decline(instrs: &[ArmInstruction]) -> Option<WcetDecline> {
    for instr in instrs {
        // Call-shaped ops: only a DIRECT local call is composable; everything else
        // (indirect / external) is a composition-independent decline.
        if let Some(class) = classify_call(&instr.op) {
            match class {
                CallClass::Direct(_) => {} // composable — recorded, not declined
                CallClass::Indirect => return Some(WcetDecline::IndirectCall),
                CallClass::External => return Some(WcetDecline::Call),
            }
            continue;
        }
        // A residual label branch: direction is not statically known here.
        if matches!(
            &instr.op,
            ArmOp::B { .. } | ArmOp::Bcc { .. } | ArmOp::Bhs { .. } | ArmOp::Blo { .. }
        ) {
            return Some(WcetDecline::UnresolvedBranch);
        }
        match op_cost(&instr.op) {
            OpCost::LoopedExpansion => return Some(WcetDecline::LoopedExpansion),
            OpCost::Unmodeled => return Some(WcetDecline::UnmodeledOp),
            OpCost::Cycles(_) => {}
        }
    }
    None
}

/// Compute the sound per-function WCET result over the FINAL Thumb-2 instruction
/// stream `instrs` (the list the encoder consumes). `triple` is
/// `config.target.triple`; a non-soundly-summable core (see [`sound_core_class`])
/// declines with [`WcetDecline::UnsupportedCore`].
///
/// Returns a [`WcetFunction::Bounded`] with the summed worst-case cycles when the
/// function is proven loop-free / call-free — or when every loop's trip count is
/// statically proven (#778 phase 2) — on a soundly-summable core, else a
/// [`WcetFunction::Declined`] with a machine-readable reason.
pub fn function_wcet(name: &str, instrs: &[ArmInstruction], triple: &str) -> WcetFunction {
    function_wcet_with_hints(name, instrs, triple, None)
}

/// [`function_wcet`] with an optional UNTRUSTED `--wcet-hints` entry for this
/// function (#778 phase 2, the scry seam). Every hint is soundly verified by
/// [`crate::wcet_loops`] before use; wrong/unverifiable hints are rejected with
/// machine reasons in the returned record — never trusted into a bound.
///
/// This is the SINGLE-FUNCTION view: it collapses the phase-3 intermediate to a
/// `WcetFunction` treating every direct call as unresolvable (External → `call`
/// decline), which is the correct answer when no module context is available. The
/// module-level driver instead calls [`function_wcet_intermediate`] and composes
/// (see [`crate::wcet_compose`]).
pub fn function_wcet_with_hints(
    name: &str,
    instrs: &[ArmInstruction],
    triple: &str,
    hints: Option<&WcetFunctionHints>,
) -> WcetFunction {
    match function_wcet_intermediate(name, instrs, triple, hints) {
        WcetIntermediate::Declined {
            name,
            reason,
            hint_rejections,
        } => WcetFunction::declined_with_rejections(name, reason, hint_rejections),
        WcetIntermediate::Composable {
            name,
            own_cycles,
            instr_count,
            call_sites,
            loops,
            hint_rejections,
        } => {
            // No module context here: an unresolved direct call cannot be composed,
            // so a composable function WITH call sites declines `call`; one with no
            // calls is a genuine intra-procedural bound.
            if call_sites.is_empty() {
                WcetFunction::Bounded {
                    name,
                    cycles: own_cycles,
                    instr_count,
                    loops,
                    hint_rejections,
                }
            } else {
                WcetFunction::declined_with_rejections(name, WcetDecline::Call, hint_rejections)
            }
        }
    }
}

/// Compute the per-function WCET INTERMEDIATE (#778 phase 3): either a
/// composition-independent decline, or a [`WcetIntermediate::Composable`] whose
/// `own_cycles` prices every instruction (each `BL`'s branch overhead included) at
/// its proven execution count, with the direct call sites recorded for the composer
/// to resolve against the whole module.
///
/// `triple` is `config.target.triple`; a non-soundly-summable core declines
/// [`WcetDecline::UnsupportedCore`]. Loop trip counts are proven exactly as in
/// phase 2 (unproven loops → `loop` decline); the ONLY phase-3 change is that a
/// direct local `BL func_N` is a recorded call site instead of an immediate decline.
pub fn function_wcet_intermediate(
    name: &str,
    instrs: &[ArmInstruction],
    triple: &str,
    hints: Option<&WcetFunctionHints>,
) -> WcetIntermediate {
    let declined = |reason, hint_rejections| WcetIntermediate::Declined {
        name: name.to_string(),
        reason,
        hint_rejections,
    };
    if sound_core_class(triple).is_none() {
        return declined(WcetDecline::UnsupportedCore, Vec::new());
    }
    if let Some(reason) = scan_for_decline(instrs) {
        return declined(reason, Vec::new());
    }
    // Loop analysis: prove a trip count for every backward-branch region, or
    // keep the loud `loop` decline.
    let (multipliers, loops, hint_rejections) = match analyze_loops(instrs, hints) {
        LoopAnalysis::NoLoops { hint_rejections } => (None, Vec::new(), hint_rejections),
        LoopAnalysis::Proven {
            multipliers,
            loops,
            hint_rejections,
        } => (Some(multipliers), loops, hint_rejections),
        LoopAnalysis::Unproven { hint_rejections } => {
            return declined(WcetDecline::Loop, hint_rejections);
        }
    };
    let mult_at = |i: usize| -> u128 { multipliers.as_ref().map_or(1u128, |m| m[i]) };

    // Every instruction's documented worst case × its proven worst-case execution
    // count (1 everywhere for a loop-free function). u128 through the sum so deep
    // nesting cannot silently wrap; an astronomically large product declines rather
    // than emitting a truncated (unsound) number. Each direct `BL` contributes its
    // branch overhead here (via op_worst_case_cycles); the callee body is added by
    // the composer.
    let cycles_wide: u128 = instrs
        .iter()
        .enumerate()
        .map(|(i, instr)| (op_worst_case_cycles(&instr.op) as u128).saturating_mul(mult_at(i)))
        .fold(0u128, u128::saturating_add);
    let Ok(own_cycles) = u64::try_from(cycles_wide) else {
        return declined(WcetDecline::Loop, hint_rejections);
    };

    // Record every DIRECT call site with the BL's proven execution-count multiplier
    // — a call inside a proven loop is counted `trip` times by the composer, never
    // once (the #1 composition soundness trap, killed by construction).
    let call_sites: Vec<WcetCallSite> = instrs
        .iter()
        .enumerate()
        .filter_map(|(i, instr)| match classify_call(&instr.op) {
            Some(CallClass::Direct(callee_label)) => Some(WcetCallSite {
                callee_label,
                multiplier: mult_at(i),
            }),
            _ => None,
        })
        .collect();

    WcetIntermediate::Composable {
        name: name.to_string(),
        own_cycles,
        instr_count: instrs.len(),
        call_sites,
        loops,
        hint_rejections,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_synthesis::{Condition, Operand2, Reg};

    fn insn(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    #[test]
    fn loop_free_sum_is_exact() {
        let instrs = vec![
            insn(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(1),
            }), // 1
            insn(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }), // 1
            insn(ArmOp::Ldr {
                rd: Reg::R2,
                addr: synth_synthesis::MemAddr {
                    base: Reg::R1,
                    offset: 0,
                    offset_reg: None,
                },
            }), // 2
            insn(ArmOp::Bx { rm: Reg::LR }), // 4
        ];
        match function_wcet("leaf", &instrs, "cortex-m4") {
            WcetFunction::Bounded { cycles, .. } => assert_eq!(cycles, 1 + 1 + 2 + 4),
            other => panic!("expected bounded, got {other:?}"),
        }
    }

    #[test]
    fn backward_branch_declines_loop() {
        // A conditional branch to itself-minus (offset -4 halfwords = backward).
        let instrs = vec![
            insn(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            insn(ArmOp::BCondOffset {
                cond: Condition::NE,
                offset: -4,
            }),
        ];
        assert!(matches!(
            function_wcet("spin", &instrs, "cortex-m4"),
            WcetFunction::Declined {
                reason: WcetDecline::Loop,
                ..
            }
        ));
    }

    #[test]
    fn forward_branch_is_loop_free() {
        // offset -1 is a FORWARD branch (lands at the next halfword) — must NOT
        // be mistaken for a loop.
        let instrs = vec![
            insn(ArmOp::BCondOffset {
                cond: Condition::EQ,
                offset: -1,
            }),
            insn(ArmOp::Bx { rm: Reg::LR }),
        ];
        assert!(matches!(
            function_wcet("fwd", &instrs, "cortex-m4"),
            WcetFunction::Bounded { .. }
        ));
    }

    #[test]
    fn call_declines() {
        let instrs = vec![insn(ArmOp::Bl {
            label: "callee".into(),
        })];
        assert!(matches!(
            function_wcet("caller", &instrs, "cortex-m4"),
            WcetFunction::Declined {
                reason: WcetDecline::Call,
                ..
            }
        ));
    }

    #[test]
    fn looped_i64_div_declines() {
        let instrs = vec![insn(ArmOp::I64DivU {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R2,
            rnhi: Reg::R3,
            rmlo: Reg::R4,
            rmhi: Reg::R5,
            elide_zero_guard: false,
        })];
        assert!(matches!(
            function_wcet("div", &instrs, "cortex-m4"),
            WcetFunction::Declined {
                reason: WcetDecline::LoopedExpansion,
                ..
            }
        ));
    }

    #[test]
    fn m7_declines_unsupported_core() {
        let instrs = vec![insn(ArmOp::Bx { rm: Reg::LR })];
        assert!(matches!(
            function_wcet("f", &instrs, "cortex-m7"),
            WcetFunction::Declined {
                reason: WcetDecline::UnsupportedCore,
                ..
            }
        ));
    }
}
