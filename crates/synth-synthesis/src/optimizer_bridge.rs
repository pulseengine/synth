//! Optimizer Bridge - Integrates optimization passes with instruction selection
//!
//! This module bridges the synthesis engine with the optimization framework,
//! allowing WASM-level and IR-level optimizations before final code generation.
//!
//! ## Multi-Pass Architecture
//!
//! 1. WASM preprocessing: Pattern-match if-else→select, etc.
//! 2. WASM → IR conversion
//! 3. IR optimization passes (constant folding, DCE, etc.)
//! 4. IR → ARM lowering
//! 5. ARM encoding with branch resolution

use crate::Condition;
use crate::instruction_selector::BoundsCheckConfig;
use crate::rules::ArmOp;
use synth_cfg::{Cfg, CfgBuilder};
use synth_core::WasmOp;
use synth_core::{Error, Result};
use synth_opt::{
    AlgebraicSimplification, CommonSubexpressionElimination, ConstantFolding, DeadCodeElimination,
    Instruction, Opcode, OptResult, PassManager, PeepholeOptimization, Reg as OptReg,
};

/// #382: fold a static memory offset that exceeds the 12-bit load/store
/// immediate range into the compile-time-constant linear-memory base.
///
/// The optimized path materializes the linear-memory base as a constant
/// (`MOVW/MOVT R12, #base`), adds the dynamic index (`ADD R12, R12, Raddr`),
/// and then accesses `[R12, #offset]`. When the wasm `offset` is `> 0xFFF` the
/// encoder's `check_ldst_imm12` (#259) correctly REFUSES the imm12 form (it
/// never silently masks to `offset & 0xFFF`), so the function was skipped.
///
/// Because `base` is a compile-time constant and `offset` is too, their sum is
/// also constant: `(base + offset) + addr ≡ base + addr + offset (mod 2^32)`.
/// Folding the offset into the materialized base keeps the access immediate at
/// `#0` with ZERO added instructions and never produces an `ADD R12, R12, #imm`
/// (which would hit the `rd==rn==R12` no-scratch corner — #350).
///
/// Gated to `offset > 0xFFF` so existing small-offset output stays
/// byte-identical (the frozen differential fixtures must not move).
fn fold_mem_offset(base: u32, offset: u32) -> (u32, i32) {
    if offset > 0xFFF {
        (base.wrapping_add(offset), 0)
    } else {
        (base, offset as i32)
    }
}

/// #377/#752: inline software bounds guard for an optimized-path
/// linear-memory access — DELEGATES to the direct selector's
/// [`InstructionSelector::software_bounds_guard`] so both codegen paths share
/// the one wraparound-safe shape (single source, no mirror to drift): trap
/// iff `addr + offset + access_size > R10` in EXACT arithmetic (R10 = memory
/// size in bytes, initialized by startup code). The previous mirror computed
/// the end address with a wrapping 32-bit ADD, so accesses at the top of the
/// address space escaped the trap (#752).
///
/// The traps are inline `UDF`s behind `BCond +0` skips (the #374
/// bulk-memory / div-by-zero pattern), NOT `Bhs Trap_Handler` label branches
/// — the label form resolves to an offset-0 fallthrough no-op in a
/// self-contained image (the second half of #377). Each skip targets
/// `branch_byte + 4`, exactly skipping the 2-byte UDF — the same
/// pre-resolved numeric-guard geometry as the DivS/DivU zero traps, which
/// every downstream pass (`resolved_branch_geometry*`) already maps.
///
/// R12 is free here: it is the encoder scratch (never allocator-assigned), and
/// every access sequence below re-materializes its base into R12 AFTER this
/// guard runs.
fn push_software_bounds_guard(
    arm_instrs: &mut Vec<ArmOp>,
    r_addr: crate::rules::Reg,
    offset: u32,
    access_size: u32,
) {
    arm_instrs.extend(
        crate::instruction_selector::InstructionSelector::software_bounds_guard(
            r_addr,
            offset as i32,
            access_size,
        ),
    );
}

/// The DEFAULT linear-memory base the optimized (absolute) path materializes.
/// #687: no longer the only possible base — `OptimizerBridge::linmem_base`
/// (threaded from `CompileConfig::linmem_base`) overrides it under
/// `--stack-layout=low`, which shifts the whole RAM layout up by the reserved
/// stack size. This constant remains the byte-identical default.
const BASE_CSE_LINMEM_BASE: u32 = synth_core::backend::OPTIMIZED_LINMEM_BASE;
/// VCR-RA lever 3 base register: R11 is OUTSIDE the `reallocate_function` pool
/// (R0–R8), so the range-reallocator identity-preserves it — the hoisted base
/// survives across every straight-line segment untouched, letting us materialize
/// it ONCE at entry rather than per-segment. R11 is also outside local
/// promotion's pool (R4–R8) and is not the encoder scratch (R12). The optimized
/// path's only other uses of R11 — synthetic-local-255 (`Select` nesting) and the
/// `(R10,R11)` i64 pair — are excluded by the planner's disqualification set.
const BASE_CSE_REG: crate::rules::Reg = crate::rules::Reg::R11;

/// VCR-RA lever 3 (#468, epic #242): plan for hoisting the loop-invariant
/// linear-memory base out of a run of constant-address memory accesses.
#[derive(Debug, Default, PartialEq)]
struct BaseCsePlan {
    /// Address vreg → folded immediate (`const_addr + access_offset`, ≤ imm12).
    /// The access is rewritten to `[R11, #imm]`, dropping its per-access
    /// `movw/movt` base + `add`.
    fold: std::collections::HashMap<u32, i32>,
    /// Const vregs whose ONLY use is a folded address — their materialization is
    /// dropped (this is what makes the reserved base a net register-pressure win
    /// rather than a wash).
    skip_const: std::collections::HashSet<u32>,
}

/// Source (read) vregs of an opcode, or `None` if the opcode is outside the
/// base-CSE-safe set — any global/memory-size/select/call/i64/unknown op needs a
/// high register (R9 globals / R10 memsize / R11 select-temp+i64-pair) or a
/// behaviour v1 does not model, so its presence declines base-CSE for the whole
/// function (returns `None` → planner bails → byte-identical per-access path).
/// `_ => None` is the safety backstop: an unenumerated opcode disqualifies rather
/// than risk a missed clobber of the reserved R11 on this un-byte-gated path.
fn base_cse_sources(op: &Opcode) -> Option<Vec<u32>> {
    use Opcode::*;
    let two = |a: &OptReg, b: &OptReg| Some(vec![a.0, b.0]);
    let one = |a: &OptReg| Some(vec![a.0]);
    match op {
        // i32 binops: read src1, src2.
        Add { src1, src2, .. }
        | Sub { src1, src2, .. }
        | Mul { src1, src2, .. }
        | DivS { src1, src2, .. }
        | DivU { src1, src2, .. }
        | RemS { src1, src2, .. }
        | RemU { src1, src2, .. }
        | And { src1, src2, .. }
        | Or { src1, src2, .. }
        | Xor { src1, src2, .. }
        | Shl { src1, src2, .. }
        | ShrS { src1, src2, .. }
        | ShrU { src1, src2, .. }
        | Rotl { src1, src2, .. }
        | Rotr { src1, src2, .. }
        | Eq { src1, src2, .. }
        | Ne { src1, src2, .. }
        | LtS { src1, src2, .. }
        | LtU { src1, src2, .. }
        | LeS { src1, src2, .. }
        | LeU { src1, src2, .. }
        | GtS { src1, src2, .. }
        | GtU { src1, src2, .. }
        | GeS { src1, src2, .. }
        | GeU { src1, src2, .. } => two(src1, src2),
        // i32 unops.
        Clz { src, .. }
        | Ctz { src, .. }
        | Popcnt { src, .. }
        | Extend8S { src, .. }
        | Extend16S { src, .. }
        | Eqz { src, .. }
        | Copy { src, .. }
        | Store { src, .. }
        | TeeStore { src, .. } => one(src),
        // Memory accesses: the address vreg is a read (this is the use that the
        // planner pairs with a const def); stores additionally read `src`.
        MemStore { src, addr, .. } | MemStoreSubword { src, addr, .. } => two(src, addr),
        MemLoad { addr, .. } | MemLoadSubword { addr, .. } => one(addr),
        Return { value } => Some(value.iter().map(|r| r.0).collect()),
        // No register reads. `Label` is allowed: a function body carries a trailing
        // structural end-label even with no real branching, and a label with
        // nothing branching to it does not split control flow. `Branch` /
        // `CondBranch` (below) are what indicate a genuine multi-block function.
        Const { .. } | Load { .. } | Nop | Label { .. } => Some(vec![]),
        // Everything else → disqualify the function. This INCLUDES `Branch` /
        // `CondBranch`: v1 confines base-CSE to functions with no control-flow
        // divergence — #468's straight-line field-initializer target — keeping it
        // clear of the optimized path's (separately-tracked) multi-block lowering.
        // R11 is realloc-immune (out of the R0–R8 pool) so a hoisted base WOULD
        // survive branches; restricting to single-block is the conservative choice.
        // Also covers Select / Global* / MemorySize-Grow / Call / all i64 (high-reg
        // users) and any unenumerated opcode (safety backstop).
        _ => None,
    }
}

/// #543 Phase 2: does a linear-memory access at (wasm-address-space) byte
/// address `addr` intersect any integrator-marked volatile DMA range
/// `[base, base+len)`?
///
/// The access is modelled as the half-open window `[addr, addr+4)` — the widest
/// i32 access. Sub-word accesses (1/2 bytes) are over-approximated to 4, which
/// can only DECLINE more folds (sound conservatism; a fold is an optimization,
/// never a correctness requirement). Arithmetic in i64 so `base+len` at the
/// u32 boundary cannot wrap.
fn intersects_volatile(addr: i64, ranges: &[synth_core::backend::VolatileRange]) -> bool {
    const ACCESS_WIDTH: i64 = 4;
    ranges.iter().any(|r| {
        let base = r.base as i64;
        let end = base + r.len as i64;
        addr < end && addr + ACCESS_WIDTH > base
    })
}

/// Decide whether base-CSE activates for this function and, if so, which const
/// addresses fold. Returns `None` (decline → unchanged per-access codegen) unless
/// ≥2 constant-address accesses fold and every opcode is base-CSE-safe.
///
/// #543 Phase 2 — volatile DMA windows (`--volatile-segment`, threaded through
/// [`OptimizerBridge::set_volatile_segments`]): a const-address access whose
/// window intersects a marked range is EXCLUDED from the fold set — it keeps its
/// per-access materialized address and its verbatim load/store, exactly as if
/// base-CSE had never run for that access. Non-intersecting accesses in the same
/// function still fold (surgical, per-access back-off). Two notes on soundness:
///  - base-CSE never deletes, forwards, or reorders a memory access — every
///    load/store is still issued in program order even when folded — so the
///    exclusion enforces the documented re-materialization contract
///    (`CompileConfig::volatile_segments`), not a value-caching hazard;
///  - DYNAMIC-address accesses are never fold candidates in the first place
///    (only a single-use compile-time-constant address folds), so an access
///    that MIGHT hit a volatile range at runtime is always left verbatim by
///    this pass — the conservative stance for statically-unknown addresses.
fn plan_base_cse(
    instructions: &[Instruction],
    volatile: &[synth_core::backend::VolatileRange],
) -> Option<BaseCsePlan> {
    use std::collections::HashMap;
    let mut const_val: HashMap<u32, i32> = HashMap::new();
    let mut uses: HashMap<u32, u32> = HashMap::new();
    // (addr vreg, static access offset) for every linear-memory access.
    let mut accesses: Vec<(u32, u32)> = Vec::new();
    for inst in instructions {
        match &inst.opcode {
            Opcode::Const { dest, value } => {
                const_val.insert(dest.0, *value);
            }
            Opcode::MemStore { addr, offset, .. }
            | Opcode::MemLoad { addr, offset, .. }
            | Opcode::MemStoreSubword { addr, offset, .. }
            | Opcode::MemLoadSubword { addr, offset, .. } => {
                accesses.push((addr.0, *offset));
            }
            _ => {}
        }
        // A single unenumerated/disqualifying opcode declines the whole function.
        let srcs = base_cse_sources(&inst.opcode)?;
        for v in srcs {
            *uses.entry(v).or_insert(0) += 1;
        }
    }
    let mut plan = BaseCsePlan::default();
    for (addr_vreg, off) in accesses {
        // Foldable iff the address is a compile-time constant whose ONLY use is
        // this access, and base+addr+offset stays in the imm12 window so the
        // access immediate `[R11, #imm]` encodes directly.
        if let Some(&aval) = const_val.get(&addr_vreg)
            && uses.get(&addr_vreg) == Some(&1)
        {
            let folded = (aval as i64) + (off as i64);
            // #543 Phase 2: an access inside a marked volatile DMA window is
            // NOT folded — it keeps its verbatim per-access codegen.
            if (0..=0xFFF).contains(&folded) && !intersects_volatile(folded, volatile) {
                plan.fold.insert(addr_vreg, folded as i32);
                plan.skip_const.insert(addr_vreg);
            }
        }
    }
    (plan.fold.len() >= 2).then_some(plan)
}

/// Optimization configuration
#[derive(Debug, Clone)]
pub struct OptimizationConfig {
    /// Enable constant folding
    pub enable_constant_folding: bool,
    /// Enable CSE
    pub enable_cse: bool,
    /// Enable algebraic simplification
    pub enable_algebraic: bool,
    /// Enable peephole optimization
    pub enable_peephole: bool,
    /// Enable dead code elimination
    pub enable_dce: bool,
    /// Maximum optimization iterations
    pub max_iterations: usize,
    /// Verbose output
    pub verbose: bool,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            enable_constant_folding: true,
            enable_cse: true,
            enable_algebraic: true,
            enable_peephole: true,
            enable_dce: true,
            max_iterations: 10,
            verbose: false,
        }
    }
}

impl OptimizationConfig {
    /// Create config with all optimizations enabled
    pub fn all() -> Self {
        Self::default()
    }

    /// Create config with all optimizations disabled
    pub fn none() -> Self {
        Self {
            enable_constant_folding: false,
            enable_cse: false,
            enable_algebraic: false,
            enable_peephole: false,
            enable_dce: false,
            max_iterations: 0,
            verbose: false,
        }
    }

    /// Create config with only fast optimizations
    pub fn fast() -> Self {
        Self {
            enable_constant_folding: true,
            enable_algebraic: true,
            enable_peephole: true,
            enable_cse: false,
            enable_dce: false,
            max_iterations: 3,
            verbose: false,
        }
    }

    /// Create config compatible with Loom preprocessing
    ///
    /// When Loom is used as a WASM-level optimizer before Synth,
    /// disable passes that Loom already handles to avoid redundant work:
    /// - Constant folding (Loom does this)
    /// - Strength reduction (via algebraic, Loom does this)
    ///
    /// Keep passes that operate at IR level and complement Loom:
    /// - CSE (at register IR level)
    /// - DCE (at register IR level)
    /// - Peephole (ARM-specific patterns)
    pub fn loom_compat() -> Self {
        Self {
            enable_constant_folding: false, // Loom handles this
            enable_algebraic: false,        // Loom handles strength reduction
            enable_peephole: true,          // ARM-specific, Loom doesn't do this
            enable_cse: true,               // IR-level, complements Loom
            enable_dce: true,               // IR-level, complements Loom
            max_iterations: 5,
            verbose: false,
        }
    }
}

/// Optimization statistics
#[derive(Debug, Clone, Default)]
pub struct OptimizationStats {
    /// Number of instructions removed
    pub removed: usize,
    /// Number of instructions modified
    pub modified: usize,
    /// Number of instructions added
    pub added: usize,
    /// Number of optimization passes run
    pub passes_run: usize,
}

/// Optimizer bridge that integrates with synthesis pipeline
/// Estimate the encoded byte size of a single optimized-path ARM instruction.
///
/// This MUST mirror the Thumb-2 encoder (`synth_backend::ArmEncoder::encode`)
/// for every `ArmOp` the optimized path emits, because `ir_to_arm`'s
/// branch-resolution pass sums these sizes to compute branch displacements: an
/// under-estimate lands a forward branch short (the #483-class miscompile), an
/// over-estimate lands it long. It is a *hand-maintained mirror* of the encoder
/// only because synth-synthesis cannot depend on synth-backend (the encoder
/// lives downstream), so the two cannot share one source of truth — the
/// structural cause behind #498. The `estimator_encoder_agreement` oracle in
/// synth-backend (which *can* see both) pins this mirror against the real
/// encoder and documents every remaining divergence as a known gap.
///
/// Extracted verbatim from the inline `instr_byte_size` closure (#498, #242) so
/// the agreement oracle can call it; the body is logic-identical to the
/// pre-extraction closure.
pub fn estimate_arm_byte_size(op: &ArmOp) -> usize {
    use crate::rules::{Operand2, Reg};
    // Helper to get register number
    let reg_num = |r: &Reg| -> u8 {
        match r {
            Reg::R0 => 0,
            Reg::R1 => 1,
            Reg::R2 => 2,
            Reg::R3 => 3,
            Reg::R4 => 4,
            Reg::R5 => 5,
            Reg::R6 => 6,
            Reg::R7 => 7,
            Reg::R8 => 8,
            Reg::R9 => 9,
            Reg::R10 => 10,
            Reg::R11 => 11,
            Reg::R12 => 12,
            Reg::SP => 13,
            Reg::LR => 14,
            Reg::PC => 15,
        }
    };

    match op {
        // SetCond: ITE + MOV #1 + MOV #0 = 2 + 2 + 2 = 6 bytes
        ArmOp::SetCond { .. } => 6,
        // SelectMove: IT + MOV = 2 + 2 = 4 bytes
        ArmOp::SelectMove { .. } => 4,
        // 32-bit Thumb-2 instructions (always 4 bytes)
        ArmOp::Movw { .. } | ArmOp::Movt { .. } => 4,
        // Register shifts and RSB are always 32-bit Thumb-2
        ArmOp::LslReg { .. }
        | ArmOp::LsrReg { .. }
        | ArmOp::AsrReg { .. }
        | ArmOp::RorReg { .. }
        | ArmOp::Rsb { .. } => 4,
        // MUL, MLS, SDIV, UDIV are always 32-bit Thumb-2
        ArmOp::Mul { .. } | ArmOp::Mls { .. } | ArmOp::Sdiv { .. } | ArmOp::Udiv { .. } => 4,
        // ADC, SBC are always 32-bit Thumb-2
        ArmOp::Adc { .. } | ArmOp::Sbc { .. } => 4,
        // CLZ, RBIT are always 32-bit Thumb-2
        ArmOp::Clz { .. } | ArmOp::Rbit { .. } => 4,
        // Popcnt: the encoder expands it to a fixed bit-twiddle sequence using
        // r11/r12 scratch (arm_encoder.rs). 84 bytes for the body, +2 for the
        // leading 16-bit `MOV rd, rm` when rd != rm. #498: previously absent
        // from the estimator (fell to `_ => 2`), an 82/84-byte under-estimate.
        ArmOp::Popcnt { rd, rm } => {
            if reg_num(rd) != reg_num(rm) {
                86
            } else {
                84
            }
        }
        // ADDS/SUBS with a register operand: 16-bit only when rd, rn, rm are all
        // R0-R7 (flag-setting T1 form); any high register forces the 32-bit
        // ADDS.W/SUBS.W (#178/#180). The immediate form is always 32-bit.
        // #498: previously fell to `_ => 2`, under-estimating the high-reg form.
        ArmOp::Adds {
            rd,
            rn,
            op2: Operand2::Reg(rm),
        }
        | ArmOp::Subs {
            rd,
            rn,
            op2: Operand2::Reg(rm),
        } => {
            if reg_num(rd) < 8 && reg_num(rn) < 8 && reg_num(rm) < 8 {
                2
            } else {
                4
            }
        }
        ArmOp::Adds { .. } | ArmOp::Subs { .. } => 4,
        // CMN with a register operand: 16-bit T1 only for R0-R7; high registers
        // (CMN has no 16-bit high-reg form, #184) force CMN.W (32-bit). The
        // immediate form is always 32-bit (CMN.W). #498: previously `_ => 2`.
        ArmOp::Cmn {
            rn,
            op2: Operand2::Reg(rm),
        } => {
            if reg_num(rn) < 8 && reg_num(rm) < 8 {
                2
            } else {
                4
            }
        }
        ArmOp::Cmn { .. } => 4,
        // SXTB, SXTH, UXTB, UXTH can be 16-bit for low registers
        ArmOp::Sxtb { rd, rm }
        | ArmOp::Sxth { rd, rm }
        | ArmOp::Uxtb { rd, rm }
        | ArmOp::Uxth { rd, rm } => {
            let rd_bits = reg_num(rd);
            let rm_bits = reg_num(rm);
            if rd_bits < 8 && rm_bits < 8 { 2 } else { 4 }
        }
        // I64SetCond: multi-instruction sequence (12 bytes for all conditions)
        // EQ/NE: CMP(2) + IT EQ(2) + CMP(2) + ITE(2) + MOV(2) + MOV(2)
        // LT/GT: CMP(2) + SBCS(4) + ITE(2) + MOV(2) + MOV(2)
        ArmOp::I64SetCond { .. } => 12,
        // I64SetCondZ: ORR.W(4) + CMP(2) + ITE(2) + MOV(2) + MOV(2)
        ArmOp::I64SetCondZ { .. } => 12,
        // I64Mul: MUL(4) + MLA(4) + UMULL(4) + ADD(2) = 14 bytes
        ArmOp::I64Mul { .. } => 14,
        // I64Shl/ShrU: AND.W(4) + SUBS.W(4) + BPL(2) + small_block(22) + B(2) + large_block(6) - but byte_size = total = 38
        ArmOp::I64Shl { .. } | ArmOp::I64ShrU { .. } => 38,
        // I64ShrS: same as ShrU but large block is 8 bytes (ASR+ASR vs LSR+MOV) = 40
        ArmOp::I64ShrS { .. } => 40,
        // I64Rotl/Rotr (#610): fixed-ABI wrapper (PUSH r0-r3(2) + 3×STR(12) +
        // 3×POP(6) + 2×MOV(4) + 4×restore(8) = 32) + core (AND(4) + SUBS(4) +
        // BPL(2) + small(30) + B(2) + large(30) = 70) = 102 bytes.
        ArmOp::I64Rotl { .. } | ArmOp::I64Rotr { .. } => 102,
        // I64Clz: CMP.W(4) + BEQ(2) + CLZ.W(4) + B(2) + NOP(2) + CLZ.W(4) + ADD.W(4) + MOV(2) = 24 bytes
        ArmOp::I64Clz { .. } => 24,
        // I64Ctz: CMP.W(4) + BEQ(2) + RBIT.W(4) + CLZ.W(4) + B(2) + NOP(2) + RBIT.W(4) + CLZ.W(4) + ADD.W(4) + MOV(2) = 32 bytes
        ArmOp::I64Ctz { .. } => 32,
        // I64Popcnt: PUSH/POP + duplicate popcount for lo and hi word (#498:
        // measured 172; #632 result-carry through R12 across the restore pop
        // + R12-routed marshal + MOV.W hi-clear = +8).
        ArmOp::I64Popcnt { .. } => 180,
        // I64 sign extension: SXTB/SXTH/ASR + ASR.
        ArmOp::I64Extend8S { .. } => 8,
        ArmOp::I64Extend16S { .. } => 8,
        // I64Extend32S: MOV (lo passthrough) + ASR (sign-fill hi) = 6 bytes
        // (#498: measured 6, was an 8-byte over-estimate).
        ArmOp::I64Extend32S { .. } => 6,
        // I64 division: #610 fixed-ABI wrapper (PUSH r0-r3(2) + 4×STR(16) +
        // 4×POP(8) + zero-trap(8) + 2×MOV(4) + 4×restore(8) = 46) around the
        // pre-#610 cores (74/78/126/124, the #498 exact measurements).
        // #494 phase 2b: a certificate-discharged divisor-nonzero fact elides
        // the fused zero-trap (ORRS.W + BNE + UDF = 8 bytes); div_s's #633
        // overflow guard (22 bytes) is a SEPARATE obligation. Sizes must track
        // the flags or the estimator↔encoder agreement oracle (#511) drifts.
        ArmOp::I64DivU {
            elide_zero_guard, ..
        } => 120 - if *elide_zero_guard { 8 } else { 0 },
        ArmOp::I64RemU {
            elide_zero_guard, ..
        } => 124 - if *elide_zero_guard { 8 } else { 0 },
        // Signed versions have additional negation logic. div_s also carries
        // the #633 INT64_MIN/-1 overflow guard (+22 bytes); rem_s deliberately
        // does NOT (rem_s(INT64_MIN, -1) == 0, no trap).
        ArmOp::I64DivS {
            elide_zero_guard,
            elide_overflow_guard,
            ..
        } => {
            194 - if *elide_zero_guard { 8 } else { 0 } - if *elide_overflow_guard { 22 } else { 0 }
        }
        ArmOp::I64RemS {
            elide_zero_guard, ..
        } => 170 - if *elide_zero_guard { 8 } else { 0 },
        // AND/OR/XOR: encoder always uses 32-bit Thumb-2 (.W) encoding
        ArmOp::And { .. } | ArmOp::Orr { .. } | ArmOp::Eor { .. } => 4,
        // LDR/STR with high base register or large offset need 32-bit
        ArmOp::Ldr { rd, addr } => {
            let rd_bits = reg_num(rd);
            let base_bits = reg_num(&addr.base);
            let offset = addr.offset as u32;
            if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 {
                2
            } else {
                4
            }
        }
        ArmOp::Str { rd, addr } => {
            let rd_bits = reg_num(rd);
            let base_bits = reg_num(&addr.base);
            let offset = addr.offset as u32;
            if rd_bits < 8 && base_bits < 8 && (offset & 0x3) == 0 && offset <= 124 {
                2
            } else {
                4
            }
        }
        // #483: half/byte loads and stores. The optimized path always
        // materializes a memory access against a HIGH base register
        // (`ip`/r12 for a const address, r11 for the base-CSE linmem
        // anchor), so the encoder always emits the 32-bit `.w` form — the
        // 16-bit Thumb T1 encoding (low base + small aligned offset) is
        // never produced here. Sizing these as the default 2 (the bug)
        // drifts `byte_offsets` and miscompiles any branch that spans the
        // access (the i32.store16 in the #483 `block`/`br_if` repro).
        ArmOp::Strh { .. }
        | ArmOp::Strb { .. }
        | ArmOp::Ldrh { .. }
        | ArmOp::Ldrsh { .. }
        | ArmOp::Ldrb { .. }
        | ArmOp::Ldrsb { .. } => 4,
        // BL is always 32-bit
        ArmOp::Bl { .. } => 4,
        // Branches: 2-byte short forms when the halfword displacement fits
        // (B.N imm11 / B<cond>.N imm8), 4-byte `.w` otherwise — mirrors the
        // encoder's range test exactly (#498). In production `ir_to_arm` sizes
        // these on the offset-0 PLACEHOLDER (pre-resolution) and its resolution
        // pass declines any displacement that outgrows the short form, so the
        // 2-byte estimate is the only one that ever feeds `byte_offsets`; the
        // far arms keep the estimator a faithful per-op encoder mirror for the
        // post-resolution consumers (`resolved_branch_geometry`) and the
        // agreement oracle.
        ArmOp::BOffset { offset } => {
            if (-1024..=1022).contains(offset) {
                2
            } else {
                4
            }
        }
        ArmOp::BCondOffset { offset, .. } => {
            if (-128..=127).contains(offset) {
                2
            } else {
                4
            }
        }
        // MOV immediate, mirroring the encoder's three-way split (#498):
        //   - 0..=255 into a low register: 2-byte MOVS
        //   - 16-bit range (or a high rd): 4-byte MOVW
        //   - negative / above 0xFFFF: 8-byte MOVW+MOVT pair (the encoder's
        //     old signed `imm <= 255` test emitted a wrong-value 2-byte
        //     MOVS #(imm&0xFF) here — fixed encoder-side alongside this arm;
        //     no emitter produces this shape today, both paths materialize
        //     wide constants as explicit Movw/Movt or Movw+Mvn upstream)
        ArmOp::Mov {
            rd,
            op2: Operand2::Imm(v),
        } => {
            if (*v as u32) > 0xFFFF {
                8
            } else if reg_num(rd) > 7 || *v > 255 {
                4
            } else {
                2
            }
        }
        ArmOp::Mov { .. } => 2,
        // SUB/ADD with high registers need 32-bit encoding
        ArmOp::Sub {
            rd,
            rn,
            op2: Operand2::Reg(rm),
        } if reg_num(rd) > 7 || reg_num(rn) > 7 || reg_num(rm) > 7 => 4,
        ArmOp::Add {
            rd,
            rn,
            op2: Operand2::Reg(rm),
        } if reg_num(rd) > 7 || reg_num(rn) > 7 || reg_num(rm) > 7 => 4,
        // #377: ADD rd, rn, #imm with a HIGH rd — always the 32-bit ADD.W form
        // (the encoder's 16-bit `ADDS #imm3` requires rd AND rn low AND
        // imm <= 7). The software bounds guard's end-address compute
        // (`ADD R12, Raddr, #off+size-1`) is this shape; without this arm it
        // fell to the `_ => 2` default and drifted every spanning branch by 2
        // bytes. Scoped to high-rd so pre-existing low-reg imm-ADD sizing is
        // untouched (the low-reg imm > 7 form remains a known gap of the
        // `_ => 2` default — no optimized-path site emits it).
        ArmOp::Add {
            rd,
            op2: Operand2::Imm(_),
            ..
        } if reg_num(rd) > 7 => 4,
        // Most 16-bit Thumb instructions (MOV low, CMP low, B, etc.)
        _ => 2,
    }
}

pub struct OptimizerBridge {
    config: OptimizationConfig,
    /// Number of imported functions (wasm function indices `< num_imports` are
    /// imports). Used to distinguish import calls (handled in the optimized
    /// path, dispatched via `func_N` → field-name rewrite, #173) from local
    /// calls (declined so the direct selector can preserve caller-saved regs
    /// across them, #188). Defaults to 0.
    num_imports: u32,
    /// VCR-RA-001 (#242, #496): allocation-time spill-on-exhaustion override
    /// for tests. `None` (default) reads the `SYNTH_SPILL_ON_EXHAUST` env flag;
    /// `Some(_)` forces the lever on/off regardless of the environment (unit
    /// tests must not race on process-global env vars).
    spill_on_exhaust: Option<bool>,
    /// #543 Phase 2: integrator-marked volatile linear-memory segments (the DMA
    /// transfer window), threaded from `CompileConfig::volatile_segments`. The
    /// address-caching levers consume it: base-CSE (#468) excludes any access
    /// whose window intersects a marked range from its fold set (see
    /// [`plan_base_cse`]), and const-CSE declines wholesale while any range is
    /// marked (a constant cannot be classified address-vs-data at that level —
    /// conservative v1). Empty (the default) ⇒ byte-identical behavior.
    volatile_segments: Vec<synth_core::backend::VolatileRange>,
    /// #377: the `--safety-bounds` mode, threaded from the backend. Pre-fix the
    /// optimized path ignored it entirely — `software`/`mask` were silent
    /// no-ops on the path that lowers the bulk of a flight loop's i32
    /// loads/stores. `Software` now emits an inline guard before every
    /// `MemLoad`/`MemStore`/`MemLoadSubword`/`MemStoreSubword`; `Masking`
    /// declines the function to the direct selector (which implements it);
    /// `None`/`Mpu` emit no inline guard (byte-identical to before).
    bounds_check: BoundsCheckConfig,
    /// #687 (`--stack-layout=low`): the absolute linear-memory base this
    /// path materializes (per-access `MOVW/MOVT R12` and the #468 base-CSE
    /// R11 hoist). Defaults to [`BASE_CSE_LINMEM_BASE`] (byte-identical);
    /// the CLI shifts it up by the reserved stack size under the low layout
    /// so const-address accesses follow the moved linear memory.
    linmem_base: u32,
    /// VCR-VER-001 (#242): whether the LAST `ir_to_arm` call's output was
    /// actually shaped by the spill-on-exhaustion machinery (a pre-step
    /// reinstate/evict fired, or a constant-divisor guard was elided). The
    /// backend scopes the post-exhaustion cleanup extensions to exactly these
    /// functions, so a flag-on compile leaves every untouched function
    /// byte-identical (the `vcr_ver_001_gate_242` lock's contract).
    spill_on_exhaust_fired: std::cell::Cell<bool>,
}

impl OptimizerBridge {
    /// Create a new optimizer bridge with default configuration
    pub fn new() -> Self {
        Self {
            config: OptimizationConfig::default(),
            num_imports: 0,
            spill_on_exhaust: None,
            volatile_segments: Vec::new(),
            bounds_check: BoundsCheckConfig::None,
            linmem_base: BASE_CSE_LINMEM_BASE,
            spill_on_exhaust_fired: std::cell::Cell::new(false),
        }
    }

    /// Create with custom configuration
    pub fn with_config(config: OptimizationConfig) -> Self {
        Self {
            config,
            num_imports: 0,
            spill_on_exhaust: None,
            volatile_segments: Vec::new(),
            bounds_check: BoundsCheckConfig::None,
            linmem_base: BASE_CSE_LINMEM_BASE,
            spill_on_exhaust_fired: std::cell::Cell::new(false),
        }
    }

    /// VCR-VER-001 (#242): did the last [`OptimizerBridge::ir_to_arm`] output
    /// get shaped by the spill-on-exhaustion machinery? See the field doc.
    pub fn spill_on_exhaust_fired(&self) -> bool {
        self.spill_on_exhaust_fired.get()
    }

    /// #377: set the `--safety-bounds` mode (see [`OptimizerBridge::bounds_check`]).
    pub fn set_bounds_check(&mut self, bounds_check: BoundsCheckConfig) {
        self.bounds_check = bounds_check;
    }

    /// #687: set the absolute linear-memory base the optimized path
    /// materializes (see [`OptimizerBridge::linmem_base`]).
    pub fn set_linmem_base(&mut self, base: u32) {
        self.linmem_base = base;
    }

    /// Set the number of imported functions (see [`OptimizerBridge::num_imports`]).
    pub fn set_num_imports(&mut self, num_imports: u32) {
        self.num_imports = num_imports;
    }

    /// #543 Phase 2: thread the integrator-marked volatile DMA-window ranges
    /// (`CompileConfig::volatile_segments`) to the address-caching levers — see
    /// [`OptimizerBridge::volatile_segments`] for what consumes them.
    pub fn set_volatile_segments(&mut self, ranges: Vec<synth_core::backend::VolatileRange>) {
        self.volatile_segments = ranges;
    }

    /// Force the allocation-time spill-on-exhaustion lever on/off (tests only —
    /// production callers use the `SYNTH_SPILL_ON_EXHAUST` env flag).
    pub fn set_spill_on_exhaust(&mut self, on: bool) {
        self.spill_on_exhaust = Some(on);
    }

    /// Whether allocation-time spill-on-exhaustion is requested (#242, #496).
    /// Default off: without the flag, pool exhaustion keeps declining the
    /// function to the direct selector — byte-identical behaviour.
    fn spill_on_exhaust_enabled(&self) -> bool {
        self.spill_on_exhaust
            .unwrap_or_else(|| std::env::var("SYNTH_SPILL_ON_EXHAUST").is_ok())
    }

    /// Preprocess WASM ops to transform patterns before IR conversion
    ///
    /// This pass converts control flow patterns to select instructions,
    /// which can be lowered to branchless ARM code (conditional moves).
    ///
    /// ## Pattern 1: Simple if-else
    /// ```text
    /// condition           ; value on stack
    /// If                  ; start if
    ///   value1            ; then-block pushes one value
    /// Else
    ///   value2            ; else-block pushes one value
    /// End
    /// ```
    /// Becomes:
    /// ```text
    /// value1              ; true value (pushed first)
    /// value2              ; false value (pushed second)
    /// condition           ; condition (on top)
    /// Select              ; pick one
    /// ```
    ///
    /// ## Pattern 2: Nested if-else
    /// ```text
    /// outer_cond
    /// If
    ///   inner_cond
    ///   If
    ///     val1
    ///   Else
    ///     val2
    ///   End
    /// Else
    ///   val3
    /// End
    /// ```
    /// Becomes:
    /// ```text
    /// val1, val2, inner_cond, Select   ; inner select
    /// val3                              ; else value
    /// outer_cond                        ; outer condition
    /// Select                            ; outer select
    /// ```
    ///
    /// ## Pattern 3: br_if at block end with simple value
    /// ```text
    /// Block
    ///   val1
    ///   cond
    ///   BrIf(0)     ; if cond, return val1
    ///   Drop
    ///   val2        ; else return val2
    /// End
    /// ```
    /// Becomes:
    /// ```text
    /// val1              ; true value
    /// val2              ; false value
    /// cond              ; condition
    /// Select            ; pick one
    /// ```
    fn preprocess_wasm_ops(&self, wasm_ops: &[WasmOp]) -> Vec<WasmOp> {
        let mut result = Vec::new();
        let mut i = 0;

        while i < wasm_ops.len() {
            // Pattern 3: Block with br_if early exit
            // Block, val1, cond, BrIf(0), Drop, val2, End
            if i + 6 < wasm_ops.len()
                && matches!(wasm_ops[i], WasmOp::Block)
                && Self::is_simple_value(&wasm_ops[i + 1])
                && Self::is_condition_producer(&wasm_ops[i + 2])
                && matches!(wasm_ops[i + 3], WasmOp::BrIf(0))
                && matches!(wasm_ops[i + 4], WasmOp::Drop)
                && Self::is_simple_value(&wasm_ops[i + 5])
                && matches!(wasm_ops[i + 6], WasmOp::End)
            {
                // br_if pattern: select(val1, val2, cond)
                let val1 = wasm_ops[i + 1].clone();
                let cond = wasm_ops[i + 2].clone();
                let val2 = wasm_ops[i + 5].clone();

                // Emit: val1, val2, cond, select
                result.push(val1);
                result.push(val2);
                result.push(cond);
                result.push(WasmOp::Select);

                i += 7;
                continue;
            }

            // Pattern 2: Nested if-else → nested select
            // [outer_cond already in result], If, inner_cond, If, val1, Else, val2, End, Else, val3, End
            // Pattern: i=If, i+1=inner_cond, i+2=If, i+3=val1, i+4=Else, i+5=val2, i+6=End, i+7=Else, i+8=val3, i+9=End
            //
            // IMPORTANT: The outer condition (e.g., LocalGet 0 = R0) must be evaluated BEFORE
            // the inner select runs, because the inner select writes its result to R0.
            // We save the outer condition to a synthetic local (index 255) to preserve it.
            if i + 9 < wasm_ops.len()
                && matches!(wasm_ops[i], WasmOp::If)
                && Self::is_condition_producer(&wasm_ops[i + 1])
                && matches!(wasm_ops[i + 2], WasmOp::If)
                && Self::is_simple_value(&wasm_ops[i + 3])
                && matches!(wasm_ops[i + 4], WasmOp::Else)
                && Self::is_simple_value(&wasm_ops[i + 5])
                && matches!(wasm_ops[i + 6], WasmOp::End)
                && matches!(wasm_ops[i + 7], WasmOp::Else)
                && Self::is_simple_value(&wasm_ops[i + 8])
                && matches!(wasm_ops[i + 9], WasmOp::End)
            {
                // Pop outer condition (e.g., LocalGet 0)
                let outer_cond = if !result.is_empty() {
                    result.pop()
                } else {
                    None
                };

                let inner_cond = wasm_ops[i + 1].clone();
                let val1 = wasm_ops[i + 3].clone();
                let val2 = wasm_ops[i + 5].clone();
                let val3 = wasm_ops[i + 8].clone();

                // Save outer condition to synthetic local 255 BEFORE inner select
                // This preserves the outer condition value before R0 gets overwritten
                if let Some(ref cond) = outer_cond {
                    result.push(cond.clone());
                    result.push(WasmOp::LocalSet(255)); // Save to synthetic local
                }

                // Emit inner select: val1, val2, inner_cond, select
                result.push(val1);
                result.push(val2);
                result.push(inner_cond);
                result.push(WasmOp::Select);

                // Emit outer select: [inner_result on stack], val3, outer_cond, select
                result.push(val3);
                if outer_cond.is_some() {
                    // Load the saved outer condition from synthetic local
                    result.push(WasmOp::LocalGet(255));
                } else {
                    result.push(WasmOp::I32Const(0));
                }
                result.push(WasmOp::Select);

                i += 10;
                continue;
            }

            // Pattern 1: Simple if-else → select
            // [condition], If, [then_value], Else, [else_value], End
            if i + 4 < wasm_ops.len()
                && matches!(wasm_ops[i], WasmOp::If)
                && Self::is_simple_value(&wasm_ops[i + 1])
                && matches!(wasm_ops[i + 2], WasmOp::Else)
                && Self::is_simple_value(&wasm_ops[i + 3])
                && matches!(wasm_ops[i + 4], WasmOp::End)
            {
                // Pop the condition (last thing added before If)
                let condition = if !result.is_empty() {
                    result.pop()
                } else {
                    None
                };

                // Extract the then and else values
                let then_value = wasm_ops[i + 1].clone();
                let else_value = wasm_ops[i + 3].clone();

                // Emit: then_value, else_value, condition, select
                result.push(then_value);
                result.push(else_value);
                if let Some(cond) = condition {
                    result.push(cond);
                } else {
                    // No condition found, use a placeholder
                    result.push(WasmOp::I32Const(0));
                }
                result.push(WasmOp::Select);

                // Skip the matched pattern
                i += 5;
            } else {
                // No pattern match, just copy the op
                result.push(wasm_ops[i].clone());
                i += 1;
            }
        }

        result
    }

    /// Check if a WASM op produces a simple value (suitable for if-else→select transform)
    fn is_simple_value(op: &WasmOp) -> bool {
        matches!(
            op,
            WasmOp::I32Const(_) | WasmOp::LocalGet(_) | WasmOp::GlobalGet(_)
        )
    }

    /// Check if a WASM op is a condition producer (comparison, local.get, etc.)
    /// Used to identify conditions in nested if-else patterns
    fn is_condition_producer(op: &WasmOp) -> bool {
        matches!(
            op,
            WasmOp::I32Const(_)
                | WasmOp::LocalGet(_)
                | WasmOp::GlobalGet(_)
                | WasmOp::I32Eqz
                | WasmOp::I32Eq
                | WasmOp::I32Ne
                | WasmOp::I32LtS
                | WasmOp::I32LtU
                | WasmOp::I32LeS
                | WasmOp::I32LeU
                | WasmOp::I32GtS
                | WasmOp::I32GtU
                | WasmOp::I32GeS
                | WasmOp::I32GeU
        )
    }

    /// Returns true if `op` is a scalar f32/f64 operation that the optimized
    /// lowering path (`wasm_to_ir` → `ir_to_arm`) cannot handle.
    ///
    /// Issue #120: `wasm_to_ir` has zero handlers for f32/f64 ops, so every
    /// float op falls through the catch-all `_ => Opcode::Nop`. A value-producing
    /// float op that emits `Nop` produces no vreg; any downstream consumer then
    /// references an unmapped vreg and trips the defensive `get_arm_reg` panic
    /// added by PR #101 (the #93 silent-drop class, for floats).
    ///
    /// The IR `Opcode` enum (`synth-opt`) has no float opcodes at all, so the
    /// optimized path cannot lower floats without a large feature addition.
    /// Instead, `optimize_full` detects these ops up front and returns a typed
    /// `Err`, letting the backend fall back to the non-optimized
    /// `InstructionSelector::select_with_stack` path, which *does* handle f32
    /// (VFP/FPU). This includes float→int / int→float conversion ops and float
    /// loads/stores, since they too produce or consume float-typed values the
    /// optimized path can neither map to a vreg nor lower to VFP.
    fn is_unsupported_float_op(op: &WasmOp) -> bool {
        matches!(
            op,
            // f32 arithmetic
            WasmOp::F32Add
                | WasmOp::F32Sub
                | WasmOp::F32Mul
                | WasmOp::F32Div
                // f32 comparisons
                | WasmOp::F32Eq
                | WasmOp::F32Ne
                | WasmOp::F32Lt
                | WasmOp::F32Le
                | WasmOp::F32Gt
                | WasmOp::F32Ge
                // f32 math functions
                | WasmOp::F32Abs
                | WasmOp::F32Neg
                | WasmOp::F32Ceil
                | WasmOp::F32Floor
                | WasmOp::F32Trunc
                | WasmOp::F32Nearest
                | WasmOp::F32Sqrt
                | WasmOp::F32Min
                | WasmOp::F32Max
                | WasmOp::F32Copysign
                // f32 constants and memory
                | WasmOp::F32Const(_)
                | WasmOp::F32Load { .. }
                | WasmOp::F32Store { .. }
                // f32 conversions
                | WasmOp::F32ConvertI32S
                | WasmOp::F32ConvertI32U
                | WasmOp::F32ConvertI64S
                | WasmOp::F32ConvertI64U
                | WasmOp::F32DemoteF64
                | WasmOp::F32ReinterpretI32
                | WasmOp::I32ReinterpretF32
                | WasmOp::I32TruncF32S
                | WasmOp::I32TruncF32U
                // f64 arithmetic
                | WasmOp::F64Add
                | WasmOp::F64Sub
                | WasmOp::F64Mul
                | WasmOp::F64Div
                // f64 comparisons
                | WasmOp::F64Eq
                | WasmOp::F64Ne
                | WasmOp::F64Lt
                | WasmOp::F64Le
                | WasmOp::F64Gt
                | WasmOp::F64Ge
                // f64 math functions
                | WasmOp::F64Abs
                | WasmOp::F64Neg
                | WasmOp::F64Ceil
                | WasmOp::F64Floor
                | WasmOp::F64Trunc
                | WasmOp::F64Nearest
                | WasmOp::F64Sqrt
                | WasmOp::F64Min
                | WasmOp::F64Max
                | WasmOp::F64Copysign
                // f64 constants and memory
                | WasmOp::F64Const(_)
                | WasmOp::F64Load { .. }
                | WasmOp::F64Store { .. }
                // f64 conversions
                | WasmOp::F64ConvertI32S
                | WasmOp::F64ConvertI32U
                | WasmOp::F64ConvertI64S
                | WasmOp::F64ConvertI64U
                | WasmOp::F64PromoteF32
                | WasmOp::F64ReinterpretI64
                | WasmOp::I64ReinterpretF64
                | WasmOp::I64TruncF64S
                | WasmOp::I64TruncF64U
                | WasmOp::I32TruncF64S
                | WasmOp::I32TruncF64U
        )
    }

    /// Returns how many i64 values a WASM op consumes (0 if not an i64-consuming op)
    fn i64_operand_count(op: &WasmOp) -> usize {
        match op {
            // Binary ops consuming 2 i64 values
            WasmOp::I64Add | WasmOp::I64Sub | WasmOp::I64And | WasmOp::I64Or
            | WasmOp::I64Xor | WasmOp::I64Mul | WasmOp::I64Shl | WasmOp::I64ShrS
            | WasmOp::I64ShrU | WasmOp::I64Rotl | WasmOp::I64Rotr
            // Division / remainder (previously omitted from this list,
            // which made `analyze_i64_local_gets` miss the i64 LocalGets
            // feeding into `i64.div_*`/`i64.rem_*` — they were then
            // emitted as 1-slot i32 Loads and the binary handler
            // underflowed `inst_id.saturating_sub(4)`. The slot_stack
            // refactor (issue #121) made this manifest as a pop-of-empty
            // panic instead of a silent miscompilation.)
            | WasmOp::I64DivS | WasmOp::I64DivU | WasmOp::I64RemS | WasmOp::I64RemU
            // Comparisons also consume 2 i64 values (but produce i32)
            | WasmOp::I64Eq | WasmOp::I64Ne | WasmOp::I64LtS | WasmOp::I64LtU
            | WasmOp::I64GtS | WasmOp::I64GtU | WasmOp::I64LeS | WasmOp::I64LeU
            | WasmOp::I64GeS | WasmOp::I64GeU => 2,
            // Unary ops consuming 1 i64 value
            WasmOp::I64Eqz | WasmOp::I64Clz | WasmOp::I64Ctz | WasmOp::I64Popcnt => 1,
            _ => 0,
        }
    }

    /// Analyze WASM ops to determine which LocalGet operations load i64 values.
    /// Returns a set of indices where LocalGet should be treated as i64.
    fn analyze_i64_local_gets(wasm_ops: &[WasmOp]) -> std::collections::HashSet<usize> {
        use std::collections::HashSet;
        let mut i64_local_gets: HashSet<usize> = HashSet::new();

        // Track stack depth to find which LocalGets feed into i64 ops
        for (i, op) in wasm_ops.iter().enumerate() {
            let count = Self::i64_operand_count(op);
            if count > 0 {
                // Walk backward to find the i64 operands (LocalGets or I64Consts)
                let mut found = 0;
                let mut j = i;
                while j > 0 && found < count {
                    j -= 1;
                    match &wasm_ops[j] {
                        // I64ExtendI32U/S consume an i32 LocalGet and produce an
                        // i64 — so they account for one i64 operand and we must
                        // skip the i32 LocalGet that immediately precedes them
                        // (otherwise we'd mistakenly mark that i32 LocalGet as
                        // i64, double-loading the local). See issue #93.
                        WasmOp::I64ExtendI32U | WasmOp::I64ExtendI32S => {
                            found += 1;
                            // Skip the i32 producer that fed this extend.
                            if j > 0
                                && matches!(
                                    &wasm_ops[j - 1],
                                    WasmOp::LocalGet(_) | WasmOp::I32Const(_)
                                )
                            {
                                j -= 1;
                            }
                        }
                        WasmOp::LocalGet(_) => {
                            i64_local_gets.insert(j);
                            found += 1;
                        }
                        WasmOp::I64Const(_) => {
                            found += 1;
                        }
                        // Skip non-value-producing ops
                        _ => {}
                    }
                }
            }
        }

        i64_local_gets
    }

    /// Convert WASM operations to optimization IR.
    ///
    /// ## Slot-stack model (issue #121)
    ///
    /// Each wasm op operates on a *value stack*; the IR represents that stack
    /// as `slot_stack: Vec<u32>` where each entry is the vreg id of a value
    /// currently live on the wasm stack. Producers push their `dest` vreg;
    /// consumers `pop()` to learn which vreg holds their source.
    ///
    /// `inst_id` is the unique IR instruction id (used for `Instruction::id`,
    /// `Opcode::Label::id`, branch targets, etc.). It is **independent** of
    /// `slot_stack` — incrementing `inst_id` does NOT push a slot, and popping
    /// a slot does NOT decrement `inst_id`.
    ///
    /// i64 values occupy **two** entries on `slot_stack` (lo first, then hi),
    /// matching the two-vreg-pair representation `(dest_lo, dest_hi)`.
    ///
    /// History — before this refactor `inst_id` was overloaded as both unique
    /// id AND vreg-slot index, and back-references like `inst_id-2` assumed
    /// a one-to-one correspondence with the wasm stack. Any op that consumed
    /// a stack slot without producing one (Drop, LocalSet, GlobalSet, stores,
    /// BrIf, …) broke that assumption and the next binary/unary op read a
    /// stale or unmapped slot — either silently miscompiling or tripping the
    /// `get_arm_reg` defensive panic (issue #121, Gale silicon report).
    fn wasm_to_ir(&self, wasm_ops: &[WasmOp]) -> Result<(Vec<Instruction>, Cfg)> {
        let mut builder = CfgBuilder::new();
        let mut instructions = Vec::new();
        let mut inst_id: usize = 0;

        // Producer-vreg stack mirroring the wasm value stack. See doc-comment
        // above. Pre-flight `wasm_stack_check` (in synth-frontend) plus the
        // wasm validator guarantee depth is sufficient for every pop, so
        // `.expect("wasm validator + pre-flight check guarantee stack depth")`
        // documents the invariant rather than masking a real bug.
        let mut slot_stack: Vec<u32> = Vec::new();

        // Analyze which LocalGets should produce i64 values (using 2 register slots)
        let i64_local_gets = Self::analyze_i64_local_gets(wasm_ops);

        // Track control flow block stack for proper branch target resolution
        // Each entry is (block_type, start_inst_id) where block_type: 0=block, 1=loop
        let mut block_stack: Vec<(u8, usize)> = Vec::new();

        for (wasm_idx, wasm_op) in wasm_ops.iter().enumerate() {
            builder.add_instruction();

            // Slot-stack convention (issue #121): producer arms compute their
            // src vreg ids by popping from `slot_stack`, then push their
            // dest's vreg id (= `inst_id as u32`). Pure consumer arms (Drop,
            // LocalSet, GlobalSet, stores, BrIf) pop and DO NOT push.
            //
            // Each i32-producer / i32-consumer arm below uses the helper
            // `let src? = slot_stack.pop().expect(...)`. The expect message
            // documents the invariant that the wasm validator + pre-flight
            // stack check have already proven depth is sufficient.

            // Helper macro for binary i32 ops: pops 2 (rhs first, then lhs in
            // wasm-stack order) and binds dest to a fresh vreg at `inst_id`.
            // We don't push `dest` here — that happens at the bottom of the
            // loop alongside the `inst_id += 1` for the fall-through arms.
            macro_rules! pop_i32_binary {
                () => {{
                    let src2 = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src1 = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    (OptReg(src1), OptReg(src2))
                }};
            }

            // Helper for unary i32 ops: pops 1 source. Returns `?` on
            // underflow so a malformed input that slipped past the pre-flight
            // check produces a typed Err instead of panicking — matches the
            // pop_i32_binary! handling. (The earlier slot_stack Result
            // conversion missed this macro because its `.expect(...)` ended
            // with `,` not `;`; the re-gated fuzz harness caught it.)
            macro_rules! pop_i32_unary {
                () => {{
                    let src = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    OptReg(src)
                }};
            }

            let opcode = match wasm_op {
                WasmOp::I32Const(val) => Opcode::Const {
                    dest: OptReg(inst_id as u32),
                    value: *val,
                },

                // Arithmetic operations (pop 2, push 1)
                WasmOp::I32Add => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Add {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Sub => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Sub {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Mul => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Mul {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32DivS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::DivS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32DivU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::DivU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32RemS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::RemS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32RemU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::RemU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }

                // Bitwise operations (pop 2, push 1)
                WasmOp::I32And => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::And {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Or => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Or {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Xor => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Xor {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Shl => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Shl {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32ShrS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::ShrS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32ShrU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::ShrU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Rotl => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Rotl {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Rotr => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Rotr {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }

                // Comparison operations (pop 2, push 1)
                WasmOp::I32Eq => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Eq {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32Ne => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::Ne {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32LtS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::LtS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32LtU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::LtU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32LeS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::LeS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32LeU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::LeU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32GtS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::GtS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32GtU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::GtU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32GeS => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::GeS {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }
                WasmOp::I32GeU => {
                    let (src1, src2) = pop_i32_binary!();
                    Opcode::GeU {
                        dest: OptReg(inst_id as u32),
                        src1,
                        src2,
                    }
                }

                // Equal to zero (unary comparison: pop 1, push 1)
                WasmOp::I32Eqz => Opcode::Eqz {
                    dest: OptReg(inst_id as u32),
                    src: pop_i32_unary!(),
                },

                // Bit count operations (pop 1, push 1)
                WasmOp::I32Clz => Opcode::Clz {
                    dest: OptReg(inst_id as u32),
                    src: pop_i32_unary!(),
                },
                WasmOp::I32Ctz => Opcode::Ctz {
                    dest: OptReg(inst_id as u32),
                    src: pop_i32_unary!(),
                },
                WasmOp::I32Popcnt => Opcode::Popcnt {
                    dest: OptReg(inst_id as u32),
                    src: pop_i32_unary!(),
                },

                // Sign extension (pop 1, push 1)
                WasmOp::I32Extend8S => Opcode::Extend8S {
                    dest: OptReg(inst_id as u32),
                    src: pop_i32_unary!(),
                },
                WasmOp::I32Extend16S => Opcode::Extend16S {
                    dest: OptReg(inst_id as u32),
                    src: pop_i32_unary!(),
                },

                // Memory and locals
                // For i64 LocalGets, we use I64Load which produces 2 register slots
                WasmOp::LocalGet(idx) => {
                    if i64_local_gets.contains(&wasm_idx) {
                        // i64 LocalGet pushes (lo, hi) onto slot_stack.
                        let lo = inst_id as u32;
                        let hi = (inst_id + 1) as u32;
                        let opcode = Opcode::I64Load {
                            dest_lo: OptReg(lo),
                            dest_hi: OptReg(hi),
                            addr: *idx,
                        };
                        instructions.push(Instruction {
                            id: inst_id,
                            opcode,
                            block_id: 0,
                            is_dead: false,
                        });
                        slot_stack.push(lo);
                        slot_stack.push(hi);
                        inst_id += 2; // Two unique IR ids for lo/hi
                        builder.add_instruction(); // Add extra instruction for hi part
                        continue; // Skip the normal instruction push at end of loop
                    } else {
                        // i32 LocalGet pushes its dest vreg.
                        Opcode::Load {
                            dest: OptReg(inst_id as u32),
                            addr: *idx,
                        }
                    }
                }
                // LocalSet pops 1 (i32 value) and emits a Store. No slot push.
                // Pre-fix: relied on `inst_id.saturating_sub(1)` which read the
                // most recently produced vreg — but if the next op was a
                // binary op, it would read the same slot, double-using it.
                // Issue #121.
                WasmOp::LocalSet(idx) => {
                    let src = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::Store {
                        src: OptReg(src),
                        addr: *idx,
                    }
                }

                // i64 operations (use register pairs on 32-bit ARM)
                // i64 values occupy 2 consecutive entries on slot_stack
                // (lo first, then hi), matching the (dest_lo, dest_hi) layout.
                WasmOp::I64Const(val) => {
                    // pushes 2 (lo, hi)
                    let lo = inst_id as u32;
                    let hi = (inst_id + 1) as u32;
                    let opcode = Opcode::I64Const {
                        dest_lo: OptReg(lo),
                        dest_hi: OptReg(hi),
                        value: *val,
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(lo);
                    slot_stack.push(hi);
                    inst_id += 2;
                    builder.add_instruction();
                    continue;
                }
                // i64 binary arithmetic ops: pops 4 / pushes 2.
                //
                // Each i64 is 2 slot_stack entries (lo, hi). We pop the
                // top-of-stack i64 first (src2_hi, src2_lo) then the next
                // (src1_hi, src1_lo). The result is pushed as (dest_lo,
                // dest_hi) so subsequent ops see the new i64 in the expected
                // order.
                //
                // Pre-fix this used `inst_id.saturating_sub(K)` arithmetic
                // which broke whenever an intervening op popped a slot
                // without producing one (Drop, LocalSet, …). Issue #121.
                WasmOp::I64Add
                | WasmOp::I64Sub
                | WasmOp::I64And
                | WasmOp::I64Or
                | WasmOp::I64Xor
                | WasmOp::I64Mul
                | WasmOp::I64DivS
                | WasmOp::I64DivU
                | WasmOp::I64RemS
                | WasmOp::I64RemU
                | WasmOp::I64Shl
                | WasmOp::I64ShrS
                | WasmOp::I64ShrU
                | WasmOp::I64Rotl
                | WasmOp::I64Rotr => {
                    let src2_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src2_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src1_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src1_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_lo_v = inst_id as u32;
                    let dest_hi_v = (inst_id + 1) as u32;
                    let dest_lo = OptReg(dest_lo_v);
                    let dest_hi = OptReg(dest_hi_v);
                    let src1_lo = OptReg(src1_lo_v);
                    let src1_hi = OptReg(src1_hi_v);
                    let src2_lo = OptReg(src2_lo_v);
                    let src2_hi = OptReg(src2_hi_v);
                    let opcode = match wasm_op {
                        WasmOp::I64Add => Opcode::I64Add {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Sub => Opcode::I64Sub {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64And => Opcode::I64And {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Or => Opcode::I64Or {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Xor => Opcode::I64Xor {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Mul => Opcode::I64Mul {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64DivS => Opcode::I64DivS {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64DivU => Opcode::I64DivU {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64RemS => Opcode::I64RemS {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64RemU => Opcode::I64RemU {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Shl => Opcode::I64Shl {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64ShrS => Opcode::I64ShrS {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64ShrU => Opcode::I64ShrU {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Rotl => Opcode::I64Rotl {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Rotr => Opcode::I64Rotr {
                            dest_lo,
                            dest_hi,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    // pushes 2 (dest_lo, dest_hi)
                    slot_stack.push(dest_lo_v);
                    slot_stack.push(dest_hi_v);
                    inst_id += 2;
                    builder.add_instruction();
                    continue;
                }

                // i64 comparisons: pops 4 (2 i64 pairs) / pushes 1 (i32 result).
                WasmOp::I64Eq
                | WasmOp::I64Ne
                | WasmOp::I64LtS
                | WasmOp::I64LtU
                | WasmOp::I64GtS
                | WasmOp::I64GtU
                | WasmOp::I64LeS
                | WasmOp::I64LeU
                | WasmOp::I64GeS
                | WasmOp::I64GeU => {
                    let src2_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src2_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src1_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src1_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_v = inst_id as u32;
                    let dest = OptReg(dest_v);
                    let src1_lo = OptReg(src1_lo_v);
                    let src1_hi = OptReg(src1_hi_v);
                    let src2_lo = OptReg(src2_lo_v);
                    let src2_hi = OptReg(src2_hi_v);
                    let opcode = match wasm_op {
                        WasmOp::I64Eq => Opcode::I64Eq {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64Ne => Opcode::I64Ne {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64LtS => Opcode::I64LtS {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64LtU => Opcode::I64LtU {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64GtS => Opcode::I64GtS {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64GtU => Opcode::I64GtU {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64LeS => Opcode::I64LeS {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64LeU => Opcode::I64LeU {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64GeS => Opcode::I64GeS {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        WasmOp::I64GeU => Opcode::I64GeU {
                            dest,
                            src1_lo,
                            src1_hi,
                            src2_lo,
                            src2_hi,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    // Single i32 result pushed.
                    slot_stack.push(dest_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 equal-to-zero: pops 2 (1 i64) / pushes 1 (i32).
                WasmOp::I64Eqz => {
                    let src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_v = inst_id as u32;
                    let opcode = Opcode::I64Eqz {
                        dest: OptReg(dest_v),
                        src_lo: OptReg(src_lo_v),
                        src_hi: OptReg(src_hi_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 count leading zeros: pops 2 (1 i64) / pushes 1 (i32).
                WasmOp::I64Clz => {
                    let src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_v = inst_id as u32;
                    let opcode = Opcode::I64Clz {
                        dest: OptReg(dest_v),
                        src_lo: OptReg(src_lo_v),
                        src_hi: OptReg(src_hi_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 count trailing zeros: pops 2 (1 i64) / pushes 1 (i32).
                WasmOp::I64Ctz => {
                    let src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_v = inst_id as u32;
                    let opcode = Opcode::I64Ctz {
                        dest: OptReg(dest_v),
                        src_lo: OptReg(src_lo_v),
                        src_hi: OptReg(src_hi_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 population count: pops 2 (1 i64) / pushes 1 (i32).
                WasmOp::I64Popcnt => {
                    let src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_v = inst_id as u32;
                    let opcode = Opcode::I64Popcnt {
                        dest: OptReg(dest_v),
                        src_lo: OptReg(src_lo_v),
                        src_hi: OptReg(src_hi_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 in-place sign extension: pops 2 (1 i64) / pushes 2 (1 i64).
                // src_hi is discarded; dest is freshly allocated.
                WasmOp::I64Extend8S => {
                    let _src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_lo_v = inst_id as u32;
                    let dest_hi_v = (inst_id + 1) as u32;
                    let opcode = Opcode::I64Extend8S {
                        dest_lo: OptReg(dest_lo_v),
                        dest_hi: OptReg(dest_hi_v),
                        src_lo: OptReg(src_lo_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_lo_v);
                    slot_stack.push(dest_hi_v);
                    inst_id += 2;
                    builder.add_instruction();
                    continue;
                }

                WasmOp::I64Extend16S => {
                    let _src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_lo_v = inst_id as u32;
                    let dest_hi_v = (inst_id + 1) as u32;
                    let opcode = Opcode::I64Extend16S {
                        dest_lo: OptReg(dest_lo_v),
                        dest_hi: OptReg(dest_hi_v),
                        src_lo: OptReg(src_lo_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_lo_v);
                    slot_stack.push(dest_hi_v);
                    inst_id += 2;
                    builder.add_instruction();
                    continue;
                }

                WasmOp::I64Extend32S => {
                    let _src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_lo_v = inst_id as u32;
                    let dest_hi_v = (inst_id + 1) as u32;
                    let opcode = Opcode::I64Extend32S {
                        dest_lo: OptReg(dest_lo_v),
                        dest_hi: OptReg(dest_hi_v),
                        src_lo: OptReg(src_lo_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(dest_lo_v);
                    slot_stack.push(dest_hi_v);
                    inst_id += 2;
                    builder.add_instruction();
                    continue;
                }

                // i32 -> i64 zero-extend: pops 1 (i32) / pushes 2 (i64).
                //
                // By IR convention `dest_lo` aliases `src` (same vreg, same
                // value semantically); `dest_hi` is a fresh slot holding 0.
                // We push the SAME src vreg as dest_lo onto slot_stack, then
                // push the fresh dest_hi — so a subsequent i64 op pops
                // (dest_hi, dest_lo=src) correctly.
                WasmOp::I64ExtendI32U => {
                    let src_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_hi_v = inst_id as u32;
                    let opcode = Opcode::I64ExtendI32U {
                        dest_lo: OptReg(src_v),
                        dest_hi: OptReg(dest_hi_v),
                        src: OptReg(src_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(src_v); // dest_lo aliases src
                    slot_stack.push(dest_hi_v);
                    inst_id += 1; // only dest_hi is a fresh IR id; dest_lo reuses src
                    builder.add_instruction();
                    continue;
                }

                // i32 -> i64 sign-extend. Same slot accounting as I64ExtendI32U.
                WasmOp::I64ExtendI32S => {
                    let src_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let dest_hi_v = inst_id as u32;
                    let opcode = Opcode::I64ExtendI32S {
                        dest_lo: OptReg(src_v),
                        dest_hi: OptReg(dest_hi_v),
                        src: OptReg(src_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    slot_stack.push(src_v);
                    slot_stack.push(dest_hi_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // i64 -> i32 wrap (truncate): pops 2 (i64) / pushes 1 (i32).
                // The result IS the low 32 bits of the input i64, so `dest`
                // aliases `src_lo` by IR convention. `src_hi` is discarded.
                WasmOp::I32WrapI64 => {
                    let _src_hi_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let src_lo_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let opcode = Opcode::I32WrapI64 {
                        dest: OptReg(src_lo_v),
                        src_lo: OptReg(src_lo_v),
                    };
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode,
                        block_id: 0,
                        is_dead: false,
                    });
                    // dest aliases src_lo (same vreg, same value); we push
                    // src_lo back onto slot_stack so consumers see the wrap
                    // result. No new inst_id needed because dest reuses
                    // src_lo's vreg — but we still consumed one Instruction
                    // slot for the I32WrapI64 op itself, so inst_id += 1.
                    slot_stack.push(src_lo_v);
                    inst_id += 1;
                    builder.add_instruction();
                    continue;
                }

                // Select: dest = cond != 0 ? val_true : val_false
                // Stack: pops 3 (val_true, val_false, cond), pushes 1.
                WasmOp::Select => {
                    let cond_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let val_false_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let val_true_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::Select {
                        dest: OptReg(inst_id as u32),
                        val_true: OptReg(val_true_v),
                        val_false: OptReg(val_false_v),
                        cond: OptReg(cond_v),
                    }
                }

                // ========================================================================
                // Control Flow Operations (Loop Support)
                // ========================================================================

                // Loop: emit a label at the start (backward branch target).
                // No stack effect — does not touch slot_stack.
                WasmOp::Loop => {
                    block_stack.push((1, inst_id)); // 1 = loop
                    Opcode::Label { id: inst_id }
                }

                // Block: emit a label placeholder (forward branch target at End).
                // No stack effect.
                WasmOp::Block => {
                    block_stack.push((0, inst_id)); // 0 = block
                    Opcode::Nop // Label will be at End
                }

                // End: marks the end of a block/loop/function. No stack effect.
                //
                // #483: a forward `block` is the branch target of any `br`/`br_if`
                // that exits it — and those branches target the id pushed when the
                // `Block` was opened (block_stack stores the Block's inst_id, and
                // the `Block` arm emits only a `Nop`, no label). So the End that
                // closes a block must emit its label with the BLOCK's id, not its
                // own, or the branch resolves against an id no label carries and is
                // left as the unpatched placeholder (offset 0 → a mid-instruction
                // landing — the #483 miscompile). Loop ends and the function-end
                // keep their own id: a loop's target label is already at its start
                // (backward branch), and the function end is just the structural
                // trailing label.
                WasmOp::End => match block_stack.pop() {
                    Some((0, block_id)) => Opcode::Label { id: block_id },
                    _ => Opcode::Label { id: inst_id },
                },

                // Br: unconditional branch to label. No stack effect at IR
                // level (the wasm validator handles unreachable stack after Br).
                //
                // #500: a branch whose depth reaches the FUNCTION level (depth
                // >= block_stack.len(), i.e. `br N` targeting the implicit
                // function body) has no label to land on — the old
                // `saturating_sub` silently clamped it onto the OUTERMOST
                // block's end (code after that block still executed) or, with
                // no open blocks, onto the bogus id 0. Both are the
                // unresolved/misresolved-forward-branch miscompile class.
                // Decline to the direct selector, whose function-end label
                // lowering handles function-level branches.
                WasmOp::Br(depth) => {
                    let Some(target_idx) = block_stack.len().checked_sub(1 + *depth as usize)
                    else {
                        return Err(synth_core::Error::validation(
                            "optimized lowering path does not support a function-level \
                             `br` (depth reaches the implicit function body); the \
                             direct instruction selector lowers it — issue #500",
                        ));
                    };
                    let (_block_type, target_inst) = block_stack[target_idx];
                    Opcode::Branch {
                        target: target_inst,
                    }
                }

                // BrIf: pops cond (i32). The value beneath remains on the
                // wasm stack — slot_stack reflects that: pop 1 only.
                // Function-level depth declines like `Br` above (#500).
                WasmOp::BrIf(depth) => {
                    let cond_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let Some(target_idx) = block_stack.len().checked_sub(1 + *depth as usize)
                    else {
                        return Err(synth_core::Error::validation(
                            "optimized lowering path does not support a function-level \
                             `br_if` (depth reaches the implicit function body); the \
                             direct instruction selector lowers it — issue #500",
                        ));
                    };
                    let (_block_type, target_inst) = block_stack[target_idx];
                    Opcode::CondBranch {
                        cond: OptReg(cond_v),
                        target: target_inst,
                    }
                }

                // LocalTee: pops 1, pushes 1 (value stays on stack as a copy).
                // TeeStore = Store + Copy: writes to local and produces a
                // fresh dest vreg holding the same value for the next op.
                WasmOp::LocalTee(idx) => {
                    let src_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::TeeStore {
                        dest: OptReg(inst_id as u32),
                        src: OptReg(src_v),
                        addr: *idx,
                    }
                }

                // ========================================================================
                // Linear Memory Operations (i32.load / i32.store)
                // ========================================================================

                // I32Load: pops 1 (addr), pushes 1 (value).
                WasmOp::I32Load { offset, .. } => {
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemLoad {
                        dest: OptReg(inst_id as u32),
                        addr: OptReg(addr_v),
                        offset: *offset,
                    }
                }

                // I32Store: pops 2 (addr, value), pushes 0.
                WasmOp::I32Store { offset, .. } => {
                    let value_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemStore {
                        src: OptReg(value_v),
                        addr: OptReg(addr_v),
                        offset: *offset,
                    }
                }

                // ===== Sub-word linear-memory ops =====
                //
                // Loads: pops 1 (addr), pushes 1 (value).
                // Stores: pops 2 (addr, value), pushes 0.
                WasmOp::I32Load8S { offset, .. } => {
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemLoadSubword {
                        dest: OptReg(inst_id as u32),
                        addr: OptReg(addr_v),
                        offset: *offset,
                        width: 1,
                        signed: true,
                    }
                }
                WasmOp::I32Load8U { offset, .. } => {
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemLoadSubword {
                        dest: OptReg(inst_id as u32),
                        addr: OptReg(addr_v),
                        offset: *offset,
                        width: 1,
                        signed: false,
                    }
                }
                WasmOp::I32Load16S { offset, .. } => {
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemLoadSubword {
                        dest: OptReg(inst_id as u32),
                        addr: OptReg(addr_v),
                        offset: *offset,
                        width: 2,
                        signed: true,
                    }
                }
                WasmOp::I32Load16U { offset, .. } => {
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemLoadSubword {
                        dest: OptReg(inst_id as u32),
                        addr: OptReg(addr_v),
                        offset: *offset,
                        width: 2,
                        signed: false,
                    }
                }
                WasmOp::I32Store8 { offset, .. } => {
                    let value_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemStoreSubword {
                        src: OptReg(value_v),
                        addr: OptReg(addr_v),
                        offset: *offset,
                        width: 1,
                    }
                }
                WasmOp::I32Store16 { offset, .. } => {
                    let value_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    let addr_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemStoreSubword {
                        src: OptReg(value_v),
                        addr: OptReg(addr_v),
                        offset: *offset,
                        width: 2,
                    }
                }

                // ===== Globals =====
                //
                // GlobalGet pushes a fresh i32; GlobalSet pops one.
                //
                // #643: this i32-single-slot model (and ir_to_arm's
                // `[R9, idx*4]` lowering) is WIDTH-NAIVE — it truncated i64
                // globals and mis-addressed globals behind a wide slot. The
                // backend's #643 pre-gate routes every global-touching
                // function of a module with any i64/f64/v128 global to the
                // direct selector, so these opcodes only ever see modules
                // whose globals are all 4-byte (`idx * 4` is then exact).
                WasmOp::GlobalGet(idx) => Opcode::GlobalGet {
                    dest: OptReg(inst_id as u32),
                    idx: *idx,
                },
                WasmOp::GlobalSet(idx) => {
                    let src_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::GlobalSet {
                        src: OptReg(src_v),
                        idx: *idx,
                    }
                }

                // ===== Memory size / grow =====
                //
                // MemorySize: pushes 1 (i32 result). No stack input.
                // MemoryGrow: pops 1 (delta in pages), pushes 1 (previous size).
                WasmOp::MemorySize(_) => Opcode::MemorySize {
                    dest: OptReg(inst_id as u32),
                },
                WasmOp::MemoryGrow(_) => {
                    let delta_v = slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    Opcode::MemoryGrow {
                        dest: OptReg(inst_id as u32),
                        delta: OptReg(delta_v),
                    }
                }

                // ===== Direct call =====
                //
                // Pre-fix, `WasmOp::Call` fell through to `Opcode::Nop`, so
                // the call's result vreg never got mapped to an ARM register.
                // A downstream consumer of the call result (e.g., the outer
                // `i32.add` of two recursive `fib` calls in `simple_add.wat`)
                // then resolved its `src` vreg via `get_arm_reg`, hit the
                // unmapped path, and either triggered the PR #101 defensive
                // panic or silently consumed whatever value happened to be in
                // R0 — a clobber-via-stale-AAPCS-param bug, same class as #93.
                //
                // We emit an `Opcode::Call` here so `ir_to_arm` can bind
                // `dest` to R0 (where the AAPCS return value lands). This
                // does NOT model the call's clobber of R0..R3 — a deeper
                // call-lowering rework is needed for fully correct codegen
                // across calls (e.g., reloading params after the BL); that's
                // a follow-up. The narrow goal here is "compile without
                // panicking on lawful WASM that contains `call`."
                //
                // Note: WASM `call` may also pop N args from the stack (for
                // a function taking N params). The IR doesn't yet model that;
                // for now arguments are assumed to already be in R0..R3 by
                // virtue of being the most-recently-produced vregs.
                WasmOp::Call(func_idx) => Opcode::Call {
                    dest: OptReg(inst_id as u32),
                    func_idx: *func_idx,
                },

                // ===== Pure consumers (pop without producing IR) =====
                //
                // Drop pops the top wasm-stack value and emits nothing —
                // it's a wasm-stack hygiene op with no IR semantics. We
                // `continue` after popping to skip both the instruction
                // push and the inst_id increment (no IR id is consumed).
                //
                // Pre-fix Drop fell through to `_ => Opcode::Nop`. The Nop
                // emission was harmless on its own, but Drop's lack of a
                // `slot_stack.pop()` meant the very next binary op would
                // misread `inst_id-1` as "the value Drop discarded" instead
                // of "the value beneath Drop's consumed slot." Issue #121.
                WasmOp::Drop => {
                    slot_stack.pop().ok_or_else(|| {
                        synth_core::Error::validation(
                            "wasm stack underflow in wasm_to_ir (slot_stack pop on empty)",
                        )
                    })?;
                    continue;
                }

                // #665: `unreachable` must TRAP (WASM §4.4.5). The optimized
                // path's local `Opcode` enum has no trap opcode, and adding
                // one would ripple through the #513 mirror-pinned
                // reg_effect/rewrite_op machinery — so decline to the direct
                // selector, whose `Unreachable` arm emits `UDF #0`. Same
                // decline-don't-drop pattern as #120 floats and the #500
                // non-tail `return` (this arm previously lumped `unreachable`
                // in with Nop as a placeholder — a silent fall-through).
                WasmOp::Unreachable => {
                    return Err(synth_core::Error::validation(
                        "optimized lowering path does not support `unreachable` \
                         (no trap opcode in the bridge IR); the direct \
                         instruction selector lowers it to UDF #0 — issue #665",
                    ));
                }

                // ===== Stack-neutral control-flow / no-op ops =====
                //
                // Nop / Return have no slot_stack effect at
                // this layer (Return's value handling is done later by the
                // function-epilogue codegen in `ir_to_arm`). They still
                // emit an IR Nop placeholder so the IR length is in lockstep
                // with the wasm op index for any downstream pass that
                // relies on positional alignment.
                WasmOp::Nop | WasmOp::Return => {
                    // #500: `return` is representable here only as a Nop
                    // placeholder — the real epilogue is emitted once at the
                    // function end, and the callee-saved push/pop frame is
                    // wrapped around the body AFTER this lowering, so a
                    // mid-body `bx lr` would skip the pop. The placeholder is
                    // therefore correct ONLY in tail position (everything
                    // after it structural `End`s/`Nop`s). A non-tail `return`
                    // used to be silently dropped — execution fell THROUGH
                    // into the code after it (`early_ret(1)` also stored the
                    // post-return value; red in
                    // `cf_shapes_500_differential.py`). Decline it to the
                    // direct selector, whose `Return` arm deallocates the
                    // frame and returns correctly mid-function.
                    if matches!(wasm_op, WasmOp::Return)
                        && wasm_ops[wasm_idx + 1..]
                            .iter()
                            .any(|op| !matches!(op, WasmOp::End | WasmOp::Nop))
                    {
                        return Err(synth_core::Error::validation(
                            "optimized lowering path does not support a non-tail \
                             `return`; the direct instruction selector lowers it — \
                             issue #500",
                        ));
                    }
                    instructions.push(Instruction {
                        id: inst_id,
                        opcode: Opcode::Nop,
                        block_id: 0,
                        is_dead: false,
                    });
                    inst_id += 1;
                    continue;
                }

                // Fallback for unsupported ops.
                //
                // We do NOT touch slot_stack here — by design. If an unknown
                // op had a stack effect, downstream consumers will surface a
                // typed `Err` via `slot_stack.pop().ok_or_else(...)?` instead
                // of silently mis-binding vregs. That's the same bug-finder
                // class introduced for issue #93 (the slot_stack rework, #121,
                // preserved it); the only change is that the failure mode is
                // now an `Err` propagation, not a `panic!`, per the harness
                // contract that lowering returns Err on malformed input.
                _ => Opcode::Nop,
            };

            // Determine slot_stack effect from the opcode just produced.
            // Arms that already `continue` above handle their slot_stack
            // updates inline; this fallback covers single-producer i32 arms
            // (Const, Load, GlobalGet, MemorySize, MemLoad, MemLoadSubword,
            // Add/Sub/.../Eqz, Select, TeeStore, MemoryGrow, Call) and
            // pure label/branch/store arms (Loop, Block, End, Br, CondBranch,
            // Store, MemStore, MemStoreSubword, GlobalSet).
            match &opcode {
                // Single-i32-producer opcodes: push `inst_id` as the dest slot.
                Opcode::Add { .. }
                | Opcode::Sub { .. }
                | Opcode::Mul { .. }
                | Opcode::DivS { .. }
                | Opcode::DivU { .. }
                | Opcode::RemS { .. }
                | Opcode::RemU { .. }
                | Opcode::And { .. }
                | Opcode::Or { .. }
                | Opcode::Xor { .. }
                | Opcode::Shl { .. }
                | Opcode::ShrS { .. }
                | Opcode::ShrU { .. }
                | Opcode::Rotl { .. }
                | Opcode::Rotr { .. }
                | Opcode::Eq { .. }
                | Opcode::Ne { .. }
                | Opcode::LtS { .. }
                | Opcode::LtU { .. }
                | Opcode::LeS { .. }
                | Opcode::LeU { .. }
                | Opcode::GtS { .. }
                | Opcode::GtU { .. }
                | Opcode::GeS { .. }
                | Opcode::GeU { .. }
                | Opcode::Eqz { .. }
                | Opcode::Clz { .. }
                | Opcode::Ctz { .. }
                | Opcode::Popcnt { .. }
                | Opcode::Extend8S { .. }
                | Opcode::Extend16S { .. }
                | Opcode::Const { .. }
                | Opcode::Load { .. }
                | Opcode::GlobalGet { .. }
                | Opcode::MemorySize { .. }
                | Opcode::MemoryGrow { .. }
                | Opcode::MemLoad { .. }
                | Opcode::MemLoadSubword { .. }
                | Opcode::Select { .. }
                | Opcode::TeeStore { .. }
                | Opcode::Call { .. } => {
                    slot_stack.push(inst_id as u32);
                }
                // Pure consumers / control flow / no-ops: no slot push.
                Opcode::Store { .. }
                | Opcode::MemStore { .. }
                | Opcode::MemStoreSubword { .. }
                | Opcode::GlobalSet { .. }
                | Opcode::Branch { .. }
                | Opcode::CondBranch { .. }
                | Opcode::Label { .. }
                | Opcode::Return { .. }
                | Opcode::Copy { .. }
                | Opcode::Nop => {}
                // i64 ops have their own continue paths above and do not
                // reach this match — defensively skip if they ever do.
                _ => {}
            }

            instructions.push(Instruction {
                id: inst_id,
                opcode,
                block_id: 0,
                is_dead: false,
            });

            inst_id += 1;
        }

        let cfg = builder.build();
        Ok((instructions, cfg))
    }

    /// Optimize WASM operation sequence and return the optimized IR
    ///
    /// This is the main entry point for the optimization pipeline. It converts
    /// WASM ops to the optimizer IR, runs all enabled passes, and returns
    /// the optimized instructions along with the CFG and statistics.
    pub fn optimize_full(
        &self,
        wasm_ops: &[WasmOp],
    ) -> Result<(Vec<Instruction>, Cfg, OptimizationStats)> {
        if wasm_ops.is_empty() {
            return Ok((
                Vec::new(),
                CfgBuilder::new().build(),
                OptimizationStats::default(),
            ));
        }

        // Pre-flight: reject obvious stack underflow as a typed error so the
        // slot_stack model in `wasm_to_ir` never has to error on an empty
        // stack. Without this, the fuzz harness can construct inputs like
        // `[I32Sub, I32Const(0)]` that bypass wasm validation and trip
        // `slot_stack.pop()` directly. Production callers come through
        // wasmparser (which validates); this safety net catches direct
        // callers (fuzz harnesses, hand-built `Vec<WasmOp>`).
        synth_core::wasm_stack_check::check_no_underflow(wasm_ops)?;

        // Issue #120: the optimized path (`wasm_to_ir` → `ir_to_arm`) has no
        // handlers for scalar f32/f64 ops — the IR `Opcode` enum has no float
        // opcodes. Rather than silently emit `Opcode::Nop` for a value-producing
        // float op (which leaves a downstream consumer with an unmapped vreg and
        // trips the PR #101 defensive panic), decline the whole module here with
        // a typed error. The backend falls back to `select_with_stack`, the
        // non-optimized path, which handles f32 via VFP/FPU.
        if let Some(float_op) = wasm_ops.iter().find(|op| Self::is_unsupported_float_op(op)) {
            return Err(Error::UnsupportedInstruction(format!(
                "optimized lowering path does not support float ops ({float_op:?}); \
                 the non-optimized instruction selector handles f32 — issue #120"
            )));
        }

        // VCR-MEM-002 phase 1 (#406): the optimized path has no per-memory
        // base — `wasm_to_ir` would drop a `MultiMemory` load/store to the
        // catch-all `Opcode::Nop` (the #120/#93 silent-drop class) or, worse,
        // alias it onto the one absolute linmem base. Decline up front; the
        // direct selector lowers it on --relocatable (and declines loudly
        // everywhere else).
        if let Some(mm_op) = wasm_ops
            .iter()
            .find(|op| matches!(op, WasmOp::MultiMemory { .. }))
        {
            return Err(Error::UnsupportedInstruction(format!(
                "optimized lowering path does not support multi-memory ops \
                 ({mm_op:?}); only the direct selector on --relocatable lowers \
                 a non-default memory — issue #406"
            )));
        }
        // #406: same for `memory.size`/`memory.grow` on a non-default memory —
        // the optimized path's lowering reads R10 / emits -1 for MEMORY 0.
        if let Some(ms_op) = wasm_ops
            .iter()
            .find(|op| matches!(op, WasmOp::MemorySize(k) | WasmOp::MemoryGrow(k) if *k != 0))
        {
            return Err(Error::UnsupportedInstruction(format!(
                "optimized lowering path does not support {ms_op:?} on a \
                 non-default memory (R10 is memory 0's size register) — issue #406"
            )));
        }

        // #372: the optimized path also has no IR opcode for full-width
        // `i64.load`/`i64.store` — it would drop them to a stub (`ld64` -> `bx
        // lr`). Decline so the backend falls back to the direct selector, which
        // lowers them to a correct lo/hi register-pair access (I64Ldr/I64Str,
        // now index-correct per #372). Same decline pattern as #120/#188.
        if let Some(mem_op) = wasm_ops
            .iter()
            .find(|op| matches!(op, WasmOp::I64Load { .. } | WasmOp::I64Store { .. }))
        {
            return Err(Error::UnsupportedInstruction(format!(
                "optimized lowering path does not support full-width i64 memory \
                 ops ({mem_op:?}); the direct instruction selector lowers them — issue #372"
            )));
        }

        // #374: bulk-memory `memory.copy`/`memory.fill` have no IR opcode in the
        // optimized path (the `Opcode` enum has no bulk-mem). Decline so the
        // backend falls back to the direct selector, which lowers them to a
        // bounds-checked byte loop (select_with_stack). Same decline pattern as
        // #120/#188/#372.
        if let Some(bulk_op) = wasm_ops
            .iter()
            .find(|op| matches!(op, WasmOp::MemoryCopy | WasmOp::MemoryFill))
        {
            return Err(Error::UnsupportedInstruction(format!(
                "optimized lowering path does not support bulk-memory \
                 ops ({bulk_op:?}); the direct instruction selector lowers them — issue #374"
            )));
        }

        // #642: `call_indirect` has no IR opcode either — it previously fell
        // through `wasm_to_ir`'s `_ => Opcode::Nop` fallback. Decline
        // EXPLICITLY so the backend falls back to the direct selector, which
        // emits the guarded dispatch (runtime bounds check + compile-time
        // closed-world type check, WASM Core §4.4.8). Same decline pattern as
        // #120/#372/#374.
        if wasm_ops
            .iter()
            .any(|op| matches!(op, WasmOp::CallIndirect { .. }))
        {
            return Err(Error::UnsupportedInstruction(
                "optimized lowering path does not support call_indirect; the direct \
                 instruction selector emits the guarded table dispatch — issue #642"
                    .to_string(),
            ));
        }

        // Issue #178/#180: the optimized linear-memory miscompilation was
        // root-caused to the Thumb encoder, NOT this lowering — `ArmOp::Add`
        // (and `Adds`/`Subs`) unconditionally used the 16-bit form, whose 3-bit
        // register fields overflow for the R12 base scratch (and i64 R8-R11
        // pairs), so `add ip,ip,r0` was emitted as `adds r4,r5,r1`, dropping the
        // address operand. Fixed in `arm_encoder.rs` (high-register → 32-bit
        // ADD.W/ADDS.W/SUBS.W). The temporary #179 decline (and its
        // `is_linear_memory_op` helper) are removed — the optimized memory path
        // now lowers correctly (byte-verified against `--no-optimize`).

        // Preprocess: convert if-else patterns to select
        let preprocessed = self.preprocess_wasm_ops(wasm_ops);

        // #500: a real `if`/`else` that SURVIVES the select-idiom preprocessing
        // has no IR lowering — `wasm_to_ir` dropped `WasmOp::If`/`Else` to
        // `Opcode::Nop`, so BOTH arms executed unconditionally (the condition
        // was never even tested; `real_ifelse(1)` stored the else-arm's value —
        // a silent miscompile, red in `cf_shapes_500_differential.py`). Decline
        // to the direct selector, whose label-form `If`/`Else`/`End` lowering
        // is correct. Same honest-degradation pattern as #120/#372/#374. The
        // check runs on the PREPROCESSED stream so the select-idiom shapes
        // (patterns 1–3) stay on the optimized path.
        if preprocessed
            .iter()
            .any(|op| matches!(op, WasmOp::If | WasmOp::Else))
        {
            return Err(Error::UnsupportedInstruction(
                "optimized lowering path does not support a non-select `if`/`else` \
                 (WasmOp::If survived preprocessing); the direct instruction \
                 selector lowers it — issue #500"
                    .to_string(),
            ));
        }

        // Convert to IR
        let (mut instructions, mut cfg) = self.wasm_to_ir(&preprocessed)?;

        // Build and run optimization pipeline
        let result = self.run_passes(&mut cfg, &mut instructions);

        // Filter out dead/nop instructions
        let live_instructions: Vec<Instruction> = instructions
            .into_iter()
            .filter(|i| !i.is_dead && i.opcode != Opcode::Nop)
            .collect();

        Ok((
            live_instructions,
            cfg,
            OptimizationStats {
                removed: result.removed_count,
                modified: result.modified_count,
                added: result.added_count,
                passes_run: self.count_enabled_passes(),
            },
        ))
    }

    /// Count how many passes are enabled
    fn count_enabled_passes(&self) -> usize {
        let mut count = 0;
        if self.config.enable_peephole {
            count += 1;
        }
        if self.config.enable_constant_folding {
            count += 1;
        }
        if self.config.enable_algebraic {
            count += 1;
        }
        if self.config.enable_cse {
            count += 1;
        }
        if self.config.enable_dce {
            count += 1;
        }
        count
    }

    /// Run optimization passes on the given instructions
    fn run_passes(&self, cfg: &mut Cfg, instructions: &mut Vec<Instruction>) -> OptResult {
        let mut manager = PassManager::new().with_max_iterations(self.config.max_iterations);

        if self.config.enable_peephole {
            let pass = if self.config.verbose {
                PeepholeOptimization::new().with_verbose()
            } else {
                PeepholeOptimization::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_constant_folding {
            let pass = if self.config.verbose {
                ConstantFolding::new().with_verbose()
            } else {
                ConstantFolding::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_algebraic {
            let pass = if self.config.verbose {
                AlgebraicSimplification::new().with_verbose()
            } else {
                AlgebraicSimplification::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_cse {
            let pass = if self.config.verbose {
                CommonSubexpressionElimination::new().with_verbose()
            } else {
                CommonSubexpressionElimination::new()
            };
            manager = manager.add_pass(pass);
        }

        if self.config.enable_dce {
            let pass = if self.config.verbose {
                DeadCodeElimination::new().with_verbose()
            } else {
                DeadCodeElimination::new()
            };
            manager = manager.add_pass(pass);
        }

        manager.run(cfg, instructions)
    }

    /// Optimize WASM operation sequence (legacy - returns only stats)
    pub fn optimize(&self, wasm_ops: &[WasmOp]) -> Result<OptimizationStats> {
        if wasm_ops.is_empty() {
            return Ok(OptimizationStats::default());
        }

        // Preprocess and convert to IR
        let preprocessed = self.preprocess_wasm_ops(wasm_ops);
        let (mut instructions, mut cfg) = self.wasm_to_ir(&preprocessed)?;
        let result = self.run_passes(&mut cfg, &mut instructions);

        Ok(OptimizationStats {
            removed: result.removed_count,
            modified: result.modified_count,
            added: result.added_count,
            passes_run: self.count_enabled_passes(),
        })
    }

    /// Get the current configuration
    pub fn config(&self) -> &OptimizationConfig {
        &self.config
    }

    /// Convert optimized IR instructions back to ARM instructions
    ///
    /// This function maps the register-based optimizer IR to ARM instructions.
    /// For function parameters, local indices 0..num_params map to R0..R3 per AAPCS.
    ///
    /// Returns `Err` (rather than panicking) when an IR virtual register has no
    /// assigned ARM register and no spill slot. With valid IR produced by
    /// `wasm_to_ir` (itself guarded by the `wasm_stack_check` pre-flight) this
    /// never happens, so an `Err` here is still the issue-#93-class bug signal
    /// it always was — it just no longer kills the process. Callers in the
    /// fuzz/AOT pipeline propagate the `Err` instead of crashing.
    pub fn ir_to_arm(&self, instructions: &[Instruction], num_params: usize) -> Result<Vec<ArmOp>> {
        self.spill_on_exhaust_fired.set(false);
        let (out, acted, guards_elided) = self.ir_to_arm_impl(instructions, num_params, true)?;
        // VCR-VER-001 scoping (#242): constant-divisor guard elision is part
        // of the post-exhaustion QUALITY story — it exists so a function that
        // only compiles on this path *because of the spill lever* is not worse
        // than its direct lowering. A function the exhaustion machinery never
        // touched must stay byte-identical flag-on (the `vcr_ver_001_gate_242`
        // contract), so if guards were elided but no pre-step action fired,
        // rebuild without elision. (One extra lowering pass for exactly the
        // functions in that corner; allocation is deterministic, so the
        // rebuild differs only by the reinstated guards.)
        if guards_elided > 0 && !acted {
            let (out, acted, _) = self.ir_to_arm_impl(instructions, num_params, false)?;
            self.spill_on_exhaust_fired.set(acted);
            return Ok(out);
        }
        self.spill_on_exhaust_fired.set(acted || guards_elided > 0);
        Ok(out)
    }

    /// The lowering behind [`OptimizerBridge::ir_to_arm`]. Returns the ARM
    /// stream plus two VCR-VER-001 facts: whether the spill-on-exhaustion
    /// pre-step ACTED (reinstated a spilled source / evicted for a dest or
    /// pair — i.e. flag-on-only behavior shaped the bytes), and how many
    /// constant-divisor trap guards were elided (`elide_div_guards` gates the
    /// elision; `false` keeps every guard, byte-identical to shipping).
    fn ir_to_arm_impl(
        &self,
        instructions: &[Instruction],
        num_params: usize,
        elide_div_guards: bool,
    ) -> Result<(Vec<ArmOp>, bool, usize)> {
        use crate::rules::{ArmOp, Operand2, Reg};
        use std::collections::HashMap;

        // #188: the optimized path's register allocator does NOT model the
        // AAPCS caller-saved clobber of a `BL` (R0–R3, R12). A function
        // containing a LOCAL call can therefore read a param (or temp) from a
        // register the callee overwrote — the confirmed miscompile in issue
        // #188. Decline such functions so the backend falls back to the direct
        // `select_with_stack` selector, which spills/reloads caller-saved
        // registers across calls. This is honest degradation: the function
        // still compiles correctly, just without IR-level optimization.
        //
        // Import calls (`func_idx < num_imports`) are NOT declined: they keep
        // going through the optimized path so the CLI's import-field-name
        // relocation rewrite (`func_N` → wasm field name, #173) still applies.
        // (Caller-saved preservation across import calls is a separate, pre-
        // existing gap tracked outside #188.)
        if instructions.iter().any(|inst| {
            matches!(inst.opcode, Opcode::Call { func_idx, .. } if func_idx >= self.num_imports)
        }) {
            return Err(synth_core::Error::synthesis(
                "optimized path declines functions with local calls (no caller-saved \
                 clobber model — see #188); falling back to direct selector"
                    .to_string(),
            ));
        }

        // #359: this lowering homes only params 0..4 in R0..R3 (see the
        // `addr < num_params && addr < 4` Load map below); a 5th+ param arrives
        // on the AAPCS incoming stack and would be silently read from a garbage
        // temp register. Decline functions with >4 params so they fall back to
        // the direct selector, which implements the stack-argument path (#359).
        if num_params > 4 {
            return Err(synth_core::Error::synthesis(
                "optimized path declines functions with >4 params (no AAPCS \
                 stack-argument model — see #359); falling back to direct selector"
                    .to_string(),
            ));
        }

        // #518: this lowering cannot home an i64 PARAM correctly — it has only the
        // param COUNT, not the per-param TYPES, so it cannot compute the AAPCS
        // even-aligned register pair an i64 param occupies (the `I64Load` arm's
        // `num_params >= 2/4` guard conflated register-count with param-count and
        // dropped the param). Decline any function that READS an i64 param (an
        // `I64Load` from a param index) to the direct selector, which homes the
        // pair via `aapcs_param_regs`. Honest degradation (the #359/#188/#507
        // pattern); functions with no i64-param read are untouched (byte-identical).
        if instructions.iter().any(|inst| {
            matches!(inst.opcode, Opcode::I64Load { addr, .. } if (addr as usize) < num_params)
        }) {
            return Err(synth_core::Error::synthesis(
                "optimized path declines functions that read an i64 param (no \
                 per-param AAPCS pair model — see #518); falling back to direct \
                 selector"
                    .to_string(),
            ));
        }

        // #377: `--safety-bounds mask` — the masking transform mutates the
        // address register in place (`AND addr, addr, R10`), which is unsound
        // here: a vreg's ARM register may be read again later (the optimized
        // path is not single-use), and the access sequence has no second
        // scratch to mask into (R12 already carries the materialized base).
        // Decline to the direct selector, which implements masking. Honest
        // degradation (the #359/#188/#518 pattern) — the flag is always
        // honored, never silently dropped.
        if self.bounds_check == BoundsCheckConfig::Masking
            && instructions.iter().any(|inst| {
                matches!(
                    inst.opcode,
                    Opcode::MemLoad { .. }
                        | Opcode::MemStore { .. }
                        | Opcode::MemLoadSubword { .. }
                        | Opcode::MemStoreSubword { .. }
                )
            })
        {
            return Err(synth_core::Error::synthesis(
                "optimized path declines linear-memory accesses under \
                 --safety-bounds mask (in-place AND is unsound on this path — \
                 see #377); falling back to direct selector"
                    .to_string(),
            ));
        }

        let mut arm_instrs = Vec::new();
        let mut vreg_to_arm: HashMap<u32, Reg> = HashMap::new();

        // For branch resolution: map IR instruction index -> ARM instruction index
        let mut ir_to_arm_idx: HashMap<usize, usize> = HashMap::new();
        // Track pending branches: (arm_instr_idx, target_ir_idx)
        let mut pending_branches: Vec<(usize, usize, bool)> = Vec::new();

        // Map local indices to ARM registers for params
        // AAPCS: first 4 params in R0-R3
        let param_regs = [Reg::R0, Reg::R1, Reg::R2, Reg::R3];

        // Reserved param registers: R0..R(min(num_params,4)). These hold incoming
        // AAPCS arguments that must NOT be clobbered by i64 op handlers — at least
        // until the user's WASM has done a `local.get` of each. Using Vec because
        // `Reg` does not derive Hash (matches `instruction_selector::alloc_consecutive_pair`).
        let mut param_reserved_regs: Vec<Reg> = param_regs[..num_params.min(4)].to_vec();

        // VCR-RA lever 3 base-CSE (#468, epic #242): if the function is a run of
        // constant-address memory accesses, reserve R11 as a persistent base
        // register (excluded from every allocator via `param_reserved_regs`),
        // materialize the linear-memory base into it ONCE at entry, and fold each
        // const address into the access immediate (`str V,[R11,#ADDR]`) — dropping
        // the per-access `movw/movt` base re-materialization (#468's complaint)
        // AND the now-dead address materialization (the pressure relief that keeps
        // the reserved base a net win). R11 is realloc-immune (outside the R0–R8
        // pool), so the single entry materialization survives every segment.
        // DEFAULT-ON (#242 feature loop, the SYNTH_SPILL_REALLOC-flip pattern):
        // base-CSE ships by default. Evidence basis for the flip: the planner
        // only activates on the narrow provably-profitable shape (every opcode
        // enumerated, ≥2 single-use const-address accesses folding into the
        // imm12 window — anything else declines the whole function), the
        // 72-fixture corpus sweep shrinks 2 fixtures / grows 0
        // (redundant_base_materialization 342→224 B, volatile_segment_543
        // 256→194 B), and the unicorn-vs-wasmtime execution differentials
        // (base_cse, volatile_segment_543, const_cse, flight_seam,
        // frame_slot_dce, spill_rung_581, control_step) re-ran green on the
        // new default bytes BEFORE the goldens were re-pinned
        // (base_cse_flip_468.rs). The optimized path is the ONLY caller of
        // `ir_to_arm`, so this never reaches the relocatable lowering (which
        // already pins the base in `fp`) — the frozen `--relocatable` anchors
        // are untouched by construction.
        // Escape hatch: `SYNTH_BASE_CSE=0` is the OPT-OUT — it restores the
        // pre-flip bytes (CI-gated by
        // `base_cse_escape_hatch_restores_old_bytes_468`). Any other value
        // (or unset) runs the planner.
        // #543 Phase 2: the planner receives the integrator-marked volatile
        // DMA ranges — an access inside a marked window is excluded from the
        // fold set (it keeps its verbatim per-access materialize-and-access
        // codegen), while accesses outside still fold.
        // #377: base-CSE is disabled while software bounds checks are active.
        // The folded arm replaces the dynamic-address materialization with a
        // direct `[R11,#imm]` access, so the per-access guard below (which
        // reads the address REGISTER) would have nothing to check against —
        // supporting a const-end compare is possible but not worth the second
        // code shape; safety mode trades the size win for uniform checking.
        let base_cse: Option<BaseCsePlan> = if self.bounds_check == BoundsCheckConfig::Software {
            None
        } else if !std::env::var("SYNTH_BASE_CSE").is_ok_and(|v| v == "0") {
            plan_base_cse(instructions, &self.volatile_segments)
        } else {
            None
        };
        if base_cse.is_some() {
            param_reserved_regs.push(BASE_CSE_REG);
        }

        // Track which ARM register currently holds each local variable
        // This avoids stack spills for simple cases
        let mut local_to_reg: HashMap<u32, Reg> = HashMap::new();
        // Registers available for locals (callee-saved)
        let local_regs = [Reg::R4, Reg::R5, Reg::R6, Reg::R7];
        // Track vregs that have been consumed and can be freed
        // This enables register reuse after values are no longer needed
        let mut dead_vregs: std::collections::HashSet<u32> = std::collections::HashSet::new();
        // Track vregs that correspond to local variables (shouldn't be marked dead after use)
        let mut local_vregs: std::collections::HashSet<u32> = std::collections::HashSet::new();

        // Track the last value-producing vreg (for function return value)
        let mut last_result_vreg: Option<u32> = None;
        // For i64 returns, also track the hi-half vreg so the epilogue can move
        // the pair into R0:R1 regardless of where regalloc placed it. Was previously
        // unnecessary because every i64 op pinned its result to R0:R1 — that's the
        // bug we're fixing here.
        let mut last_result_vreg_hi: Option<u32> = None;
        // For i64 ops whose IR Opcode only tracks a single `dest` vreg (Clz / Ctz /
        // Popcnt), the hi half lives in a register chosen at lowering time but has
        // no IR vreg pointing at it. Stash that physical reg directly so the
        // epilogue can still emit the correct (R0, R1) move.
        let mut last_result_vreg_hi_reg: Option<Reg> = None;
        // Track whether the last result is an i64 (return value occupies a pair).
        let mut is_i64_result = false;
        // WASM operand value stack - tracks vreg IDs for correct stack semantics
        // Used to restore last_result_vreg after br_if pops its condition
        let mut value_stack: Vec<u32> = Vec::new();

        // Register spilling support: when all temp registers are in use,
        // spill least-recently-used values to the stack frame
        let mut spilled_vregs: HashMap<u32, i32> = HashMap::new();
        let mut next_spill_offset: i32 = 4; // first spill at [SP, #4], etc.
        // Insertion order tracking for LRU eviction
        let mut vreg_alloc_order: Vec<u32> = Vec::new();

        // Known i64 constant values keyed by their `dest_lo` vreg id. Populated
        // when we lower `Opcode::I64Const`; consulted by i64 shift / mask
        // handlers to detect compile-time-constant operands and avoid emitting
        // the full 38-byte runtime shift sequence.
        //
        // Issue #94: when a u64-packed FFI return is split via `i64.shr_u 32`
        // followed by `i32.wrap_i64`, the hi32 field is already in the high
        // register of the i64 pair — no shift instructions are needed, just a
        // vreg rename plus a single `mov rd_hi, #0` for the (now-zero) hi half.
        let mut known_i64_consts: HashMap<u32, i64> = HashMap::new();

        // Helper to get ARM reg from virtual reg.
        // Also checks spill slots — if a vreg was spilled, returns R12 (IP scratch).
        // Callers should also call `reload_spill` to emit the actual load instruction.
        //
        // Returns `Err` if the vreg is neither mapped nor spilled. The original
        // behaviour here was a silent `Reg::R0` fallback, which produced
        // miscompilation: a downstream instruction reading the "unknown" vreg
        // would silently consume whatever R0 happens to hold (often a live
        // caller param or memset's dest pointer). Issue #93 was exactly this —
        // `wasm_to_ir` had no handler for `I64ExtendI32U`/`I64ExtendI32S`/
        // `I32WrapI64`, so the IR they should have produced never got mapped to
        // ARM regs, and downstream i64 shifts read R0 as their `rm_lo`/`rm_hi`,
        // destroying the loop counter on real silicon.
        //
        // PR #101 replaced the silent fallback with a hard `panic!` — strictly
        // better than a quiet miscompilation. This converts that panic into a
        // typed `Err`: still a loud, diagnostic "this shouldn't happen with
        // valid IR" signal (the issue-#93-class bug-finder), but it no longer
        // kills the process, so the optimized lowering path is panic-free and
        // the `wasm_ops_lower_or_error` fuzz harness can gate on it again.
        // History: PR #108 (47-site AAPCS audit) deferred the guard behind a
        // silent R0 fallback while one last v13 case in fib compilation was
        // tracked down. PR #109 fixed that case (WasmOp::Call had no wasm_to_ir
        // handler, falling through to Opcode::Nop). With every known wasm_to_ir
        // gap closed, the guard remains as a permanent defence against the
        // class — now as a recoverable `Err` rather than a panic.
        let get_arm_reg =
            |vreg: &OptReg, map: &HashMap<u32, Reg>, spills: &HashMap<u32, i32>| -> Result<Reg> {
                if let Some(&r) = map.get(&vreg.0) {
                    Ok(r)
                } else if spills.contains_key(&vreg.0) {
                    // Will be reloaded into R12 by reload_spill
                    Ok(Reg::R12)
                } else {
                    Err(Error::synthesis(format!(
                        "synth internal compiler error: vreg v{} has no assigned \
                     ARM register and no spill slot. This is a wasm_to_ir bug — \
                     likely a wasm op whose result is unmapped (see issue #93).",
                        vreg.0
                    )))
                }
            };

        // #496: the optimized path's last-resort scratch fallbacks below
        // (`alloc_i32_scratch` → R12, `alloc_i64_pair` → (R4,R5)) are UNSAFE under
        // real register pressure — R12/IP is the encoder's indexed-load base
        // scratch (#212), so a fold that exhausts R4-R8 and borrows R12 collides
        // with the address math of a later MemLoad (control_step: `lsl ip,r4,ip`
        // clobbered by base materialization → `add ip,ip,ip`). Rather than emit a
        // silent miscompile, we record that exhaustion happened and DECLINE the
        // whole function to the direct selector (which spills correctly) at the end
        // of the build. The Cell is shared by reference into both closures.
        let r12_exhausted = std::cell::Cell::new(false);

        // Allocate a CONSECUTIVE callee-saved register pair for an i64 destination.
        //
        // Searches `[(R4,R5), (R6,R7), (R8,R9), (R10,R11)]` for a pair where neither
        // register is currently:
        //   - holding a live vreg (`vreg_to_arm.values()`)
        //   - bound to a non-param local (`local_to_reg.values()`)
        //   - one of the AAPCS param registers we must preserve on entry
        //     (`param_reserved_regs`)
        //
        // Falls back to `(R4, R5)` if no pair is free — preserves prior behaviour
        // for very-pressured functions, but at least keeps params intact in the
        // common case. Per `instruction_selector::alloc_consecutive_pair`, callers
        // who hit the fallback in real workloads will need spill support; that's
        // out of scope for this fix.
        let alloc_i64_pair = |vreg_to_arm: &HashMap<u32, Reg>,
                              local_to_reg: &HashMap<u32, Reg>,
                              param_reserved_regs: &[Reg]|
         -> (Reg, Reg) {
            // Candidate list shared with the #587 pair-spill pre-step
            // (`SPILL_I64_PAIR_CANDIDATES`): the evictor frees pairs from
            // EXACTLY the set this allocator searches, so the two can never
            // drift (the estimator↔encoder mirror-pinning lesson, #511).
            let is_in_use = |r: Reg| -> bool {
                vreg_to_arm.values().any(|&v| v == r)
                    || local_to_reg.values().any(|&v| v == r)
                    || param_reserved_regs.contains(&r)
            };
            for &(lo, hi) in &SPILL_I64_PAIR_CANDIDATES {
                if !is_in_use(lo) && !is_in_use(hi) {
                    return (lo, hi);
                }
            }
            // #496: every pair is occupied — the (R4,R5) fallback would alias a
            // live value. Flag exhaustion so the build declines to the direct
            // selector; still return a pair so the rest of the build completes
            // (its bytes are discarded). This path is unverified by a fixture
            // (empirically never triggered for our workloads), but flagging it is
            // free insurance against the same class as the i32 case below.
            r12_exhausted.set(true);
            (Reg::R4, Reg::R5)
        };

        // Allocate a SINGLE callee-saved register for an i32 destination.
        //
        // Searches `[R4, R5, R6, R7, R8]` for a register not currently held
        // by a live vreg, bound to a non-param local, or reserved as an
        // AAPCS param. The extra_avoid list is honoured for transient
        // operand-region exclusions (e.g. addresses-of operands that must
        // outlive the destination allocation).
        //
        // Falls back to R12 (IP, the universal scratch) if every callee-
        // saved register is taken — matches the prior pressure-relief
        // behaviour. R12 is intentionally NOT in the search list because
        // it's used as a transient by MemLoad/MemStore for the base+offset
        // pointer math, and would be clobbered before the destination is
        // read.
        let alloc_i32_scratch = |vreg_to_arm: &HashMap<u32, Reg>,
                                 local_to_reg: &HashMap<u32, Reg>,
                                 param_reserved_regs: &[Reg],
                                 extra_avoid: &[Reg]|
         -> Reg {
            const CANDIDATES: &[Reg] = &[Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];
            let is_in_use = |r: Reg| -> bool {
                vreg_to_arm.values().any(|&v| v == r)
                    || local_to_reg.values().any(|&v| v == r)
                    || param_reserved_regs.contains(&r)
                    || extra_avoid.contains(&r)
            };
            for &r in CANDIDATES {
                if !is_in_use(r) {
                    return r;
                }
            }
            // #496: every callee-saved scratch is live. Borrowing R12/IP here is
            // a miscompile under real pressure — IP is the encoder's indexed-load
            // base scratch, so the "dest written before R12 used" assumption fails
            // when two folds both land on R12 (collide) or an R12 value survives
            // across a later MemLoad's base math. Flag exhaustion so the build
            // declines to the direct selector (which spills); still return R12 so
            // the remaining build completes (those bytes are discarded).
            r12_exhausted.set(true);
            Reg::R12
        };

        // Emit a reload instruction if the vreg was spilled to stack.
        // Must be called before the instruction that uses the register.
        let reload_spill = |vreg: &OptReg, spills: &HashMap<u32, i32>, instrs: &mut Vec<ArmOp>| {
            if let Some(&offset) = spills.get(&vreg.0) {
                instrs.push(ArmOp::Ldr {
                    rd: Reg::R12,
                    addr: crate::rules::MemAddr::imm(Reg::SP, offset),
                });
            }
        };

        // Pre-pass for issue #94: find i64 constants whose ONLY use is as the
        // shift amount of a shr_u/shr_s where the value is 32, or as the mask
        // operand of an `i64.and 0xFFFFFFFF` — those constants are folded away
        // by the shift / and handlers below, so the MOVs that load them into
        // registers are dead. This skip set is consulted in the I64Const
        // handler to bypass emitting those MOVs (saves ~4 bytes per fold).
        let mut skip_const_dest_lo: std::collections::HashSet<u32> =
            std::collections::HashSet::new();
        {
            // First, collect simple constant values produced by I64Const (we
            // only need their `value` and `dest_lo` here — the rest is
            // determined by the consumer instruction below).
            let mut const_values: HashMap<u32, i64> = HashMap::new();
            // Count uses of each const dest_lo across the IR. A const is
            // skip-eligible only if it has exactly one use and that use is the
            // folded shift / and pattern.
            let mut use_count: HashMap<u32, u32> = HashMap::new();
            for inst in instructions {
                if let Opcode::I64Const { dest_lo, value, .. } = &inst.opcode {
                    const_values.insert(dest_lo.0, *value);
                }
                let mut bump = |v: u32| {
                    *use_count.entry(v).or_insert(0) += 1;
                };
                match &inst.opcode {
                    Opcode::I64Add {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Sub {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Or {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Xor {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Mul {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64DivS {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64DivU {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64RemS {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64RemU {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Shl {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64ShrU {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64ShrS {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64And {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Eq {
                        src1_lo, src2_lo, ..
                    }
                    | Opcode::I64Ne {
                        src1_lo, src2_lo, ..
                    } => {
                        bump(src1_lo.0);
                        bump(src2_lo.0);
                    }
                    _ => {}
                }
            }
            // Now mark constants whose only use is the folded pattern.
            for inst in instructions {
                match &inst.opcode {
                    Opcode::I64ShrU { src2_lo, .. } | Opcode::I64ShrS { src2_lo, .. } => {
                        if use_count.get(&src2_lo.0).copied() == Some(1)
                            && let Some(v) = const_values.get(&src2_lo.0)
                            && (*v as u64) & 0x3F == 32
                        {
                            skip_const_dest_lo.insert(src2_lo.0);
                        }
                    }
                    Opcode::I64And { src2_lo, .. } => {
                        if use_count.get(&src2_lo.0).copied() == Some(1)
                            && let Some(v) = const_values.get(&src2_lo.0)
                            && (*v as u64) == 0xFFFF_FFFF
                        {
                            skip_const_dest_lo.insert(src2_lo.0);
                        }
                    }
                    _ => {}
                }
            }
        }

        // First pass: map Load instructions (local.get) to ARM registers
        for inst in instructions {
            if let Opcode::Load { dest, addr } = &inst.opcode {
                // If this is loading a function parameter (local.get N where N < num_params)
                if (*addr as usize) < num_params && (*addr as usize) < 4 {
                    // Map this virtual register to the ARM register holding the param
                    vreg_to_arm.insert(dest.0, param_regs[*addr as usize]);
                } else {
                    // For non-param locals, allocate a temp register
                    // Simple strategy: use R4+ for non-param locals
                    let temp_regs = [Reg::R4, Reg::R5, Reg::R6, Reg::R7];
                    let idx = vreg_to_arm.len().saturating_sub(num_params);
                    if idx < temp_regs.len() {
                        vreg_to_arm.insert(dest.0, temp_regs[idx]);
                    }
                }
            }
        }

        // VCR-RA lever 3 base-CSE: materialize the linear-memory base into the
        // reserved R11 ONCE, before any access. Placed before the second pass so
        // it precedes every folded `[R11,#ADDR]` and so `ir_to_arm_idx` (recorded
        // during the loop) accounts for these two leading instructions. R11 is
        // realloc-immune, so this single def reaches every later use unremapped.
        if base_cse.is_some() {
            arm_instrs.push(ArmOp::Movw {
                rd: BASE_CSE_REG,
                imm16: (self.linmem_base & 0xFFFF) as u16,
            });
            arm_instrs.push(ArmOp::Movt {
                rd: BASE_CSE_REG,
                imm16: ((self.linmem_base >> 16) & 0xFFFF) as u16,
            });
        }

        // VCR-RA const-CSE (#242): the bridge-level INLINE aliasing that used
        // to live here (alias a repeated const's vreg to the register already
        // holding the value, under `SYNTH_CONST_CSE`) is RETIRED. Inline
        // aliasing made two live vregs share one physical register, breaking
        // the spill model's vreg↔reg bijection — the recorded alias-eviction
        // hazard that blocked the default-on flip (see the #592 PR body and
        // `const_cse_reduction_242.rs`). Const materialization now always
        // falls through to the normal allocate-and-emit below; the flag gates
        // ONLY the post-hoc, liveness-proven `liveness::apply_const_cse`
        // passes wired in `arm_backend.rs` (PR1 #519 cross-register fold +
        // PR2 #562 extending-alias hoist), which are removal+retarget on
        // already-register-assigned code and cannot alias two live vregs.

        // VCR-RA-001 allocation-time spill-on-exhaustion (#242, closes #496 for
        // straight-line i32 functions; #587 extends it to i64 register PAIRS).
        // Opt-in (`SYNTH_SPILL_ON_EXHAUST=1`); off ⇒ byte-identical (no new
        // state is read, the pre-step below is skipped, and exhaustion keeps
        // declining to the direct selector). Active only when EVERY opcode is
        // modeled (no control flow, no calls, no non-param locals, only the
        // i64 subset whose lowering the pair model covers — see
        // `spill_on_exhaust_supported` / `spill_on_exhaust_scope_ok` for the
        // honest scope); otherwise the #496 decline stands for the whole
        // function.
        //
        // #587: `pair_partner` maps each i64 half vreg to (partner, is_lo),
        // built from the IR pair DEFS. Pairs are evicted and reloaded as
        // coherent units into 8-byte-aligned slot pairs (the #325 direct-path
        // convention); a half is never spilled alone by the pre-step. If the
        // map is ambiguous (a vreg re-used across two pairs), the lever
        // declines for the whole function — never wrong code.
        let spill_pairs: Option<HashMap<u32, (u32, bool)>> = if self.spill_on_exhaust_enabled()
            && spill_on_exhaust_scope_ok(instructions, num_params)
        {
            spill_pair_partner_map(instructions)
        } else {
            None
        };
        let spill_on_exhaust = spill_pairs.is_some();
        let pair_partner: HashMap<u32, (u32, bool)> = spill_pairs.unwrap_or_default();
        // VCR-VER-001 post-exhaustion quality (#242, the PR #659 verdict):
        // single-def `Const` values, consulted by the DivS/DivU/RemS/RemU
        // handlers to elide trap guards a constant divisor makes unreachable
        // (divide-by-zero when c ≠ 0; the DivS INT_MIN/-1 overflow when
        // c ∉ {0, -1}) — the direct selector's #209 Opt-1a guard elision,
        // which the optimized path lacked and which is what made a spilled
        // `signed_div_const` compile WORSE than its direct lowering (34→76 B).
        // Gated on `spill_on_exhaust` twice over: (a) flag off ⇒ empty map ⇒
        // byte-identical, and (b) the scope gate has already proven every
        // opcode is in the modeled i32 subset, so `spill_i32_def` enumerates
        // EVERY def and a multi-defined vreg can never smuggle in a stale
        // constant (only the first def of a vreg may register a value).
        // VCR-VER-001 (#242): tracks whether flag-on-only machinery actually
        // shaped this function's bytes (pre-step reinstate/evict) and how many
        // divisor guards were elided — the wrapper's scoping facts.
        let mut exhaust_acted = false;
        let mut guards_elided = 0usize;
        let exhaust_const_vals: HashMap<u32, i32> = if spill_on_exhaust && elide_div_guards {
            let mut vals = HashMap::new();
            let mut defined = std::collections::HashSet::new();
            let mut total = true; // every op's defs enumerable, or no map at all
            for inst in instructions.iter() {
                let Some(defs) = spill_exhaust_defs(&inst.opcode) else {
                    total = false;
                    break;
                };
                for d in defs {
                    if !defined.insert(d) {
                        vals.remove(&d); // redefined: never trust the value
                    } else if let Opcode::Const { dest, value } = &inst.opcode
                        && dest.0 == d
                    {
                        vals.insert(d, *value);
                    }
                }
            }
            if total { vals } else { HashMap::new() }
        } else {
            HashMap::new()
        };
        // NOTE (VCR-VER-001, measured dead end): widening the reload pool
        // with caller-saved R2/R3 was tried and REVERTED — reload targets in
        // R2/R3 consume exactly the exit-dead rename targets the post-hoc
        // spill-rechoice pass (`apply_spill_realloc_post_exhaust`) needs, and
        // eviction COUNT is dest-driven (R4-R8 only), so the net effect was
        // strictly worse (spill_rung_581 +8.8% → +14.7% on the cycle proxy).
        // The genuine allocation-time fix is dest allocation over the full
        // R0-R8 pool — `alloc_i32_scratch`'s fixed R4-R8 pool is the
        // residual named in scripts/repro/vcr_ver_001_gate.md.
        // Belady next-use table: for each vreg, the (sorted) instruction
        // positions where it is read. "Farthest next use" picks the victim.
        // i64 sources contribute BOTH halves (#587).
        let use_positions: HashMap<u32, Vec<usize>> = if spill_on_exhaust {
            let mut m: HashMap<u32, Vec<usize>> = HashMap::new();
            for (pos, i) in instructions.iter().enumerate() {
                for v in spill_i32_sources(&i.opcode)
                    .into_iter()
                    .chain(spill_i64_half_sources(&i.opcode))
                {
                    m.entry(v).or_default().push(pos);
                }
            }
            m
        } else {
            HashMap::new()
        };
        // Vregs premapped by the first pass (param registers). Never victims:
        // their registers are outside the pool and their liveness is not
        // tracked by `dead_vregs`.
        let premapped_vregs: std::collections::HashSet<u32> = if spill_on_exhaust {
            vreg_to_arm.keys().copied().collect()
        } else {
            std::collections::HashSet::new()
        };

        // Second pass: generate ARM instructions
        for (spill_idx, inst) in instructions.iter().enumerate() {
            // VCR-RA-001 spill pre-step (#242, #496): with the flag on and the
            // whole function in the modeled subset, make sure the handler below
            // never hits pool exhaustion:
            //  (a) reinstate spilled SOURCES — reload each into a pool register
            //      (evicting the farthest-next-use victim if the pool is full)
            //      and put it back in `vreg_to_arm`, so `get_arm_reg` finds a
            //      real register (never the flag-off R12 spill placeholder,
            //      which cannot carry two operands and collides with the
            //      encoder's IP scratch — the #496 miscompile class);
            //  (b) free a DEST register — if the handler will allocate a fresh
            //      scratch and the pool is full, evict one victim now so
            //      `alloc_i32_scratch` succeeds instead of flagging exhaustion.
            // If eviction finds no victim (everything pinned), fall through:
            // the handler's exhaustion fallback fires and the function declines
            // to the direct selector exactly as with the flag off — the lever
            // degrades to the status quo, never to a miscompile.
            if spill_on_exhaust {
                let mut srcs = spill_i32_sources(&inst.opcode);
                srcs.extend(spill_i64_half_sources(&inst.opcode));
                // Registers the current instruction's operands occupy (or are
                // being reloaded into): never evict these.
                let mut operand_regs: Vec<Reg> = srcs
                    .iter()
                    .filter_map(|v| vreg_to_arm.get(v).copied())
                    .collect();
                for v in &srcs {
                    if !spilled_vregs.contains_key(v) {
                        continue;
                    }
                    // #587: an i64 half whose partner is also spilled reloads
                    // as a COHERENT pair into a legal even pair (lo→even reg,
                    // hi→odd reg), from the 8-byte-aligned slot pair the pair
                    // evictor wrote. A half spilled ALONE (only possible via
                    // the Const handler's own flag-off eviction of a
                    // to-be-extended i32) takes the single path below — its
                    // partner is untouched, and i64 lowerings read lo/hi
                    // registers independently (adjacency is a DEST-only
                    // constraint).
                    if let Some(&(partner, is_lo)) = pair_partner.get(v)
                        && spilled_vregs.contains_key(&partner)
                    {
                        let (v_lo, v_hi) = if is_lo { (*v, partner) } else { (partner, *v) };
                        let pair = find_free_spill_pair(
                            &vreg_to_arm,
                            &local_to_reg,
                            &param_reserved_regs,
                            &operand_regs,
                        )
                        .or_else(|| {
                            spill_evict_pair_farthest(
                                spill_idx,
                                &operand_regs,
                                &use_positions,
                                &local_vregs,
                                &premapped_vregs,
                                &pair_partner,
                                &local_to_reg,
                                &param_reserved_regs,
                                &mut vreg_to_arm,
                                &mut spilled_vregs,
                                &mut next_spill_offset,
                                &mut arm_instrs,
                            )
                        });
                        let Some((p_lo, p_hi)) = pair else {
                            // No sound eviction — decline (#496), exactly as
                            // with the flag off. Never wrong code.
                            r12_exhausted.set(true);
                            break;
                        };
                        let slot_lo = spilled_vregs
                            .remove(&v_lo)
                            .expect("pair halves spill together (#587 invariant)");
                        let slot_hi = spilled_vregs
                            .remove(&v_hi)
                            .expect("pair halves spill together (#587 invariant)");
                        arm_instrs.push(ArmOp::Ldr {
                            rd: p_lo,
                            addr: crate::rules::MemAddr::imm(Reg::SP, slot_lo),
                        });
                        arm_instrs.push(ArmOp::Ldr {
                            rd: p_hi,
                            addr: crate::rules::MemAddr::imm(Reg::SP, slot_hi),
                        });
                        vreg_to_arm.insert(v_lo, p_lo);
                        vreg_to_arm.insert(v_hi, p_hi);
                        operand_regs.push(p_lo);
                        operand_regs.push(p_hi);
                        exhaust_acted = true;
                        continue;
                    }
                    // A free pool register, by `alloc_i32_scratch`'s in-use
                    // rule (every mapped vreg counts, dead or not).
                    let free = SPILL_ON_EXHAUST_POOL.iter().copied().find(|r| {
                        !vreg_to_arm.values().any(|u| u == r)
                            && !local_to_reg.values().any(|u| u == r)
                            && !param_reserved_regs.contains(r)
                            && !operand_regs.contains(r)
                    });
                    let rd = free
                        .or_else(|| {
                            spill_evict_farthest(
                                &SPILL_ON_EXHAUST_POOL,
                                spill_idx,
                                &operand_regs,
                                &use_positions,
                                &local_vregs,
                                &premapped_vregs,
                                &pair_partner,
                                &local_to_reg,
                                &param_reserved_regs,
                                &mut vreg_to_arm,
                                &mut spilled_vregs,
                                &mut next_spill_offset,
                                &mut arm_instrs,
                            )
                        })
                        .or_else(|| {
                            // #587: no single victim (the pool may be wall-to-
                            // wall i64 halves) — evicting a whole pair frees
                            // two registers; reload into its lo half.
                            spill_evict_pair_farthest(
                                spill_idx,
                                &operand_regs,
                                &use_positions,
                                &local_vregs,
                                &premapped_vregs,
                                &pair_partner,
                                &local_to_reg,
                                &param_reserved_regs,
                                &mut vreg_to_arm,
                                &mut spilled_vregs,
                                &mut next_spill_offset,
                                &mut arm_instrs,
                            )
                            .map(|(lo, _)| lo)
                        });
                    let Some(rd) = rd else {
                        // Nothing evictable — leave the vreg spilled; the
                        // handler's R12 placeholder path flags exhaustion and
                        // the function declines (#496) at the end of the build.
                        r12_exhausted.set(true);
                        break;
                    };
                    let slot = spilled_vregs.remove(v).expect("checked contains_key above");
                    arm_instrs.push(ArmOp::Ldr {
                        rd,
                        addr: crate::rules::MemAddr::imm(Reg::SP, slot),
                    });
                    vreg_to_arm.insert(*v, rd);
                    operand_regs.push(rd);
                    exhaust_acted = true;
                }
                if let Some(d) = spill_i32_scratch_dest(&inst.opcode)
                    && !vreg_to_arm.contains_key(&d)
                {
                    let pool_full = !SPILL_ON_EXHAUST_POOL.iter().any(|r| {
                        !vreg_to_arm.values().any(|u| u == r)
                            && !local_to_reg.values().any(|u| u == r)
                            && !param_reserved_regs.contains(r)
                            && !operand_regs.contains(r)
                    });
                    if pool_full {
                        let freed = spill_evict_farthest(
                            &SPILL_ON_EXHAUST_POOL,
                            spill_idx,
                            &operand_regs,
                            &use_positions,
                            &local_vregs,
                            &premapped_vregs,
                            &pair_partner,
                            &local_to_reg,
                            &param_reserved_regs,
                            &mut vreg_to_arm,
                            &mut spilled_vregs,
                            &mut next_spill_offset,
                            &mut arm_instrs,
                        )
                        .or_else(|| {
                            // #587: free a whole pair when no single victim
                            // exists (pool saturated by i64 halves).
                            spill_evict_pair_farthest(
                                spill_idx,
                                &operand_regs,
                                &use_positions,
                                &local_vregs,
                                &premapped_vregs,
                                &pair_partner,
                                &local_to_reg,
                                &param_reserved_regs,
                                &mut vreg_to_arm,
                                &mut spilled_vregs,
                                &mut next_spill_offset,
                                &mut arm_instrs,
                            )
                            .map(|(lo, _)| lo)
                        });
                        // For most handlers a None is fine: `alloc_i32_scratch`
                        // flags exhaustion itself and the function declines as
                        // with the flag off. `Const` is the exception — its own
                        // allocator falls back to R9/R10/R11/R3, which is only
                        // sound while exhausted functions decline; with i64
                        // pairs legitimately parked in R9-R11 (#587) that
                        // fallback could clobber a live pair half, so decline
                        // loudly instead. Gated on pair presence so flag-on
                        // i32-only behavior is unchanged.
                        if freed.is_none()
                            && !pair_partner.is_empty()
                            && matches!(&inst.opcode, Opcode::Const { .. })
                        {
                            r12_exhausted.set(true);
                        }
                        exhaust_acted |= freed.is_some();
                    }
                }
                // #587: pre-free a legal even pair for handlers that call
                // `alloc_i64_pair` for their destination (i64 producers, and
                // the i64 comparisons whose i32 result binds the lo half of a
                // freshly allocated pair). If eviction finds no victim, fall
                // through: `alloc_i64_pair`'s #496 fallback flags exhaustion
                // and the function declines — the lever degrades to the
                // status quo, never to a miscompile.
                let needs_pair = match &inst.opcode {
                    // A skip-folded i64 const (#94) emits nothing and
                    // allocates nothing.
                    Opcode::I64Const { dest_lo, .. } => !skip_const_dest_lo.contains(&dest_lo.0),
                    op => spill_needs_pair_alloc(op),
                };
                if needs_pair
                    && find_free_spill_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[])
                        .is_none()
                {
                    let freed_pair = spill_evict_pair_farthest(
                        spill_idx,
                        &operand_regs,
                        &use_positions,
                        &local_vregs,
                        &premapped_vregs,
                        &pair_partner,
                        &local_to_reg,
                        &param_reserved_regs,
                        &mut vreg_to_arm,
                        &mut spilled_vregs,
                        &mut next_spill_offset,
                        &mut arm_instrs,
                    );
                    exhaust_acted |= freed_pair.is_some();
                }
            }

            match &inst.opcode {
                Opcode::Nop => continue,

                // Load for params: no instruction needed, value is already in register
                Opcode::Load { dest, addr } if (*addr as usize) < num_params => {
                    // Value is already in param register, just record the mapping
                    if (*addr as usize) < 4 {
                        vreg_to_arm.insert(dest.0, param_regs[*addr as usize]);
                    }
                    // Mark as local vreg (shouldn't be freed after use)
                    local_vregs.insert(dest.0);
                    // Track as potential return value
                    last_result_vreg = Some(dest.0);
                }

                // Load for non-param locals: use tracked register or allocate one
                Opcode::Load { dest, addr } => {
                    // Check if we have this local in a register
                    if let Some(&src_reg) = local_to_reg.get(addr) {
                        // Local is already in a register, just track the mapping
                        vreg_to_arm.insert(dest.0, src_reg);
                    } else {
                        // Allocate a register for this local
                        let local_idx = (*addr as usize).saturating_sub(num_params);
                        let rd = if local_idx < local_regs.len() {
                            local_regs[local_idx]
                        } else {
                            Reg::R4
                        };
                        vreg_to_arm.insert(dest.0, rd);
                        local_to_reg.insert(*addr, rd);
                    }
                    // Mark as local vreg (shouldn't be freed after use)
                    local_vregs.insert(dest.0);
                    // Track as potential return value
                    last_result_vreg = Some(dest.0);
                }

                // Store: write to local variable
                Opcode::Store { src, addr } => {
                    let rs = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    // Track which register holds this local's value
                    // Special case: synthetic local 255 is used for preserving conditions
                    // across nested selects - use R11 which is rarely used elsewhere
                    if *addr == 255 {
                        let local_reg = Reg::R11;
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov {
                                rd: local_reg,
                                op2: Operand2::Reg(rs),
                            });
                        }
                        local_to_reg.insert(*addr, local_reg);
                    } else if (*addr as usize) >= num_params {
                        // For non-param locals, we keep the value in a dedicated register
                        let local_idx = (*addr as usize).saturating_sub(num_params);
                        let local_reg = if local_idx < local_regs.len() {
                            local_regs[local_idx]
                        } else {
                            Reg::R4
                        };
                        // Move value to the local's register if not already there
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov {
                                rd: local_reg,
                                op2: Operand2::Reg(rs),
                            });
                        }
                        local_to_reg.insert(*addr, local_reg);
                    }
                    // For param locals (addr < num_params), value stays in param register
                    // Mark source vreg as dead (unless it's a local vreg)
                    if !local_vregs.contains(&src.0) {
                        dead_vregs.insert(src.0);
                    }
                }

                // Constant: mov immediate to register
                Opcode::Const { dest, value } => {
                    // VCR-RA lever 3 base-CSE: this const is a folded address — its
                    // ONLY use is a `[R11,#ADDR]` access (planner-verified single
                    // use), so do not materialize it at all. Dropping it is the
                    // register-pressure relief that makes the reserved base a win.
                    if let Some(plan) = &base_cse
                        && plan.skip_const.contains(&dest.0)
                    {
                        continue;
                    }
                    // NOTE (#242): the inline const-CSE aliasing that used to
                    // short-circuit here (alias `dest` to a register already
                    // holding the value) is RETIRED — it made two live vregs
                    // share one physical register, breaking the spill model's
                    // vreg↔reg bijection (the alias-eviction hazard). Every
                    // const now allocates and materializes normally; redundant
                    // materializations are recovered post-hoc by the
                    // liveness-proven `liveness::apply_const_cse` passes.
                    // Allocate a register for this constant
                    let rd = if let Some(&r) = vreg_to_arm.get(&dest.0) {
                        r
                    } else {
                        // Find next available temp register
                        // Exclude live vregs (not dead) and local_to_reg to avoid clobbering.
                        // Base-CSE reserves R11 (in `param_reserved_regs`); fold it in
                        // so the const pool never hands out the live base register.
                        let used: Vec<_> = vreg_to_arm
                            .iter()
                            .filter(|(k, _)| !dead_vregs.contains(k))
                            .map(|(_, v)| *v)
                            .chain(local_to_reg.values().copied())
                            .chain(param_reserved_regs.iter().copied())
                            .collect();
                        // Expanded temp register pool: R4-R11 (callee-saved) plus R3
                        // Note: R0-R2 are reserved for params/return, R12 is IP, R13 is SP, R14 is LR, R15 is PC
                        let temp_regs = [
                            Reg::R4,
                            Reg::R5,
                            Reg::R6,
                            Reg::R7,
                            Reg::R8,
                            Reg::R9,
                            Reg::R10,
                            Reg::R11,
                            Reg::R3,
                        ];
                        let rd = match temp_regs.iter().find(|r| !used.contains(r)).copied() {
                            Some(r) => r,
                            None => {
                                // All registers exhausted — spill the oldest live
                                // non-local vreg to the stack to free a register.
                                // Find oldest live vreg by allocation order
                                let evict_vreg = vreg_alloc_order
                                    .iter()
                                    .find(|v| {
                                        !dead_vregs.contains(v)
                                            && !local_vregs.contains(v)
                                            && vreg_to_arm.contains_key(v)
                                    })
                                    .copied();
                                if let Some(victim) = evict_vreg {
                                    let victim_reg = vreg_to_arm[&victim];
                                    // Spill: STR victim_reg, [SP, #offset]
                                    let offset = next_spill_offset;
                                    next_spill_offset += 4;
                                    arm_instrs.push(ArmOp::Str {
                                        rd: victim_reg,
                                        addr: crate::rules::MemAddr::imm(Reg::SP, offset),
                                    });
                                    spilled_vregs.insert(victim, offset);
                                    vreg_to_arm.remove(&victim);
                                    victim_reg
                                } else {
                                    // Last resort: reuse R3 (scratch)
                                    Reg::R3
                                }
                            }
                        };
                        vreg_to_arm.insert(dest.0, rd);
                        vreg_alloc_order.push(dest.0);
                        rd
                    };
                    // For 32-bit values outside 16-bit range, use MOVW + MOVT
                    // ARM Thumb MOVW only handles 0-65535, so -1 (0xFFFFFFFF) needs both
                    let val_u32 = *value as u32;
                    if val_u32 > 0xFFFF {
                        // Need MOVW (lower 16) + MOVT (upper 16) for full 32-bit value
                        let lo = (val_u32 & 0xFFFF) as u16;
                        let hi = ((val_u32 >> 16) & 0xFFFF) as u16;
                        arm_instrs.push(ArmOp::Movw { rd, imm16: lo });
                        arm_instrs.push(ArmOp::Movt { rd, imm16: hi });
                    } else {
                        arm_instrs.push(ArmOp::Mov {
                            rd,
                            op2: Operand2::Imm(*value),
                        });
                    }
                }

                // Arithmetic operations
                //
                // Pre-fix these hardcoded `rd = Reg::R3`, clobbering the 4th
                // AAPCS argument on every i32 arith in 4-param functions.
                // Use `alloc_i32_scratch` so the destination is picked from
                // the callee-saved bank; sources are added to `extra_avoid`
                // so a 3-operand op doesn't pick its own input as dest while
                // it's still live in `vreg_to_arm`.
                Opcode::Add { dest, src1, src2 } => {
                    reload_spill(src1, &spilled_vregs, &mut arm_instrs);
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    reload_spill(src2, &spilled_vregs, &mut arm_instrs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Add {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                    // Mark source vregs as dead (unless they're local vregs)
                    if !local_vregs.contains(&src1.0) {
                        dead_vregs.insert(src1.0);
                    }
                    if !local_vregs.contains(&src2.0) {
                        dead_vregs.insert(src2.0);
                    }
                }

                Opcode::Sub { dest, src1, src2 } => {
                    reload_spill(src1, &spilled_vregs, &mut arm_instrs);
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    reload_spill(src2, &spilled_vregs, &mut arm_instrs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sub {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                    if !local_vregs.contains(&src1.0) {
                        dead_vregs.insert(src1.0);
                    }
                    if !local_vregs.contains(&src2.0) {
                        dead_vregs.insert(src2.0);
                    }
                }

                Opcode::Mul { dest, src1, src2 } => {
                    reload_spill(src1, &spilled_vregs, &mut arm_instrs);
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    reload_spill(src2, &spilled_vregs, &mut arm_instrs);
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Mul { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                    if !local_vregs.contains(&src1.0) {
                        dead_vregs.insert(src1.0);
                    }
                    if !local_vregs.contains(&src2.0) {
                        dead_vregs.insert(src2.0);
                    }
                }

                Opcode::DivS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // VCR-VER-001 (#242): a single-def constant divisor makes
                    // the trap conditions statically decidable — elide the
                    // guards a nonzero (and, for overflow, non-minus-one)
                    // constant can never fire (the direct selector's #209
                    // Opt-1a elision; empty map ⇒ both guards stay, flag-off
                    // byte-identical).
                    let divisor = exhaust_const_vals.get(&src2.0).copied();
                    let elide_zero = matches!(divisor, Some(c) if c != 0);
                    let elide_ovf = matches!(divisor, Some(c) if c != 0 && c != -1);

                    // Trap check 1: divide by zero
                    if elide_zero {
                        guards_elided += 1;
                    } else {
                        arm_instrs.push(ArmOp::Cmp {
                            rn: rm,
                            op2: Operand2::Imm(0),
                        });
                        arm_instrs.push(ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        });
                        arm_instrs.push(ArmOp::Udf { imm: 0 });
                    }

                    // Trap check 2: signed overflow (INT_MIN / -1)
                    if elide_ovf {
                        guards_elided += 1;
                    }
                    if !elide_ovf {
                        // Load INT_MIN (0x80000000) into R12
                        arm_instrs.push(ArmOp::Movw {
                            rd: Reg::R12,
                            imm16: 0,
                        });
                        arm_instrs.push(ArmOp::Movt {
                            rd: Reg::R12,
                            imm16: 0x8000,
                        });
                        // CMP dividend, INT_MIN
                        arm_instrs.push(ArmOp::Cmp {
                            rn,
                            op2: Operand2::Reg(Reg::R12),
                        });
                        // BNE.N +3 (skip overflow check if dividend != INT_MIN)
                        // Skip 8 bytes: CMN.W(4) + BNE(2) + UDF(2)
                        // Branch target = PC + (imm8 << 1) = B+4 + 6 = B+10 (SDIV)
                        arm_instrs.push(ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 3,
                        });
                        // CMN divisor, #1 (check if divisor == -1: -1 + 1 = 0 sets Z flag)
                        // CMN.W is 4 bytes
                        arm_instrs.push(ArmOp::Cmn {
                            rn: rm,
                            op2: Operand2::Imm(1),
                        });
                        // BNE.N +0 (skip UDF if divisor != -1)
                        arm_instrs.push(ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        });
                        // UDF #1 (trap on overflow)
                        arm_instrs.push(ArmOp::Udf { imm: 1 });
                    }

                    arm_instrs.push(ArmOp::Sdiv { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::DivU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero. VCR-VER-001 (#242): elided
                    // for a single-def nonzero constant divisor (see DivS).
                    if matches!(exhaust_const_vals.get(&src2.0), Some(c) if *c != 0) {
                        guards_elided += 1;
                    } else {
                        arm_instrs.push(ArmOp::Cmp {
                            rn: rm,
                            op2: Operand2::Imm(0),
                        });
                        arm_instrs.push(ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        });
                        arm_instrs.push(ArmOp::Udf { imm: 0 });
                    }

                    arm_instrs.push(ArmOp::Udiv { rd, rn, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Remainder: rd = rn - (rn / rm) * rm
                Opcode::RemS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero (rem_s doesn't trap on INT_MIN % -1).
                    // VCR-VER-001 (#242): elided for a single-def nonzero
                    // constant divisor (see DivS).
                    if matches!(exhaust_const_vals.get(&src2.0), Some(c) if *c != 0) {
                        guards_elided += 1;
                    } else {
                        arm_instrs.push(ArmOp::Cmp {
                            rn: rm,
                            op2: Operand2::Imm(0),
                        });
                        arm_instrs.push(ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        });
                        arm_instrs.push(ArmOp::Udf { imm: 0 });
                    }

                    // Use MLS: rd = ra - rn * rm, where ra = dividend, result of div in temp
                    arm_instrs.push(ArmOp::Sdiv {
                        rd: Reg::R12,
                        rn,
                        rm,
                    }); // R12 = rn / rm
                    arm_instrs.push(ArmOp::Mls {
                        rd,
                        rn: Reg::R12,
                        rm,
                        ra: rn,
                    }); // rd = rn - R12 * rm
                    last_result_vreg = Some(dest.0);
                }

                Opcode::RemU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // Trap check: divide by zero. VCR-VER-001 (#242): elided
                    // for a single-def nonzero constant divisor (see DivS).
                    if matches!(exhaust_const_vals.get(&src2.0), Some(c) if *c != 0) {
                        guards_elided += 1;
                    } else {
                        arm_instrs.push(ArmOp::Cmp {
                            rn: rm,
                            op2: Operand2::Imm(0),
                        });
                        arm_instrs.push(ArmOp::BCondOffset {
                            cond: Condition::NE,
                            offset: 0,
                        });
                        arm_instrs.push(ArmOp::Udf { imm: 0 });
                    }

                    arm_instrs.push(ArmOp::Udiv {
                        rd: Reg::R12,
                        rn,
                        rm,
                    });
                    arm_instrs.push(ArmOp::Mls {
                        rd,
                        rn: Reg::R12,
                        rm,
                        ra: rn,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Bitwise operations
                Opcode::And { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Or { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Orr {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Xor { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Eor {
                        rd,
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Shifts - WASM spec: shift amount masked to 5 bits (& 31)
                // ARM LSL/LSR/ASR by register use low byte, so shift >= 32
                // produces 0 (not wrapping). We must mask first.
                Opcode::Shl { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    // Mask shift amount: R12 = rm & 31
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::LslReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::ShrS { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::AsrReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::ShrU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::LsrReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Rotate right: WASM masks to 5 bits, ARM ROR by register
                // uses low byte (ROR by 32 = no-op on ARM, but WASM wants same)
                // Actually ROR wraps naturally, but we mask for consistency
                Opcode::Rotr { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    arm_instrs.push(ArmOp::RorReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Rotate left: ROTL(x, n) = ROR(x, 32 - (n & 31))
                // Emit: AND R12, Rm, #31; RSB R12, R12, #32; ROR.W Rd, Rn, R12
                Opcode::Rotl { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);
                    // R12 = rm & 31
                    arm_instrs.push(ArmOp::And {
                        rd: Reg::R12,
                        rn: rm,
                        op2: Operand2::Imm(31),
                    });
                    // R12 = 32 - R12
                    arm_instrs.push(ArmOp::Rsb {
                        rd: Reg::R12,
                        rn: Reg::R12,
                        imm: 32,
                    });
                    // rd = ROR(rn, R12)
                    arm_instrs.push(ArmOp::RorReg {
                        rd,
                        rn,
                        rm: Reg::R12,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Bit count operations (unary)
                Opcode::Clz { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Clz { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Ctz { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    // CTZ = CLZ(RBIT(x)) - reverse bits, then count leading zeros
                    arm_instrs.push(ArmOp::Rbit { rd, rm });
                    arm_instrs.push(ArmOp::Clz { rd, rm: rd });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Popcnt { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    // Popcnt - no direct instruction, use Popcnt pseudo-op
                    arm_instrs.push(ArmOp::Popcnt { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Sign extension operations (unary)
                Opcode::Extend8S { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sxtb { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::Extend16S { dest, src } => {
                    let rm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rm]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Sxth { rd, rm });
                    last_result_vreg = Some(dest.0);
                }

                // Eqz - compare with zero (unary)
                Opcode::Eqz { dest, src } => {
                    let rn = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rn]);
                    vreg_to_arm.insert(dest.0, rd);

                    // CMP rn, #0; SetCond rd, EQ
                    arm_instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    });
                    arm_instrs.push(ArmOp::SetCond {
                        rd,
                        cond: crate::rules::Condition::EQ,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Comparisons - set result to 0 or 1
                Opcode::Eq { dest, src1, src2 }
                | Opcode::Ne { dest, src1, src2 }
                | Opcode::LtS { dest, src1, src2 }
                | Opcode::LtU { dest, src1, src2 }
                | Opcode::LeS { dest, src1, src2 }
                | Opcode::LeU { dest, src1, src2 }
                | Opcode::GtS { dest, src1, src2 }
                | Opcode::GtU { dest, src1, src2 }
                | Opcode::GeS { dest, src1, src2 }
                | Opcode::GeU { dest, src1, src2 } => {
                    let rn = get_arm_reg(src1, &vreg_to_arm, &spilled_vregs)?;
                    let rm = get_arm_reg(src2, &vreg_to_arm, &spilled_vregs)?;
                    // Pre-fix this hardcoded `Reg::R7` to keep the SetCond
                    // encodable as 16-bit Thumb (which can only address R0-R7).
                    // R7 is callee-saved (no AAPCS clobber) but the hardcode
                    // collided with non-param locals stored in R7. Use
                    // `alloc_i32_scratch` constrained to the R4..R7 lower-
                    // bank candidates so SetCond keeps its 16-bit encoding
                    // when possible. (R4..R7 are all in the helper's
                    // search list and all 16-bit-MOV-addressable.)
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[rn, rm],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    let cond = match &inst.opcode {
                        Opcode::Eq { .. } => crate::rules::Condition::EQ,
                        Opcode::Ne { .. } => crate::rules::Condition::NE,
                        Opcode::LtS { .. } => crate::rules::Condition::LT,
                        Opcode::LtU { .. } => crate::rules::Condition::LO,
                        Opcode::LeS { .. } => crate::rules::Condition::LE,
                        Opcode::LeU { .. } => crate::rules::Condition::LS,
                        Opcode::GtS { .. } => crate::rules::Condition::GT,
                        Opcode::GtU { .. } => crate::rules::Condition::HI,
                        Opcode::GeS { .. } => crate::rules::Condition::GE,
                        Opcode::GeU { .. } => crate::rules::Condition::HS,
                        _ => crate::rules::Condition::EQ,
                    };

                    arm_instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Reg(rm),
                    });
                    arm_instrs.push(ArmOp::SetCond { rd, cond });
                    // Track comparison result as potential return value
                    last_result_vreg = Some(dest.0);
                }

                // Control flow
                Opcode::Branch { target } => {
                    // Record this branch for later resolution
                    pending_branches.push((arm_instrs.len(), *target, false));
                    // Emit placeholder - will be patched later
                    arm_instrs.push(ArmOp::BOffset { offset: 0 });
                }

                Opcode::CondBranch { cond, target } => {
                    let rcond = get_arm_reg(cond, &vreg_to_arm, &spilled_vregs)?;
                    arm_instrs.push(ArmOp::Cmp {
                        rn: rcond,
                        op2: Operand2::Imm(0),
                    });
                    // Record this branch for later resolution
                    pending_branches.push((arm_instrs.len(), *target, true));
                    // Emit placeholder conditional branch (branch if NOT equal to zero)
                    arm_instrs.push(ArmOp::BCondOffset {
                        cond: crate::rules::Condition::NE,
                        offset: 0,
                    });
                }

                Opcode::Return { value } => {
                    if let Some(v) = value {
                        let rv = get_arm_reg(v, &vreg_to_arm, &spilled_vregs)?;
                        if rv != Reg::R0 {
                            arm_instrs.push(ArmOp::Mov {
                                rd: Reg::R0,
                                op2: Operand2::Reg(rv),
                            });
                        }
                    }
                    arm_instrs.push(ArmOp::Bx { rm: Reg::LR });
                }

                // Select: dest = cond != 0 ? val_true : val_false
                // Implementation: CMP cond, #0; IT EQ; MOVEQ dest, val_false
                // (if cond==0, move val_false to dest; otherwise val_true is already in position)
                Opcode::Select {
                    dest,
                    val_true,
                    val_false,
                    cond,
                } => {
                    let r_cond = get_arm_reg(cond, &vreg_to_arm, &spilled_vregs)?;
                    let r_true = get_arm_reg(val_true, &vreg_to_arm, &spilled_vregs)?;
                    let r_false = get_arm_reg(val_false, &vreg_to_arm, &spilled_vregs)?;

                    // Pre-fix this hardcoded R3, clobbering the 4th AAPCS
                    // arg on every Select. Use `alloc_i32_scratch` so the
                    // destination is callee-saved by construction.
                    let rd = alloc_i32_scratch(
                        &vreg_to_arm,
                        &local_to_reg,
                        &param_reserved_regs,
                        &[r_cond, r_true, r_false],
                    );
                    vreg_to_arm.insert(dest.0, rd);

                    // CRITICAL: If condition is in rd and we need to move val_true to rd,
                    // we must save the condition first to avoid clobbering it
                    let actual_cond = if r_cond == rd && r_true != rd {
                        // Save condition to R12 (IP) before overwriting rd
                        arm_instrs.push(ArmOp::Mov {
                            rd: Reg::R12,
                            op2: Operand2::Reg(r_cond),
                        });
                        Reg::R12
                    } else {
                        r_cond
                    };

                    // Move val_true to result (it will be overwritten if cond==0)
                    if r_true != rd {
                        arm_instrs.push(ArmOp::Mov {
                            rd,
                            op2: Operand2::Reg(r_true),
                        });
                    }

                    // Compare condition with 0
                    arm_instrs.push(ArmOp::Cmp {
                        rn: actual_cond,
                        op2: Operand2::Imm(0),
                    });

                    // If cond == 0, overwrite with val_false using conditional move
                    arm_instrs.push(ArmOp::SelectMove {
                        rd,
                        rm: r_false,
                        cond: crate::rules::Condition::EQ,
                    });

                    // Track Select result as the function return value
                    last_result_vreg = Some(dest.0);
                }

                // i64 operations (register pairs on 32-bit ARM)
                // Per AAPCS: i64 params in R0:R1 and R2:R3, result in R0:R1

                // I64Load: load an i64 parameter from local index
                // For i64 params on 32-bit ARM:
                // - Param 0 (i64) is in R0:R1
                // - Param 1 (i64) is in R2:R3
                Opcode::I64Load {
                    dest_lo,
                    dest_hi,
                    addr,
                } => {
                    // Map local index to register pair
                    // Per AAPCS: i64 uses consecutive even/odd register pairs
                    let (lo_reg, hi_reg) = if *addr == 0 && num_params >= 2 {
                        (Reg::R0, Reg::R1) // First i64 param
                    } else if *addr == 1 && num_params >= 4 {
                        (Reg::R2, Reg::R3) // Second i64 param
                    } else {
                        // Non-param i64 local: pick a free callee-saved pair so we
                        // don't clobber AAPCS arg regs that haven't been read yet.
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs)
                    };
                    vreg_to_arm.insert(dest_lo.0, lo_reg);
                    vreg_to_arm.insert(dest_hi.0, hi_reg);
                    // No ARM instructions needed - values are already in registers for params
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Const {
                    dest_lo,
                    dest_hi,
                    value,
                } => {
                    // Record the constant value so downstream i64 shift / mask
                    // handlers can detect and special-case constant operands.
                    // See `known_i64_consts` declaration for the rationale (issue #94).
                    known_i64_consts.insert(dest_lo.0, *value);
                    // Issue #94: if the pre-pass marked this constant as
                    // dead-on-arrival (its sole use is folded by the
                    // shift/and handler), skip emitting it entirely.
                    if skip_const_dest_lo.contains(&dest_lo.0) {
                        continue;
                    }
                    // Load 64-bit constant into register pair
                    let lo = (*value & 0xFFFFFFFF) as u32;
                    let hi = ((*value >> 32) & 0xFFFFFFFF) as u32;
                    // Choose a free callee-saved pair so we don't trample params still
                    // sitting in R0..R3. The earlier heuristic (vreg-id → R0:R1 / R2:R3)
                    // ignored AAPCS, breaking any function that issued an i64.const
                    // before reading its i32 params.
                    let (lo_reg, hi_reg) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, lo_reg);
                    vreg_to_arm.insert(dest_hi.0, hi_reg);
                    // Load low word
                    if lo <= 255 {
                        arm_instrs.push(ArmOp::Mov {
                            rd: lo_reg,
                            op2: Operand2::Imm(lo as i32),
                        });
                    } else {
                        arm_instrs.push(ArmOp::Movw {
                            rd: lo_reg,
                            imm16: (lo & 0xFFFF) as u16,
                        });
                        if lo > 0xFFFF {
                            arm_instrs.push(ArmOp::Movt {
                                rd: lo_reg,
                                imm16: ((lo >> 16) & 0xFFFF) as u16,
                            });
                        }
                    }
                    // Load high word
                    if hi <= 255 {
                        arm_instrs.push(ArmOp::Mov {
                            rd: hi_reg,
                            op2: Operand2::Imm(hi as i32),
                        });
                    } else {
                        arm_instrs.push(ArmOp::Movw {
                            rd: hi_reg,
                            imm16: (hi & 0xFFFF) as u16,
                        });
                        if hi > 0xFFFF {
                            arm_instrs.push(ArmOp::Movt {
                                rd: hi_reg,
                                imm16: ((hi >> 16) & 0xFFFF) as u16,
                            });
                        }
                    }
                    // If this i64 const is the final return value, the epilogue
                    // needs to know which pair holds it (for the move into R0:R1).
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Add {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    // i64.add: rd = rn + rm using the actual operand regs from
                    // vreg_to_arm — NOT hardcoded R0:R1/R2:R3 (which would clobber
                    // AAPCS param regs).
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Adds {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Adc {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Sub {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Subs {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Sbc {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64And {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    // Issue #94: `i64.and` against a constant low-half mask
                    // (typically `0xFFFFFFFF` to extract the lo32 of a u64-packed
                    // FFI return). The lo half collapses to a no-op rename, the
                    // hi half collapses to MOV #0 — saving the two AND.W
                    // instructions (8 bytes total) plus the MOVW/MOVT for the
                    // mask constant itself (deduped by ConstantFolding/CSE in
                    // most cases, but the ANDs always remain).
                    let mask = known_i64_consts.get(&src2_lo.0).copied();
                    if let Some(m) = mask {
                        let m_u64 = m as u64;
                        if m_u64 == 0xFFFF_FFFF {
                            // Low 32 bits unchanged, high 32 bits zeroed.
                            let rd_hi =
                                alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs).1;
                            vreg_to_arm.insert(dest_lo.0, rn_lo);
                            vreg_to_arm.insert(dest_hi.0, rd_hi);
                            arm_instrs.push(ArmOp::Mov {
                                rd: rd_hi,
                                op2: Operand2::Imm(0),
                            });
                            last_result_vreg = Some(dest_lo.0);
                            last_result_vreg_hi = Some(dest_hi.0);
                            is_i64_result = true;
                            // Skip the generic AND emit below.
                            continue;
                        }
                    }
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::And {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::And {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Or {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Orr {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Orr {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Xor {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::Eor {
                        rd: rd_lo,
                        rn: rn_lo,
                        op2: Operand2::Reg(rm_lo),
                    });
                    arm_instrs.push(ArmOp::Eor {
                        rd: rd_hi,
                        rn: rn_hi,
                        op2: Operand2::Reg(rm_hi),
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // ========================================================================
                // i64 Comparisons (result is single i32)
                //
                // Sources are read from `vreg_to_arm[src*]` rather than hardcoded
                // R0:R1/R2:R3 — the latter would mean "i64 ops always assume their
                // operands materialised at the AAPCS arg slots", which is false:
                // operand registers come from whatever the upstream IR producers
                // (I64Const, I64Load, prior i64 ops) chose. Result lands on the lo
                // half of a freshly allocated callee-saved pair so we don't smash
                // any AAPCS arg reg the user hasn't read yet.
                // ========================================================================
                Opcode::I64Eq {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::EQ,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64Ne {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::NE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LtS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LT,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GtS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::GT,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LeS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GeS {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::GE,
                    });
                    last_result_vreg = Some(dest.0);
                }

                // Unsigned i64 comparisons
                Opcode::I64LtU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LO,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GtU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::HI,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64LeU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::LS,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64GeU {
                    dest,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCond {
                        rd,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                        cond: Condition::HS,
                    });
                    last_result_vreg = Some(dest.0);
                }

                Opcode::I64Eqz {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rn_lo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd, _) = alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::I64SetCondZ { rd, rn_lo, rn_hi });
                    last_result_vreg = Some(dest.0);
                }

                // i64 count leading zeros (i64 result: lo gets count, hi must be 0).
                //
                // The ArmOp::I64Clz encoder writes the count into `rd` AND zeroes
                // `rnhi` in-place — so `rnhi` doubles as the result's hi half. To
                // keep the upstream src_hi register intact and avoid clobbering
                // unrelated AAPCS regs, we copy src_hi into a freshly allocated
                // callee-saved hi slot and pass that as `rnhi`. After the encoded
                // sequence, the i64 result lives in (rd_lo, rd_hi).
                //
                // The IR Opcode only carries a single `dest` vreg (the lo half);
                // we register dest.0 → rd_lo. The hi-zero is implicit and used by
                // the function epilogue when this is the i64 return value (see
                // last_result_vreg_hi_reg below).
                Opcode::I64Clz {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi_src = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if rd_hi != rnhi_src {
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Reg(rnhi_src),
                        });
                    }
                    vreg_to_arm.insert(dest.0, rd_lo);
                    arm_instrs.push(ArmOp::I64Clz {
                        rd: rd_lo,
                        rnlo,
                        rnhi: rd_hi,
                    });
                    last_result_vreg = Some(dest.0);
                    last_result_vreg_hi_reg = Some(rd_hi);
                    is_i64_result = true;
                }

                // i64 count trailing zeros — same pattern as I64Clz above.
                Opcode::I64Ctz {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi_src = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if rd_hi != rnhi_src {
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Reg(rnhi_src),
                        });
                    }
                    vreg_to_arm.insert(dest.0, rd_lo);
                    arm_instrs.push(ArmOp::I64Ctz {
                        rd: rd_lo,
                        rnlo,
                        rnhi: rd_hi,
                    });
                    last_result_vreg = Some(dest.0);
                    last_result_vreg_hi_reg = Some(rd_hi);
                    is_i64_result = true;
                }

                // i64 population count — same pattern as I64Clz above.
                Opcode::I64Popcnt {
                    dest,
                    src_lo,
                    src_hi,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi_src = get_arm_reg(src_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if rd_hi != rnhi_src {
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Reg(rnhi_src),
                        });
                    }
                    vreg_to_arm.insert(dest.0, rd_lo);
                    arm_instrs.push(ArmOp::I64Popcnt {
                        rd: rd_lo,
                        rnlo,
                        rnhi: rd_hi,
                    });
                    last_result_vreg = Some(dest.0);
                    last_result_vreg_hi_reg = Some(rd_hi);
                    is_i64_result = true;
                }

                // i64 sign extension operations
                Opcode::I64Extend8S {
                    dest_lo,
                    dest_hi,
                    src_lo,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Extend8S { rdlo, rdhi, rnlo });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Extend16S {
                    dest_lo,
                    dest_hi,
                    src_lo,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Extend16S { rdlo, rdhi, rnlo });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                Opcode::I64Extend32S {
                    dest_lo,
                    dest_hi,
                    src_lo,
                } => {
                    let rnlo = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Extend32S { rdlo, rdhi, rnlo });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i32 -> i64 zero-extension (issue #93 fix).
                //
                // Critical: we MUST move `src` into a callee-saved register
                // pair, even if `src` was already in a non-param register.
                // The downstream `I64Shl/ShrU/ShrS` ARM emitter writes to
                // both `rm_lo` and `rm_hi` (see `arm_encoder.rs:2872`,
                // `:2954`, `:3036` — `AND.W rm_lo, rm_lo, #63;
                // SUBS.W rm_hi, rm_lo, #32; ...`). Pre-fix, `src` could be
                // an AAPCS param register (R0..R3) and the shift would
                // clobber the caller's argument. By Mov'ing into a fresh
                // pair from `alloc_i64_pair` (which excludes params and
                // live vregs), we guarantee `rm_lo`/`rm_hi` are scratch.
                Opcode::I64ExtendI32U {
                    dest_lo,
                    dest_hi,
                    src,
                } => {
                    let src_arm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let (new_lo, new_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if src_arm != new_lo {
                        arm_instrs.push(ArmOp::Mov {
                            rd: new_lo,
                            op2: crate::rules::Operand2::Reg(src_arm),
                        });
                    }
                    arm_instrs.push(ArmOp::Movw {
                        rd: new_hi,
                        imm16: 0,
                    });
                    // Re-map dest_lo (which IS the src vreg by IR convention)
                    // to the new lo arm reg, AND map dest_hi to the new hi.
                    vreg_to_arm.insert(dest_lo.0, new_lo);
                    vreg_to_arm.insert(dest_hi.0, new_hi);
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i32 -> i64 sign-extension. Same scratch-pair discipline as
                // I64ExtendI32U; the high half is `src ASR #31`.
                Opcode::I64ExtendI32S {
                    dest_lo,
                    dest_hi,
                    src,
                } => {
                    let src_arm = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let (new_lo, new_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    if src_arm != new_lo {
                        arm_instrs.push(ArmOp::Mov {
                            rd: new_lo,
                            op2: crate::rules::Operand2::Reg(src_arm),
                        });
                    }
                    // hi = src ASR #31 — sign bit replicated across all 32 bits.
                    arm_instrs.push(ArmOp::Asr {
                        rd: new_hi,
                        rn: new_lo,
                        shift: 31,
                    });
                    vreg_to_arm.insert(dest_lo.0, new_lo);
                    vreg_to_arm.insert(dest_hi.0, new_hi);
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 -> i32 wrap. The result IS the low 32 bits of the
                // input — by IR convention `dest == src_lo` (same vreg),
                // so the lookup of `dest` is already correctly mapped to
                // the i64 lo half's ARM register. Emit no ARM code.
                Opcode::I32WrapI64 { dest, src_lo } => {
                    let src_arm = get_arm_reg(src_lo, &vreg_to_arm, &spilled_vregs)?;
                    vreg_to_arm.insert(dest.0, src_arm);
                    last_result_vreg = Some(dest.0);
                    is_i64_result = false;
                }

                // i64 multiply: UMULL + MLA cross products
                Opcode::I64Mul {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::I64Mul {
                        rd_lo,
                        rd_hi,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 shift left
                Opcode::I64Shl {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rd_lo, rd_hi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rd_lo);
                    vreg_to_arm.insert(dest_hi.0, rd_hi);
                    arm_instrs.push(ArmOp::I64Shl {
                        rd_lo,
                        rd_hi,
                        rn_lo,
                        rn_hi,
                        rm_lo,
                        rm_hi,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 arithmetic shift right
                Opcode::I64ShrS {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    // Issue #94 (signed variant): `i64.shr_s 32; i32.wrap_i64`
                    // also extracts the upper 32 bits unchanged. dest_lo = rn_hi,
                    // dest_hi = sign-extension of rn_hi (ASR #31 of rn_hi).
                    let shr_const = known_i64_consts
                        .get(&src2_lo.0)
                        .copied()
                        .map(|v| (v as u64) & 0x3F);
                    if shr_const == Some(32) {
                        let rd_hi =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs).1;
                        vreg_to_arm.insert(dest_lo.0, rn_hi);
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        // ASR rd_hi, rn_hi, #31 — replicate the sign bit across
                        // the new hi half. 4-byte Thumb-2 encoding via Asr-imm.
                        arm_instrs.push(ArmOp::Asr {
                            rd: rd_hi,
                            rn: rn_hi,
                            shift: 31,
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    } else {
                        let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                        let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                        let (rd_lo, rd_hi) =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                        vreg_to_arm.insert(dest_lo.0, rd_lo);
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        arm_instrs.push(ArmOp::I64ShrS {
                            rd_lo,
                            rd_hi,
                            rn_lo,
                            rn_hi,
                            rm_lo,
                            rm_hi,
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    }
                }

                // i64 logical shift right
                Opcode::I64ShrU {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rn_lo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rn_hi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    // Issue #94: u64-packed FFI return — `i64.shr_u 32` extracts
                    // the high 32 bits, which are already sitting in `rn_hi`. Skip
                    // the 38-byte runtime shift sequence; just rename `dest_lo`
                    // onto `rn_hi` and zero `dest_hi`. Total cost: a single
                    // `mov rd_hi, #0` (2-4 bytes) instead of 38 bytes.
                    //
                    // Per WASM semantics the shift amount is taken modulo 64, so
                    // any constant whose low 6 bits == 32 hits this fast path.
                    let shr_const = known_i64_consts
                        .get(&src2_lo.0)
                        .copied()
                        .map(|v| (v as u64) & 0x3F);
                    if shr_const == Some(32) {
                        let rd_hi =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs).1;
                        // dest_lo aliases the source's hi register (no instruction).
                        vreg_to_arm.insert(dest_lo.0, rn_hi);
                        // dest_hi is zero — emit a single MOV rd_hi, #0.
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        arm_instrs.push(ArmOp::Mov {
                            rd: rd_hi,
                            op2: Operand2::Imm(0),
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    } else {
                        let rm_lo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                        let rm_hi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                        let (rd_lo, rd_hi) =
                            alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                        vreg_to_arm.insert(dest_lo.0, rd_lo);
                        vreg_to_arm.insert(dest_hi.0, rd_hi);
                        arm_instrs.push(ArmOp::I64ShrU {
                            rd_lo,
                            rd_hi,
                            rn_lo,
                            rn_hi,
                            rm_lo,
                            rm_hi,
                        });
                        last_result_vreg = Some(dest_lo.0);
                        last_result_vreg_hi = Some(dest_hi.0);
                        is_i64_result = true;
                    }
                }

                // i64 rotate left
                Opcode::I64Rotl {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    ..
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let shift = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Rotl {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        shift,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 rotate right
                Opcode::I64Rotr {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    ..
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let shift = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64Rotr {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        shift,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 signed division
                Opcode::I64DivS {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64DivS {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                        // #494: the optimized path never consumes fact marks —
                        // marked functions are routed to the direct selector.
                        elide_zero_guard: false,
                        elide_overflow_guard: false,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 unsigned division
                Opcode::I64DivU {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64DivU {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                        elide_zero_guard: false,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 signed remainder
                Opcode::I64RemS {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64RemS {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                        elide_zero_guard: false,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // i64 unsigned remainder
                Opcode::I64RemU {
                    dest_lo,
                    dest_hi,
                    src1_lo,
                    src1_hi,
                    src2_lo,
                    src2_hi,
                } => {
                    let rnlo = get_arm_reg(src1_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rnhi = get_arm_reg(src1_hi, &vreg_to_arm, &spilled_vregs)?;
                    let rmlo = get_arm_reg(src2_lo, &vreg_to_arm, &spilled_vregs)?;
                    let rmhi = get_arm_reg(src2_hi, &vreg_to_arm, &spilled_vregs)?;
                    let (rdlo, rdhi) =
                        alloc_i64_pair(&vreg_to_arm, &local_to_reg, &param_reserved_regs);
                    vreg_to_arm.insert(dest_lo.0, rdlo);
                    vreg_to_arm.insert(dest_hi.0, rdhi);
                    arm_instrs.push(ArmOp::I64RemU {
                        rdlo,
                        rdhi,
                        rnlo,
                        rnhi,
                        rmlo,
                        rmhi,
                        elide_zero_guard: false,
                    });
                    last_result_vreg = Some(dest_lo.0);
                    last_result_vreg_hi = Some(dest_hi.0);
                    is_i64_result = true;
                }

                // ========================================================================
                // Control Flow Operations (Loop Support)
                // ========================================================================

                // Label: marks a branch target position
                // Labels don't emit any code - they're just markers for branch offset calculation
                Opcode::Label { id } => {
                    // Record where this IR instruction maps to in ARM instructions
                    // The branch target is the NEXT ARM instruction to be emitted
                    ir_to_arm_idx.insert(*id, arm_instrs.len());
                    // No ARM instruction emitted for labels
                }

                // Copy: move value from src to dest (for local.tee semantics)
                //
                // Pre-fix hardcoded `rd = Reg::R0`, which clobbered the
                // first AAPCS param on every local.tee even when neither
                // src nor dest had anything to do with R0.
                Opcode::Copy { dest, src } => {
                    let rs = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[rs]);
                    vreg_to_arm.insert(dest.0, rd);
                    if rs != rd {
                        arm_instrs.push(ArmOp::Mov {
                            rd,
                            op2: Operand2::Reg(rs),
                        });
                    }
                    last_result_vreg = Some(dest.0);
                }

                // TeeStore: Store to local AND keep value on stack (local.tee)
                Opcode::TeeStore { dest, src, addr } => {
                    let rs = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;

                    // For non-param locals, move to the local's dedicated register
                    if (*addr as usize) >= num_params {
                        let local_idx = (*addr as usize).saturating_sub(num_params);
                        let local_reg = if local_idx < local_regs.len() {
                            local_regs[local_idx]
                        } else {
                            Reg::R4
                        };
                        // Move value to the local's register if not already there
                        if rs != local_reg {
                            arm_instrs.push(ArmOp::Mov {
                                rd: local_reg,
                                op2: Operand2::Reg(rs),
                            });
                        }
                        local_to_reg.insert(*addr, local_reg);
                        // The dest vreg now refers to the local's register
                        vreg_to_arm.insert(dest.0, local_reg);
                    } else {
                        // For param locals (local.tee to a param), move to param register
                        // This handles cases like modifying loop counter that was passed as param
                        let param_reg = if (*addr as usize) < 4 {
                            param_regs[*addr as usize]
                        } else {
                            Reg::R0
                        };
                        if rs != param_reg {
                            arm_instrs.push(ArmOp::Mov {
                                rd: param_reg,
                                op2: Operand2::Reg(rs),
                            });
                        }
                        vreg_to_arm.insert(dest.0, param_reg);
                    }
                    // TeeStore produces a value that may be the function result
                    last_result_vreg = Some(dest.0);
                }

                // ========================================================================
                // Linear Memory Operations
                // ========================================================================

                // MemLoad: load 32-bit value from linear memory.
                //
                // Generates: MOVW R12, #base_lo; MOVT R12, #base_hi;
                //            ADD R12, R12, Raddr; LDR Rd, [R12, #offset]
                //
                // `Rd` MUST NOT alias an AAPCS param register (R0..R3) — a
                // `local.get` of param N anywhere downstream would otherwise
                // observe whatever the MemLoad just wrote. Pre-fix this was
                // hardcoded to `Reg::R3`, which clobbered the 4th AAPCS
                // argument on every `i32.load`. Use the scratch helper so
                // the destination is picked from the callee-saved bank.
                Opcode::MemLoad { dest, addr, offset } => {
                    // VCR-RA lever 3 base-CSE: const address → load directly off the
                    // once-materialized base in R11 (no per-access base / add / addr).
                    if let Some(plan) = &base_cse
                        && let Some(&folded) = plan.fold.get(&addr.0)
                    {
                        let rd = alloc_i32_scratch(
                            &vreg_to_arm,
                            &local_to_reg,
                            &param_reserved_regs,
                            &[],
                        );
                        vreg_to_arm.insert(dest.0, rd);
                        arm_instrs.push(ArmOp::Ldr {
                            rd,
                            addr: crate::rules::MemAddr::imm(BASE_CSE_REG, folded),
                        });
                        last_result_vreg = Some(dest.0);
                    } else {
                        let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs)?;
                        let rd = alloc_i32_scratch(
                            &vreg_to_arm,
                            &local_to_reg,
                            &param_reserved_regs,
                            &[r_addr],
                        );
                        vreg_to_arm.insert(dest.0, rd);

                        // #377: --safety-bounds software — guard BEFORE the base
                        // materialization (R12 still free).
                        if self.bounds_check == BoundsCheckConfig::Software {
                            push_software_bounds_guard(&mut arm_instrs, r_addr, *offset, 4);
                        }

                        // Linear memory base (default 0x20000100; #687 shifts
                        // it under --stack-layout=low). #382: fold a large
                        // static offset (> imm12) into the compile-time-
                        // constant base so the access immediate is 0.
                        let (base, mem_off) = fold_mem_offset(self.linmem_base, *offset);
                        let base_lo = (base & 0xFFFF) as u16;
                        let base_hi = ((base >> 16) & 0xFFFF) as u16;

                        // Load base address into R12 (scratch register)
                        arm_instrs.push(ArmOp::Movw {
                            rd: Reg::R12,
                            imm16: base_lo,
                        });
                        arm_instrs.push(ArmOp::Movt {
                            rd: Reg::R12,
                            imm16: base_hi,
                        });
                        // Add WASM address offset
                        arm_instrs.push(ArmOp::Add {
                            rd: Reg::R12,
                            rn: Reg::R12,
                            op2: Operand2::Reg(r_addr),
                        });
                        // Load from [base + wasm_addr + static_offset]
                        arm_instrs.push(ArmOp::Ldr {
                            rd,
                            addr: crate::rules::MemAddr::imm(Reg::R12, mem_off),
                        });
                        last_result_vreg = Some(dest.0);
                    }
                }

                // MemStore: store 32-bit value to linear memory
                // Generates: MOVW R12, #base_lo; MOVT R12, #base_hi; ADD R12, R12, Raddr; STR Rsrc, [R12, #offset]
                Opcode::MemStore { src, addr, offset } => {
                    // VCR-RA lever 3 base-CSE: the address is a folded compile-time
                    // constant — store directly off the once-materialized base in
                    // R11, dropping the per-access `movw/movt` + `add` and the
                    // address materialization (skipped at its `Const`).
                    if let Some(plan) = &base_cse
                        && let Some(&folded) = plan.fold.get(&addr.0)
                    {
                        let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                        arm_instrs.push(ArmOp::Str {
                            rd: r_src,
                            addr: crate::rules::MemAddr::imm(BASE_CSE_REG, folded),
                        });
                    } else {
                        let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs)?;
                        let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;

                        // #377: --safety-bounds software guard (see MemLoad).
                        if self.bounds_check == BoundsCheckConfig::Software {
                            push_software_bounds_guard(&mut arm_instrs, r_addr, *offset, 4);
                        }

                        // Linear memory base (default 0x20000100; #687 shifts
                        // it under --stack-layout=low). #382: fold a large
                        // static offset (> imm12) into the compile-time-
                        // constant base so the access immediate is 0.
                        let (base, mem_off) = fold_mem_offset(self.linmem_base, *offset);
                        let base_lo = (base & 0xFFFF) as u16;
                        let base_hi = ((base >> 16) & 0xFFFF) as u16;

                        // Load base address into R12 (scratch register)
                        arm_instrs.push(ArmOp::Movw {
                            rd: Reg::R12,
                            imm16: base_lo,
                        });
                        arm_instrs.push(ArmOp::Movt {
                            rd: Reg::R12,
                            imm16: base_hi,
                        });
                        // Add WASM address offset
                        arm_instrs.push(ArmOp::Add {
                            rd: Reg::R12,
                            rn: Reg::R12,
                            op2: Operand2::Reg(r_addr),
                        });
                        // Store to [base + wasm_addr + static_offset]
                        arm_instrs.push(ArmOp::Str {
                            rd: r_src,
                            addr: crate::rules::MemAddr::imm(Reg::R12, mem_off),
                        });
                    }
                    // MemStore does not produce a value
                }

                // Sub-word linear memory load (i32.load8_s/u, i32.load16_s/u).
                //
                // Generates the same base+addr math as MemLoad, then LDRB/
                // LDRH/LDRSB/LDRSH into a non-param destination register
                // chosen by `alloc_i32_scratch`. Pre-fix these wasm ops
                // had no IR handler; the optimizer pipeline left the
                // produced vreg unmapped → defensive panic (or pre-PR-101
                // silent R0 alias).
                Opcode::MemLoadSubword {
                    dest,
                    addr,
                    offset,
                    width,
                    signed,
                } => {
                    // VCR-RA lever 3 base-CSE: const address → subword load off R11.
                    let (rd, addr_mem) = if let Some(plan) = &base_cse
                        && let Some(&folded) = plan.fold.get(&addr.0)
                    {
                        let rd = alloc_i32_scratch(
                            &vreg_to_arm,
                            &local_to_reg,
                            &param_reserved_regs,
                            &[],
                        );
                        vreg_to_arm.insert(dest.0, rd);
                        (rd, crate::rules::MemAddr::imm(BASE_CSE_REG, folded))
                    } else {
                        let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs)?;
                        let rd = alloc_i32_scratch(
                            &vreg_to_arm,
                            &local_to_reg,
                            &param_reserved_regs,
                            &[r_addr],
                        );
                        vreg_to_arm.insert(dest.0, rd);

                        // #377: --safety-bounds software guard (see MemLoad).
                        if self.bounds_check == BoundsCheckConfig::Software {
                            push_software_bounds_guard(&mut arm_instrs, r_addr, *offset, *width);
                        }

                        // #382: fold a large static offset (> imm12) into the
                        // compile-time-constant base (#687-shifted under
                        // --stack-layout=low) so the access immediate is 0.
                        let (base, mem_off) = fold_mem_offset(self.linmem_base, *offset);
                        let base_lo = (base & 0xFFFF) as u16;
                        let base_hi = ((base >> 16) & 0xFFFF) as u16;
                        arm_instrs.push(ArmOp::Movw {
                            rd: Reg::R12,
                            imm16: base_lo,
                        });
                        arm_instrs.push(ArmOp::Movt {
                            rd: Reg::R12,
                            imm16: base_hi,
                        });
                        arm_instrs.push(ArmOp::Add {
                            rd: Reg::R12,
                            rn: Reg::R12,
                            op2: Operand2::Reg(r_addr),
                        });
                        (rd, crate::rules::MemAddr::imm(Reg::R12, mem_off))
                    };
                    let sub_op = match (*width, *signed) {
                        (1, false) => ArmOp::Ldrb { rd, addr: addr_mem },
                        (1, true) => ArmOp::Ldrsb { rd, addr: addr_mem },
                        (2, false) => ArmOp::Ldrh { rd, addr: addr_mem },
                        (2, true) => ArmOp::Ldrsh { rd, addr: addr_mem },
                        // Width 4 is impossible here (caller would use
                        // `Opcode::MemLoad`); fall through to plain Ldr
                        // rather than panicking — that keeps the lowering
                        // total, and the encoder will validate.
                        _ => ArmOp::Ldr { rd, addr: addr_mem },
                    };
                    arm_instrs.push(sub_op);
                    last_result_vreg = Some(dest.0);
                }

                // Sub-word linear memory store (i32.store8, i32.store16,
                // i64.store8/16/32). Generates address math + STRB/STRH/STR.
                Opcode::MemStoreSubword {
                    src,
                    addr,
                    offset,
                    width,
                } => {
                    // VCR-RA lever 3 base-CSE: const address → subword store off R11.
                    let (r_src, addr_mem) = if let Some(plan) = &base_cse
                        && let Some(&folded) = plan.fold.get(&addr.0)
                    {
                        let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                        (r_src, crate::rules::MemAddr::imm(BASE_CSE_REG, folded))
                    } else {
                        let r_addr = get_arm_reg(addr, &vreg_to_arm, &spilled_vregs)?;
                        let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;

                        // #377: --safety-bounds software guard (see MemLoad).
                        if self.bounds_check == BoundsCheckConfig::Software {
                            push_software_bounds_guard(&mut arm_instrs, r_addr, *offset, *width);
                        }

                        // #382: fold a large static offset (> imm12) into the
                        // compile-time-constant base (#687-shifted under
                        // --stack-layout=low) so the access immediate is 0.
                        let (base, mem_off) = fold_mem_offset(self.linmem_base, *offset);
                        let base_lo = (base & 0xFFFF) as u16;
                        let base_hi = ((base >> 16) & 0xFFFF) as u16;
                        arm_instrs.push(ArmOp::Movw {
                            rd: Reg::R12,
                            imm16: base_lo,
                        });
                        arm_instrs.push(ArmOp::Movt {
                            rd: Reg::R12,
                            imm16: base_hi,
                        });
                        arm_instrs.push(ArmOp::Add {
                            rd: Reg::R12,
                            rn: Reg::R12,
                            op2: Operand2::Reg(r_addr),
                        });
                        (r_src, crate::rules::MemAddr::imm(Reg::R12, mem_off))
                    };
                    let sub_op = match *width {
                        1 => ArmOp::Strb {
                            rd: r_src,
                            addr: addr_mem,
                        },
                        2 => ArmOp::Strh {
                            rd: r_src,
                            addr: addr_mem,
                        },
                        _ => ArmOp::Str {
                            rd: r_src,
                            addr: addr_mem,
                        },
                    };
                    arm_instrs.push(sub_op);
                }

                // `global.get N` — load global N into a fresh non-param
                // scratch. ARM convention: R9 is the globals base, globals
                // are packed as 4-byte slots.
                Opcode::GlobalGet { dest, idx } => {
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[]);
                    vreg_to_arm.insert(dest.0, rd);
                    arm_instrs.push(ArmOp::Ldr {
                        rd,
                        addr: crate::rules::MemAddr::imm(Reg::R9, (*idx as i32) * 4),
                    });
                    last_result_vreg = Some(dest.0);
                }

                // `global.set N` — store the popped i32 to global N.
                Opcode::GlobalSet { src, idx } => {
                    let r_src = get_arm_reg(src, &vreg_to_arm, &spilled_vregs)?;
                    arm_instrs.push(ArmOp::Str {
                        rd: r_src,
                        addr: crate::rules::MemAddr::imm(Reg::R9, (*idx as i32) * 4),
                    });
                }

                // `memory.size` — current memory size in pages. Convention:
                // R10 holds the memory size word. Emit `MOV dest, R10`.
                Opcode::MemorySize { dest } => {
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[]);
                    vreg_to_arm.insert(dest.0, rd);
                    // #539: emit the dedicated MemorySize op — its encoder does
                    // `LSR rd, R10, #16` (bytes → pages). The previous `MOV rd,
                    // R10` returned the size in BYTES, not pages, so `memory.size`
                    // (and the `memory.grow(0)` fold that lowers to it) was 65536×
                    // too large on the optimized path.
                    arm_instrs.push(ArmOp::MemorySize { rd });
                    last_result_vreg = Some(dest.0);
                }

                // `memory.grow` — embedded targets have fixed memory; emit
                // a stub that returns -1 (the wasm spec's "grow failed"
                // sentinel). The `delta` is read but discarded.
                Opcode::MemoryGrow { dest, delta } => {
                    let _ = get_arm_reg(delta, &vreg_to_arm, &spilled_vregs)?;
                    let rd =
                        alloc_i32_scratch(&vreg_to_arm, &local_to_reg, &param_reserved_regs, &[]);
                    vreg_to_arm.insert(dest.0, rd);
                    // mov rd, #-1  →  MOVW rd, #0xFFFF; MOVT rd, #0xFFFF
                    arm_instrs.push(ArmOp::Movw { rd, imm16: 0xFFFF });
                    arm_instrs.push(ArmOp::Movt { rd, imm16: 0xFFFF });
                    last_result_vreg = Some(dest.0);
                }

                // Direct call. Emit `BL func_<idx>`; the AAPCS return value
                // is in R0, so we bind `dest` to R0. This MUST register
                // `dest` in `vreg_to_arm` — without that mapping, any
                // downstream consumer of the call result would hit the
                // unmapped-vreg path in `get_arm_reg` (formerly the silent
                // R0 fallback, now the PR #101 defensive panic — same class
                // of bug that motivated this fix).
                //
                // Caveat (out of scope for this PR): a call clobbers
                // R0..R3, so any vreg currently mapped to R0..R3 that
                // *survives* the call is invalidated by it. We don't model
                // that here — fully correct call-boundary regalloc in the
                // optimized path needs a broader rework. The narrow goal
                // here is "compile cleanly, don't panic on `WasmOp::Call`."
                Opcode::Call { dest, func_idx } => {
                    arm_instrs.push(ArmOp::Bl {
                        label: format!("func_{}", func_idx),
                    });
                    vreg_to_arm.insert(dest.0, Reg::R0);
                    last_result_vreg = Some(dest.0);
                }
            }

            // Track WASM operand value stack for correct br_if semantics.
            // br_if pops the condition; the value underneath is the result.
            match &inst.opcode {
                // Binary ops: consume 2, produce 1
                Opcode::Add { dest, .. }
                | Opcode::Sub { dest, .. }
                | Opcode::Mul { dest, .. }
                | Opcode::DivS { dest, .. }
                | Opcode::DivU { dest, .. }
                | Opcode::RemS { dest, .. }
                | Opcode::RemU { dest, .. }
                | Opcode::And { dest, .. }
                | Opcode::Or { dest, .. }
                | Opcode::Xor { dest, .. }
                | Opcode::Shl { dest, .. }
                | Opcode::ShrS { dest, .. }
                | Opcode::ShrU { dest, .. }
                | Opcode::Rotl { dest, .. }
                | Opcode::Rotr { dest, .. }
                | Opcode::Eq { dest, .. }
                | Opcode::Ne { dest, .. }
                | Opcode::LtS { dest, .. }
                | Opcode::LtU { dest, .. }
                | Opcode::LeS { dest, .. }
                | Opcode::LeU { dest, .. }
                | Opcode::GtS { dest, .. }
                | Opcode::GtU { dest, .. }
                | Opcode::GeS { dest, .. }
                | Opcode::GeU { dest, .. } => {
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Unary ops: consume 1, produce 1
                Opcode::Clz { dest, .. }
                | Opcode::Ctz { dest, .. }
                | Opcode::Popcnt { dest, .. }
                | Opcode::Eqz { dest, .. }
                | Opcode::Copy { dest, .. }
                | Opcode::Extend8S { dest, .. }
                | Opcode::Extend16S { dest, .. } => {
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // MemLoad: consume 1 (addr), produce 1 (loaded value)
                Opcode::MemLoad { dest, .. } => {
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Value producers: push 1
                Opcode::Load { dest, .. } | Opcode::Const { dest, .. } => {
                    value_stack.push(dest.0);
                }
                // Store: consume 1
                Opcode::Store { .. } => {
                    value_stack.pop();
                }
                // MemStore: consume 2 (addr, value), produce 0
                Opcode::MemStore { .. } => {
                    value_stack.pop();
                    value_stack.pop();
                }
                // TeeStore: consume 1, produce 1 (value stays on stack)
                Opcode::TeeStore { dest, .. } => {
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // CondBranch (br_if): pops condition, result is value underneath
                Opcode::CondBranch { .. } => {
                    value_stack.pop(); // pop condition
                    if let Some(&top) = value_stack.last() {
                        last_result_vreg = Some(top);
                    }
                }
                // Select: consume 3 (val1, val2, cond), produce 1
                Opcode::Select { dest, .. } => {
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.pop();
                    value_stack.push(dest.0);
                }
                // Call: produce 1 (the AAPCS return value in R0). The IR
                // doesn't yet carry arg-count metadata, so we do NOT pop
                // arg slots from the value stack — same imprecision as the
                // unhandled-call case prior to this fix; deferred to a
                // broader call-lowering rework.
                Opcode::Call { dest, .. } => {
                    value_stack.push(dest.0);
                }
                // Label, Branch, Nop, Return: no stack effect
                _ => {}
            }
        }

        // ========================================================================
        // Branch Resolution Pass: Patch branch offsets
        // ========================================================================
        // Calculate byte offsets for each instruction to handle variable-length
        // Thumb-2 encoding (SetCond = 6 bytes, most others = 2 bytes).

        // Estimate instruction byte sizes via the shared `estimate_arm_byte_size`
        // (extracted from the former inline closure, #498/#242). Must match the
        // encoder's behavior for correct branch offset calculation; the
        // `estimator_encoder_agreement` oracle in synth-backend pins it.

        // Build byte offset table: byte_offsets[i] = byte position of instruction i
        let mut byte_offsets: Vec<usize> = Vec::with_capacity(arm_instrs.len() + 1);
        let mut current_offset = 0usize;
        for op in &arm_instrs {
            byte_offsets.push(current_offset);
            current_offset += estimate_arm_byte_size(op);
        }
        byte_offsets.push(current_offset); // End marker for target lookups

        for (branch_arm_idx, target_ir_idx, is_conditional) in pending_branches {
            // Find where the target label is in ARM instructions.
            //
            // #500: a MISSING target used to be skipped silently, leaving the
            // offset-0 placeholder in the stream — `br_if` landed on the very
            // next instruction, mid-shape (the #483-class miscompile, broadened
            // by #500 to the if/else and sequential-block shapes). Any branch
            // whose target id never got a label is a lowering bug or an
            // unsupported shape; decline LOUDLY so the backend falls back to
            // the direct selector instead of emitting wrong code.
            let Some(&target_arm_idx) = ir_to_arm_idx.get(&target_ir_idx) else {
                return Err(Error::synthesis(format!(
                    "optimized path: branch at ARM index {branch_arm_idx} targets \
                     IR id {target_ir_idx}, but no label with that id was emitted — \
                     unresolvable forward-branch shape (#500); falling back to \
                     direct selector"
                )));
            };
            // Calculate the Thumb branch displacement
            // Formula: imm8 = (target_addr - (branch_addr + 4)) / 2
            // This is because PC points to branch_addr + 4 during execution
            let branch_byte_pos = byte_offsets[branch_arm_idx] as i32;
            let target_byte_pos = byte_offsets[target_arm_idx] as i32;

            // Halfword offset is the raw encoded value for imm8
            let halfword_offset = (target_byte_pos - branch_byte_pos - 4) / 2;

            // #498: `byte_offsets` sized this branch as the 2-byte short form
            // (the estimator runs on the offset-0 placeholder). If the resolved
            // displacement only fits the 4-byte `.w` encoding, the encoder would
            // emit 2 extra bytes the offset table never accounted for — shifting
            // every subsequent instruction and corrupting THIS displacement and
            // any branch spanning it. That was a silent latent miscompile for
            // large functions; decline to the direct selector (whose label-form
            // resolution re-runs after layout) instead.
            let fits_short = if is_conditional {
                // 16-bit B<cond> (T1): imm8, -256..+254 bytes = -128..=127 hw
                (-128..=127).contains(&halfword_offset)
            } else {
                // 16-bit B (T2): imm11, -2048..+2044 bytes = -1024..=1022 hw
                (-1024..=1022).contains(&halfword_offset)
            };
            if !fits_short {
                return Err(Error::synthesis(format!(
                    "optimized path: resolved branch displacement {halfword_offset} \
                     halfwords exceeds the 2-byte Thumb short form the offset table \
                     assumed (#498 far-branch); falling back to direct selector"
                )));
            }

            // Patch the branch instruction
            if is_conditional {
                arm_instrs[branch_arm_idx] = ArmOp::BCondOffset {
                    cond: crate::rules::Condition::NE,
                    offset: halfword_offset,
                };
            } else {
                arm_instrs[branch_arm_idx] = ArmOp::BOffset {
                    offset: halfword_offset,
                };
            }
        }

        // Ensure the return value is in R0 (i32 result) or R0:R1 (i64 result).
        //
        // Pre-fix, every i64 op pinned its result at R0:R1 so this could be a
        // no-op for is_i64_result. After the fix, the result pair may live in
        // any callee-saved pair (R4:R5..R10:R11), and we need an explicit move.
        // The order matters: copy hi → R1 first, then lo → R0, so we don't
        // clobber the lo value if the source happens to be R1.
        if spill_on_exhaust
            && is_i64_result
            && let Some(vl) = last_result_vreg
            && let Some(vh) = last_result_vreg_hi
            && let (Some(&slot_lo), Some(&slot_hi)) =
                (spilled_vregs.get(&vl), spilled_vregs.get(&vh))
        {
            // VCR-RA #587: the final i64 result pair was evicted AFTER its def
            // (the epilogue read is invisible to the linear next-use table,
            // which is why pair eviction always STRs both halves). Reload the
            // pair from its 8-byte slot straight into the AAPCS return pair.
            arm_instrs.push(ArmOp::Ldr {
                rd: Reg::R0,
                addr: crate::rules::MemAddr::imm(Reg::SP, slot_lo),
            });
            arm_instrs.push(ArmOp::Ldr {
                rd: Reg::R1,
                addr: crate::rules::MemAddr::imm(Reg::SP, slot_hi),
            });
        } else if is_i64_result {
            // Resolve the lo half from vreg_to_arm.
            let lo_reg = last_result_vreg.and_then(|v| vreg_to_arm.get(&v).copied());
            // Resolve the hi half: prefer an explicit vreg id, else fall back to
            // the physical reg stash used by Clz/Ctz/Popcnt.
            let hi_reg = last_result_vreg_hi
                .and_then(|v| vreg_to_arm.get(&v).copied())
                .or(last_result_vreg_hi_reg);

            if let (Some(lo), Some(hi)) = (lo_reg, hi_reg) {
                // Move hi first (so we don't clobber lo if hi's source is R1).
                if hi != Reg::R1 {
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R1,
                        op2: Operand2::Reg(hi),
                    });
                }
                // Now move lo. If lo was R1 originally, it just got smashed by
                // the hi-move above; but R1's prior contents are now in R1
                // (the hi value), so we'd actually have wanted to save lo first.
                // Handle that case explicitly: save lo to R12 (IP scratch) first.
                if lo == Reg::R1 && hi != Reg::R1 {
                    // lo was in R1, which we just overwrote. We can't recover it
                    // unless we saved earlier. The clean fix: detect this
                    // arrangement up front. For now, swap order via R12.
                    // (This is reached only on bizarre regalloc choices; the
                    // common case is lo in R4..R10, which doesn't hit it.)
                    arm_instrs.pop(); // remove the hi-move we just emitted
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R12,
                        op2: Operand2::Reg(lo),
                    });
                    if hi != Reg::R1 {
                        arm_instrs.push(ArmOp::Mov {
                            rd: Reg::R1,
                            op2: Operand2::Reg(hi),
                        });
                    }
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R0,
                        op2: Operand2::Reg(Reg::R12),
                    });
                } else if lo != Reg::R0 {
                    arm_instrs.push(ArmOp::Mov {
                        rd: Reg::R0,
                        op2: Operand2::Reg(lo),
                    });
                }
            } else if let Some(lo) = lo_reg
                && lo != Reg::R0
            {
                // Hi is unknown — fall back to single-register move (caller of
                // this function may have set is_i64_result without populating
                // the hi tracker; preserve old behaviour rather than crash).
                arm_instrs.push(ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Reg(lo),
                });
            }
        } else if let Some(result_vreg) = last_result_vreg
            && let Some(&result_reg) = vreg_to_arm.get(&result_vreg)
            && result_reg != Reg::R0
        {
            arm_instrs.push(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(result_reg),
            });
        } else if spill_on_exhaust
            && let Some(result_vreg) = last_result_vreg
            && let Some(&slot) = spilled_vregs.get(&result_vreg)
        {
            // VCR-RA-001 (#242): the final result was evicted AFTER its def
            // (this epilogue read is invisible to the linear next-use table,
            // which is why eviction always STRs, never drops). Reload it
            // straight into R0 from its frame slot.
            arm_instrs.push(ArmOp::Ldr {
                rd: Reg::R0,
                addr: crate::rules::MemAddr::imm(Reg::SP, slot),
            });
        }

        // If any registers were spilled, insert stack frame setup/teardown.
        // Prologue: SUB SP, SP, #frame_size at the beginning
        // Epilogue: ADD SP, SP, #frame_size before every BX LR
        //
        // Gate on `next_spill_offset` (monotonic), not `spilled_vregs` (with
        // SYNTH_SPILL_ON_EXHAUST reinstated vregs are REMOVED from the map, but
        // their STR/LDR slots still need the frame). Flag-off the two are
        // equivalent: nothing ever leaves `spilled_vregs`, so `offset > 4` ⟺
        // `!spilled_vregs.is_empty()` — byte-identical.
        if next_spill_offset > 4 {
            // Round frame size up to 8-byte alignment (AAPCS requirement)
            let frame_size = ((next_spill_offset as u32 + 7) & !7) as i32;
            // Insert prologue at position 0
            arm_instrs.insert(
                0,
                ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(frame_size),
                },
            );
            // Add epilogue before each BX LR (scan for existing returns)
            let mut i = 1; // skip the prologue we just inserted
            while i < arm_instrs.len() {
                if matches!(&arm_instrs[i], ArmOp::Bx { rm: Reg::LR }) {
                    arm_instrs.insert(
                        i,
                        ArmOp::Add {
                            rd: Reg::SP,
                            rn: Reg::SP,
                            op2: Operand2::Imm(frame_size),
                        },
                    );
                    i += 2; // skip both the ADD and the BX
                } else {
                    i += 1;
                }
            }
        }

        // Add return if not present
        if arm_instrs.is_empty() || !matches!(arm_instrs.last(), Some(ArmOp::Bx { .. })) {
            // #499: the spill-frame block above only inserts the `ADD SP`
            // epilogue before returns that ALREADY exist; a return appended
            // here must also deallocate the frame, or SP returns off by the
            // frame size and the `pop {…, pc}` epilogue (#490) reads PC from
            // a spill slot. This was previously gated on `spill_on_exhaust`
            // under the belief that a flag-off spill implied scratch-pool
            // exhaustion (which declines the function) — false: the
            // `Opcode::Const` allocator has its own oldest-vreg eviction
            // spill on R4-R11/R3 pool exhaustion that never sets
            // `r12_exhausted`, so functions that fall off the end (the common
            // wasm shape: no explicit `return`) shipped with an imbalanced SP.
            if next_spill_offset > 4 {
                let frame_size = ((next_spill_offset as u32 + 7) & !7) as i32;
                arm_instrs.push(ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(frame_size),
                });
            }
            arm_instrs.push(ArmOp::Bx { rm: Reg::LR });
        }

        // #499 defensive post-condition (internal-bug panic pattern): if a
        // spill frame was allocated, EVERY return must be immediately preceded
        // by the exact `ADD SP, SP, #frame_size` teardown. The prologue is the
        // only `SUB SP` and the epilogue inserts the only `ADD SP`s, so the
        // "immediately preceding instruction" check is precise — any return
        // this scan flags would ship an SP-imbalanced function.
        if next_spill_offset > 4 {
            let frame_size = ((next_spill_offset as u32 + 7) & !7) as i32;
            for (i, op) in arm_instrs.iter().enumerate() {
                if matches!(op, ArmOp::Bx { rm: Reg::LR }) {
                    let deallocated = i > 0
                        && matches!(
                            &arm_instrs[i - 1],
                            ArmOp::Add {
                                rd: Reg::SP,
                                rn: Reg::SP,
                                op2: Operand2::Imm(n),
                            } if *n == frame_size
                        );
                    assert!(
                        deallocated,
                        "internal error (#499): return at instruction {i} does not \
                         deallocate the {frame_size}-byte spill frame — SP would \
                         return imbalanced and `pop {{…, pc}}` would read PC from \
                         a spill slot. This is an optimizer_bridge epilogue bug."
                    );
                }
            }
        }

        // #490: the callee-saved prologue/epilogue the optimized path needs to
        // honour AAPCS is added AFTER range-realloc (in `arm_backend`), where the
        // re-allocated body shows which callee-saved registers are *genuinely*
        // live — realloc lowers low-pressure r4-r8 scratch back to r0-r3, so a
        // decision here (pre-realloc) would over-save. See
        // `liveness::ensure_callee_saved_prologue`.

        // #496: if any scratch allocation exhausted the R4-R8 pool and fell back to
        // R12/IP (or the i64 (R4,R5) alias), the body we just built contains a
        // latent miscompile (R12 is the encoder's indexed-load base scratch).
        // Decline the whole function to the direct selector, which has real
        // spill-on-exhaustion support (`instruction_selector`); `arm_backend`
        // catches this `Err` and retries via `select_direct`. This is a
        // correctness retreat, not a perf win — keeping these functions on the
        // optimized path requires proper spilling there, the VCR-RA follow-up.
        if r12_exhausted.get() {
            return Err(Error::UnsupportedInstruction(
                "optimized path: R4-R8 scratch pool exhausted — declining to the \
                 direct selector for correct spilling (#496)"
                    .to_string(),
            ));
        }

        Ok((arm_instrs, exhaust_acted, guards_elided))
    }
}

// ---------------------------------------------------------------------------
// VCR-RA-001 allocation-time spill-on-exhaustion (#242, closes the #496
// hard-fail for straight-line i32 functions). Helpers for the flag-gated
// pre-step in `ir_to_arm`: when the R4-R8 scratch pool is exhausted, spill the
// live vreg with the FARTHEST next use (Belady) to a fresh frame slot instead
// of declining the whole function to the direct selector.
// ---------------------------------------------------------------------------

/// The register pool `alloc_i32_scratch` draws from. The spill pre-step frees
/// registers in exactly this pool (and only this pool — params live in R0-R3,
/// R9/R10/R11/R12 are reserved conventions the optimized path must not touch).
const SPILL_ON_EXHAUST_POOL: [crate::rules::Reg; 5] = [
    crate::rules::Reg::R4,
    crate::rules::Reg::R5,
    crate::rules::Reg::R6,
    crate::rules::Reg::R7,
    crate::rules::Reg::R8,
];

/// The CONSECUTIVE even-aligned register pairs `alloc_i64_pair` searches, in
/// search order. The #587 pair-spill pre-step frees and reloads pairs from
/// exactly this list — sharing the const (instead of mirroring it) pins the
/// two against drift. R9/R10/R11 appear here because `alloc_i64_pair` has
/// always handed them out; functions whose lowering RESERVES them (globals
/// base R9, memory-size R10 — see `spill_on_exhaust_scope_ok`) decline the
/// lever wholesale.
const SPILL_I64_PAIR_CANDIDATES: [(crate::rules::Reg, crate::rules::Reg); 4] = [
    (crate::rules::Reg::R4, crate::rules::Reg::R5),
    (crate::rules::Reg::R6, crate::rules::Reg::R7),
    (crate::rules::Reg::R8, crate::rules::Reg::R9),
    (crate::rules::Reg::R10, crate::rules::Reg::R11),
];

/// Whether the allocation-time spill pre-step models `op`. ONE unsupported
/// opcode disables the pre-step for the whole function, preserving the #496
/// decline-to-direct-selector behaviour for those shapes. Deliberately narrow
/// (honest scope):
///
/// - **i64 family (#587)**: only lowerings whose register discipline the pair
///   model covers — pair-allocating producers (`I64Const`/`I64Add`/`I64Sub`/
///   `I64And`/`I64Or`/`I64Xor`/`I64Mul`), the pair-allocating comparisons +
///   `I64Eqz`, the i32↔i64 conversions, and PARAM `I64Load`. Excluded: i64
///   shifts/rotates (their encoders clobber the shift-amount pair in place,
///   so a spilled-then-reloaded amount would re-materialize a value the
///   flag-off path treats as consumed), div/rem, `I64Clz`/`Ctz`/`Popcnt`
///   (their hi half is a physical reg with no IR vreg), the narrowing
///   extends, and non-param i64 locals. All of these keep the #496 decline.
/// - **no control flow** (`Branch`/`CondBranch`): the Belady next-use table is
///   linear — a back-edge would make "next use" wrong and a reload could be
///   skipped on a re-entered path. (`Label` alone is fine: with no branches it
///   is inert.)
/// - **no calls**: import calls stay on the optimized path today, but the
///   dispatch lowering has its own scratch conventions; keep the pre-step out
///   of its way.
/// - **no non-param locals** (except the synthetic select-condition local 255,
///   which is pinned to R11, outside the pool): non-param locals are pinned to
///   R4-R7 by `local_to_reg`, and the pre-pass premapping interacts with the
///   pool in ways v1 does not model.
///
/// Per-function constraints (pair-map unambiguity, no R9/R10 reservations
/// alongside i64) live in `spill_on_exhaust_scope_ok` /
/// `spill_pair_partner_map`.
fn spill_on_exhaust_supported(op: &Opcode, num_params: usize) -> bool {
    let param_local = |addr: u32| (addr as usize) < num_params || addr == 255;
    match op {
        Opcode::Nop
        | Opcode::Label { .. }
        | Opcode::Const { .. }
        | Opcode::Add { .. }
        | Opcode::Sub { .. }
        | Opcode::Mul { .. }
        | Opcode::DivS { .. }
        | Opcode::DivU { .. }
        | Opcode::RemS { .. }
        | Opcode::RemU { .. }
        | Opcode::And { .. }
        | Opcode::Or { .. }
        | Opcode::Xor { .. }
        | Opcode::Shl { .. }
        | Opcode::ShrS { .. }
        | Opcode::ShrU { .. }
        | Opcode::Rotl { .. }
        | Opcode::Rotr { .. }
        | Opcode::Clz { .. }
        | Opcode::Ctz { .. }
        | Opcode::Popcnt { .. }
        | Opcode::Extend8S { .. }
        | Opcode::Extend16S { .. }
        | Opcode::Eqz { .. }
        | Opcode::Eq { .. }
        | Opcode::Ne { .. }
        | Opcode::LtS { .. }
        | Opcode::LtU { .. }
        | Opcode::LeS { .. }
        | Opcode::LeU { .. }
        | Opcode::GtS { .. }
        | Opcode::GtU { .. }
        | Opcode::GeS { .. }
        | Opcode::GeU { .. }
        | Opcode::Select { .. }
        | Opcode::Copy { .. }
        | Opcode::MemLoad { .. }
        | Opcode::MemStore { .. }
        | Opcode::MemLoadSubword { .. }
        | Opcode::MemStoreSubword { .. }
        | Opcode::GlobalGet { .. }
        | Opcode::GlobalSet { .. }
        | Opcode::MemorySize { .. }
        | Opcode::MemoryGrow { .. }
        | Opcode::Return { .. } => true,
        Opcode::Load { addr, .. } | Opcode::Store { addr, .. } => param_local(*addr),
        Opcode::TeeStore { addr, .. } => param_local(*addr),
        // #587: the modeled i64 subset (see doc comment above).
        Opcode::I64Const { .. }
        | Opcode::I64Add { .. }
        | Opcode::I64Sub { .. }
        | Opcode::I64And { .. }
        | Opcode::I64Or { .. }
        | Opcode::I64Xor { .. }
        | Opcode::I64Mul { .. }
        | Opcode::I64Eq { .. }
        | Opcode::I64Ne { .. }
        | Opcode::I64LtS { .. }
        | Opcode::I64LtU { .. }
        | Opcode::I64LeS { .. }
        | Opcode::I64LeU { .. }
        | Opcode::I64GtS { .. }
        | Opcode::I64GtU { .. }
        | Opcode::I64GeS { .. }
        | Opcode::I64GeU { .. }
        | Opcode::I64Eqz { .. }
        | Opcode::I64ExtendI32U { .. }
        | Opcode::I64ExtendI32S { .. }
        | Opcode::I32WrapI64 { .. } => true,
        // PARAM i64 loads bind the AAPCS pair (R0:R1 / R2:R3, outside every
        // spill pool) — mirror the handler's classification EXACTLY.
        // Non-param i64 locals allocate a pinned pair the model does not
        // cover: decline.
        Opcode::I64Load { addr, .. } => {
            (*addr == 0 && num_params >= 2) || (*addr == 1 && num_params >= 4)
        }
        // Everything else — the unmodeled i64 remainder (shifts/rotates,
        // div/rem, clz/ctz/popcnt, narrowing extends), Branch/CondBranch,
        // Call — is out of scope: keep the #496 decline.
        _ => false,
    }
}

/// Function-level scope gate for the spill-on-exhaustion lever (#587): every
/// opcode must be modeled (`spill_on_exhaust_supported`), and if the function
/// touches i64 at all, it must not ALSO reserve R9/R10 by convention
/// (`global.get`/`global.set` address globals off R9; `memory.size` reads
/// R10): `alloc_i64_pair` — and therefore the pair evictor/reloader — hands
/// out (R8,R9) and (R10,R11), which would collide with those bases.
fn spill_on_exhaust_scope_ok(instructions: &[Instruction], num_params: usize) -> bool {
    if !instructions
        .iter()
        .all(|i| spill_on_exhaust_supported(&i.opcode, num_params))
    {
        return false;
    }
    let has_i64 = instructions.iter().any(|i| {
        spill_pair_def(&i.opcode).is_some() || !spill_i64_half_sources(&i.opcode).is_empty()
    });
    !has_i64
        || !instructions.iter().any(|i| {
            matches!(
                &i.opcode,
                Opcode::GlobalGet { .. } | Opcode::GlobalSet { .. } | Opcode::MemorySize { .. }
            )
        })
}

/// The (lo, hi) vreg pair `op` DEFINES, when its lowering binds an i64 value
/// to a register pair. Param `I64Load` is included: its halves live in
/// R0:R1/R2:R3 (outside every candidate pair, so never evicted), but mapping
/// them keeps the pair model total over i64 values.
fn spill_pair_def(op: &Opcode) -> Option<(u32, u32)> {
    match op {
        Opcode::I64Const {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64Load {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64Add {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64Sub {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64And {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64Or {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64Xor {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64Mul {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64ExtendI32U {
            dest_lo, dest_hi, ..
        }
        | Opcode::I64ExtendI32S {
            dest_lo, dest_hi, ..
        } => Some((dest_lo.0, dest_hi.0)),
        _ => None,
    }
}

/// Build the half-vreg → (partner, is_lo) map from the IR pair defs (#587).
/// `None` when the map would be ambiguous — a vreg re-used across two
/// different pairs (or a degenerate lo==hi def): reloading such a pair could
/// pick the wrong partner, so the lever declines for the whole function.
/// (The extend convention `dest_lo == src` re-uses ONE vreg across an i32 and
/// its later i64-lo life, which is fine — ambiguity only arises from two
/// conflicting PAIR memberships.)
fn spill_pair_partner_map(
    instructions: &[Instruction],
) -> Option<std::collections::HashMap<u32, (u32, bool)>> {
    let mut m: std::collections::HashMap<u32, (u32, bool)> = std::collections::HashMap::new();
    for i in instructions {
        if let Some((lo, hi)) = spill_pair_def(&i.opcode) {
            if lo == hi {
                return None;
            }
            for (v, entry) in [(lo, (hi, true)), (hi, (lo, false))] {
                match m.insert(v, entry) {
                    Some(prev) if prev != entry => return None,
                    _ => {}
                }
            }
        }
    }
    Some(m)
}

/// The i64 half vregs (and conversion i32 sources) `op`'s lowering reads from
/// registers — the pair-side complement of [`spill_i32_sources`]. Feeds the
/// Belady next-use table and the pre-step's reinstatement loop. Exhaustive
/// over the i64 opcodes [`spill_on_exhaust_supported`] admits.
fn spill_i64_half_sources(op: &Opcode) -> Vec<u32> {
    match op {
        Opcode::I64Add {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64Sub {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64And {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64Or {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64Xor {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64Mul {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64Eq {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64Ne {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64LtS {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64LtU {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64LeS {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64LeU {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64GtS {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64GtU {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64GeS {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        }
        | Opcode::I64GeU {
            src1_lo,
            src1_hi,
            src2_lo,
            src2_hi,
            ..
        } => vec![src1_lo.0, src1_hi.0, src2_lo.0, src2_hi.0],
        Opcode::I64Eqz { src_lo, src_hi, .. } => vec![src_lo.0, src_hi.0],
        Opcode::I64ExtendI32U { src, .. } | Opcode::I64ExtendI32S { src, .. } => vec![src.0],
        // Wrap reads only the lo half; if the pair was spilled, the
        // reinstatement loop finds the partner through `pair_partner`.
        Opcode::I32WrapI64 { src_lo, .. } => vec![src_lo.0],
        _ => Vec::new(),
    }
}

/// Whether `op`'s handler calls `alloc_i64_pair` for its destination — the
/// i64 producers AND the i64 comparisons/`I64Eqz` (whose i32 result binds the
/// lo half of a freshly allocated pair). Used by the pre-step to guarantee a
/// free candidate pair BEFORE the handler runs, so `alloc_i64_pair` never
/// reaches its (R4,R5) exhaustion fallback. The call site refines `I64Const`
/// with the #94 skip-set (a folded const allocates nothing). Param `I64Load`
/// binds AAPCS registers and allocates nothing.
fn spill_needs_pair_alloc(op: &Opcode) -> bool {
    matches!(
        op,
        Opcode::I64Const { .. }
            | Opcode::I64Add { .. }
            | Opcode::I64Sub { .. }
            | Opcode::I64And { .. }
            | Opcode::I64Or { .. }
            | Opcode::I64Xor { .. }
            | Opcode::I64Mul { .. }
            | Opcode::I64Eq { .. }
            | Opcode::I64Ne { .. }
            | Opcode::I64LtS { .. }
            | Opcode::I64LtU { .. }
            | Opcode::I64LeS { .. }
            | Opcode::I64LeU { .. }
            | Opcode::I64GtS { .. }
            | Opcode::I64GtU { .. }
            | Opcode::I64GeS { .. }
            | Opcode::I64GeU { .. }
            | Opcode::I64Eqz { .. }
            | Opcode::I64ExtendI32U { .. }
            | Opcode::I64ExtendI32S { .. }
    )
}

/// A candidate pair that is free by `alloc_i64_pair`'s in-use rule (every
/// mapped vreg counts, dead or not) and clear of `avoid` (operands of the
/// current instruction, including registers being reloaded into).
fn find_free_spill_pair(
    vreg_to_arm: &std::collections::HashMap<u32, crate::rules::Reg>,
    local_to_reg: &std::collections::HashMap<u32, crate::rules::Reg>,
    param_reserved_regs: &[crate::rules::Reg],
    avoid: &[crate::rules::Reg],
) -> Option<(crate::rules::Reg, crate::rules::Reg)> {
    let in_use = |r: crate::rules::Reg| -> bool {
        vreg_to_arm.values().any(|&u| u == r)
            || local_to_reg.values().any(|&u| u == r)
            || param_reserved_regs.contains(&r)
            || avoid.contains(&r)
    };
    SPILL_I64_PAIR_CANDIDATES
        .iter()
        .copied()
        .find(|&(lo, hi)| !in_use(lo) && !in_use(hi))
}

/// The i32 SOURCE vregs `op`'s lowering reads from registers. Used to (a)
/// build the Belady next-use table and (b) reinstate spilled sources before
/// the handler runs. Exhaustive over the opcodes
/// [`spill_on_exhaust_supported`] admits.
fn spill_i32_sources(op: &Opcode) -> Vec<u32> {
    match op {
        Opcode::Add { src1, src2, .. }
        | Opcode::Sub { src1, src2, .. }
        | Opcode::Mul { src1, src2, .. }
        | Opcode::DivS { src1, src2, .. }
        | Opcode::DivU { src1, src2, .. }
        | Opcode::RemS { src1, src2, .. }
        | Opcode::RemU { src1, src2, .. }
        | Opcode::And { src1, src2, .. }
        | Opcode::Or { src1, src2, .. }
        | Opcode::Xor { src1, src2, .. }
        | Opcode::Shl { src1, src2, .. }
        | Opcode::ShrS { src1, src2, .. }
        | Opcode::ShrU { src1, src2, .. }
        | Opcode::Rotl { src1, src2, .. }
        | Opcode::Rotr { src1, src2, .. }
        | Opcode::Eq { src1, src2, .. }
        | Opcode::Ne { src1, src2, .. }
        | Opcode::LtS { src1, src2, .. }
        | Opcode::LtU { src1, src2, .. }
        | Opcode::LeS { src1, src2, .. }
        | Opcode::LeU { src1, src2, .. }
        | Opcode::GtS { src1, src2, .. }
        | Opcode::GtU { src1, src2, .. }
        | Opcode::GeS { src1, src2, .. }
        | Opcode::GeU { src1, src2, .. } => vec![src1.0, src2.0],
        Opcode::Clz { src, .. }
        | Opcode::Ctz { src, .. }
        | Opcode::Popcnt { src, .. }
        | Opcode::Extend8S { src, .. }
        | Opcode::Extend16S { src, .. }
        | Opcode::Eqz { src, .. }
        | Opcode::Copy { src, .. }
        | Opcode::Store { src, .. }
        | Opcode::TeeStore { src, .. }
        | Opcode::GlobalSet { src, .. } => vec![src.0],
        Opcode::Select {
            val_true,
            val_false,
            cond,
            ..
        } => vec![val_true.0, val_false.0, cond.0],
        Opcode::MemLoad { addr, .. } | Opcode::MemLoadSubword { addr, .. } => vec![addr.0],
        Opcode::MemStore { src, addr, .. } | Opcode::MemStoreSubword { src, addr, .. } => {
            vec![src.0, addr.0]
        }
        Opcode::MemoryGrow { delta, .. } => vec![delta.0],
        Opcode::Return { value } => value.iter().map(|v| v.0).collect(),
        // No register sources (Const/Load/GlobalGet/MemorySize/Nop/Label) or
        // out of the supported set (the pre-step is disabled for those
        // functions anyway).
        _ => Vec::new(),
    }
}

/// The i32 dest vreg whose register `op`'s handler allocates via
/// `alloc_i32_scratch` (None when the handler needs no fresh scratch dest —
/// `Const` has its own, larger pool with eviction; `Load`/`Call` bind fixed
/// registers). Used by the pre-step to free a pool register BEFORE the handler
/// runs, so `alloc_i32_scratch` never reaches its R12 exhaustion fallback.
/// EVERY vreg `op` defines, total over the spill-on-exhaust modeled subset
/// ([`spill_on_exhaust_supported`]) — or `None` for anything outside it.
/// Used by the VCR-VER-001 single-def `Const` scan: the divisor-guard elision
/// must see every def (a missed redefinition could smuggle a stale constant),
/// so a single `None` disables the whole map — decline-to-empty, never a
/// wrong value.
fn spill_exhaust_defs(op: &Opcode) -> Option<Vec<u32>> {
    // i32 scratch dests + the local-backed `Load`/`TeeStore` dests.
    if let Opcode::Load { dest, .. } | Opcode::TeeStore { dest, .. } = op {
        return Some(vec![dest.0]);
    }
    if let Some(d) = spill_i32_scratch_dest(op) {
        return Some(vec![d]);
    }
    // i64 pair defs (I64Const/Load/Add/.../Extend).
    if let Some((lo, hi)) = spill_pair_def(op) {
        return Some(vec![lo, hi]);
    }
    match op {
        // i64 ops with an i32 destination.
        Opcode::I64Eq { dest, .. }
        | Opcode::I64Ne { dest, .. }
        | Opcode::I64LtS { dest, .. }
        | Opcode::I64LtU { dest, .. }
        | Opcode::I64LeS { dest, .. }
        | Opcode::I64LeU { dest, .. }
        | Opcode::I64GtS { dest, .. }
        | Opcode::I64GtU { dest, .. }
        | Opcode::I64GeS { dest, .. }
        | Opcode::I64GeU { dest, .. }
        | Opcode::I64Eqz { dest, .. }
        | Opcode::I32WrapI64 { dest, .. } => Some(vec![dest.0]),
        // Modeled ops that define no vreg.
        Opcode::Nop
        | Opcode::Label { .. }
        | Opcode::Store { .. }
        | Opcode::MemStore { .. }
        | Opcode::MemStoreSubword { .. }
        | Opcode::GlobalSet { .. }
        | Opcode::Return { .. } => Some(vec![]),
        // Anything else: not enumerable here — disable the const map.
        _ => None,
    }
}

fn spill_i32_scratch_dest(op: &Opcode) -> Option<u32> {
    match op {
        Opcode::Add { dest, .. }
        | Opcode::Sub { dest, .. }
        | Opcode::Mul { dest, .. }
        | Opcode::DivS { dest, .. }
        | Opcode::DivU { dest, .. }
        | Opcode::RemS { dest, .. }
        | Opcode::RemU { dest, .. }
        | Opcode::And { dest, .. }
        | Opcode::Or { dest, .. }
        | Opcode::Xor { dest, .. }
        | Opcode::Shl { dest, .. }
        | Opcode::ShrS { dest, .. }
        | Opcode::ShrU { dest, .. }
        | Opcode::Rotl { dest, .. }
        | Opcode::Rotr { dest, .. }
        | Opcode::Clz { dest, .. }
        | Opcode::Ctz { dest, .. }
        | Opcode::Popcnt { dest, .. }
        | Opcode::Extend8S { dest, .. }
        | Opcode::Extend16S { dest, .. }
        | Opcode::Eqz { dest, .. }
        | Opcode::Eq { dest, .. }
        | Opcode::Ne { dest, .. }
        | Opcode::LtS { dest, .. }
        | Opcode::LtU { dest, .. }
        | Opcode::LeS { dest, .. }
        | Opcode::LeU { dest, .. }
        | Opcode::GtS { dest, .. }
        | Opcode::GtU { dest, .. }
        | Opcode::GeS { dest, .. }
        | Opcode::GeU { dest, .. }
        | Opcode::Select { dest, .. }
        | Opcode::Copy { dest, .. }
        | Opcode::MemLoad { dest, .. }
        | Opcode::MemLoadSubword { dest, .. }
        | Opcode::GlobalGet { dest, .. }
        | Opcode::MemorySize { dest }
        | Opcode::MemoryGrow { dest, .. } => Some(dest.0),
        // `Const` has its own allocator with a LARGER pool (R4-R8, then
        // R9/R10/R11, then R3) and its own oldest-first eviction. Covering it
        // here guarantees one of R4-R8 is free before the handler runs, so its
        // `find` never reaches R9/R10/R11 (reserved conventions: globals base,
        // memory size, base-CSE) nor the R3 last-resort clobber — both of
        // which are only safe today because exhausted functions decline.
        Opcode::Const { dest, .. } => Some(dest.0),
        _ => None,
    }
}

/// Spill the live pool vreg with the FARTHEST next use (Belady) to a fresh
/// frame slot, freeing its register. Returns the freed register, or `None`
/// when no vreg is evictable (everything in the pool is pinned: locals,
/// premapped param/local vregs, aliased registers, i64 pair halves, or
/// `avoid`-listed operands of the current instruction) — the caller then
/// leaves `alloc_i32_scratch` to its flag-off exhaustion fallback, which
/// flags the function for the #496 decline. Every victim gets a `STR` (never
/// drop-without-store): the victim may be the function's final result, read
/// by the epilogue after the last instruction, which the linear next-use
/// table cannot see.
#[allow(clippy::too_many_arguments)]
fn spill_evict_farthest(
    pool: &[crate::rules::Reg],
    cur_idx: usize,
    avoid: &[crate::rules::Reg],
    use_positions: &std::collections::HashMap<u32, Vec<usize>>,
    local_vregs: &std::collections::HashSet<u32>,
    premapped_vregs: &std::collections::HashSet<u32>,
    pair_partner: &std::collections::HashMap<u32, (u32, bool)>,
    local_to_reg: &std::collections::HashMap<u32, crate::rules::Reg>,
    param_reserved_regs: &[crate::rules::Reg],
    vreg_to_arm: &mut std::collections::HashMap<u32, crate::rules::Reg>,
    spilled_vregs: &mut std::collections::HashMap<u32, i32>,
    next_spill_offset: &mut i32,
    arm_instrs: &mut Vec<ArmOp>,
) -> Option<crate::rules::Reg> {
    use crate::rules::Reg;
    // Deterministic candidate order: sort by vreg id (HashMap iteration order
    // must never influence emitted bytes). `pool` is the register set whose
    // freeing helps the caller: the widened reload pool for source
    // reinstatement, exactly `SPILL_ON_EXHAUST_POOL` for dest pre-freeing
    // (`alloc_i32_scratch` cannot draw from R2/R3 — VCR-VER-001).
    let mut candidates: Vec<(u32, Reg)> = vreg_to_arm
        .iter()
        .map(|(&v, &r)| (v, r))
        .filter(|&(v, r)| {
            pool.contains(&r)
                && !local_vregs.contains(&v)
                && !premapped_vregs.contains(&v)
                // #587 pair guard: i64 halves are only ever spilled as
                // coherent pairs (8-byte slot pair, `spill_evict_pair_farthest`)
                // — a half spilled alone here would break the pair-reload
                // invariant (the #518 class of bug).
                && !pair_partner.contains_key(&v)
                && !local_to_reg.values().any(|&u| u == r)
                && !param_reserved_regs.contains(&r)
                && !avoid.contains(&r)
                // Alias guard: only evict a register held by exactly ONE vreg.
                // The inline const-CSE aliasing that could make two live vregs
                // share a register is RETIRED (#242 — const-CSE is now only
                // the post-hoc `liveness::apply_const_cse`), so today the
                // vreg↔reg map is a bijection by construction; the guard stays
                // as a cheap structural tripwire (spilling a shared victim
                // would leave the other alias reading a reused register).
                && vreg_to_arm.values().filter(|&&u| u == r).count() == 1
        })
        .collect();
    candidates.sort_by_key(|&(v, _)| v);
    // Belady: farthest next use wins; a vreg with NO next use (usize::MAX) is
    // the ideal victim. Ties broken by the sort above (lowest vreg id).
    let (victim, victim_reg) = candidates.into_iter().max_by_key(|&(v, _)| {
        use_positions
            .get(&v)
            .and_then(|ps| ps.iter().find(|&&p| p >= cur_idx))
            .copied()
            .unwrap_or(usize::MAX)
    })?;
    let offset = *next_spill_offset;
    *next_spill_offset += 4;
    arm_instrs.push(ArmOp::Str {
        rd: victim_reg,
        addr: crate::rules::MemAddr::imm(Reg::SP, offset),
    });
    spilled_vregs.insert(victim, offset);
    vreg_to_arm.remove(&victim);
    Some(victim_reg)
}

/// What one candidate-pair eviction displaces (#587): a coherent i64 PAIR
/// (both halves, wherever their registers are — sources need no adjacency,
/// only dests do), or an independent i32 single.
enum SpillEvictUnit {
    Pair(u32, u32), // (lo vreg, hi vreg)
    Single(u32),
}

/// Free one legal even pair from `SPILL_I64_PAIR_CANDIDATES` by evicting what
/// occupies it — either (a) a live i64 PAIR, or (b) up to two independent
/// singles — choosing the candidate whose displaced values have the FARTHEST
/// soonest-next-use (pair-aware Belady: the cost of an eviction is dominated
/// by the value needed soonest, so maximize that minimum). Deterministic
/// tie-break: first candidate in the fixed search order wins.
///
/// Returns the freed `(lo, hi)` pair, or `None` when no candidate is fully
/// evictable (pinned locals/params/aliases/avoid-listed operands, or a
/// half-defined pair) — the caller then falls through to the #496 decline.
///
/// Pair victims get an 8-byte-aligned slot pair (lo at `off`, hi at `off+4` —
/// the #325 direct-path pair-spill convention) and BOTH halves are STR'd;
/// singles get the usual 4-byte slot. Never drop-without-store, for the same
/// epilogue-read reason as the single evictor.
#[allow(clippy::too_many_arguments)]
fn spill_evict_pair_farthest(
    cur_idx: usize,
    avoid: &[crate::rules::Reg],
    use_positions: &std::collections::HashMap<u32, Vec<usize>>,
    local_vregs: &std::collections::HashSet<u32>,
    premapped_vregs: &std::collections::HashSet<u32>,
    pair_partner: &std::collections::HashMap<u32, (u32, bool)>,
    local_to_reg: &std::collections::HashMap<u32, crate::rules::Reg>,
    param_reserved_regs: &[crate::rules::Reg],
    vreg_to_arm: &mut std::collections::HashMap<u32, crate::rules::Reg>,
    spilled_vregs: &mut std::collections::HashMap<u32, i32>,
    next_spill_offset: &mut i32,
    arm_instrs: &mut Vec<ArmOp>,
) -> Option<(crate::rules::Reg, crate::rules::Reg)> {
    use crate::rules::Reg;
    let next_use = |v: u32| -> usize {
        use_positions
            .get(&v)
            .and_then(|ps| ps.iter().find(|&&p| p >= cur_idx))
            .copied()
            .unwrap_or(usize::MAX)
    };
    // Deterministic occupant lookup (sorted by vreg id; only the aliased case
    // has >1 occupant and that disqualifies the candidate anyway).
    let occupants = |map: &std::collections::HashMap<u32, Reg>, r: Reg| -> Vec<u32> {
        let mut o: Vec<u32> = map
            .iter()
            .filter(|&(_, &u)| u == r)
            .map(|(&v, _)| v)
            .collect();
        o.sort_unstable();
        o
    };
    // A register may be displaced at all?
    let reg_pinned = |r: Reg| -> bool {
        local_to_reg.values().any(|&u| u == r)
            || param_reserved_regs.contains(&r)
            || avoid.contains(&r)
    };
    let vreg_pinned = |v: u32| -> bool { local_vregs.contains(&v) || premapped_vregs.contains(&v) };

    let mut best: Option<(usize, usize, Vec<SpillEvictUnit>)> = None;
    'cand: for (ci, &(p_lo, p_hi)) in SPILL_I64_PAIR_CANDIDATES.iter().enumerate() {
        let mut units: Vec<SpillEvictUnit> = Vec::new();
        for r in [p_lo, p_hi] {
            if reg_pinned(r) {
                continue 'cand;
            }
            let occ = occupants(vreg_to_arm, r);
            match occ.as_slice() {
                [] => {}
                [v] => {
                    let v = *v;
                    if vreg_pinned(v) {
                        continue 'cand;
                    }
                    if let Some(&(partner, is_lo)) = pair_partner.get(&v) {
                        // Whole-pair unit: the partner half (wherever it
                        // lives) must be displaceable too. A half-defined
                        // pair (partner not yet mapped — the extend
                        // convention re-uses the i32 src vreg as dest_lo
                        // before dest_hi exists) is conservatively pinned.
                        let Some(&pr) = vreg_to_arm.get(&partner) else {
                            continue 'cand;
                        };
                        if vreg_pinned(partner)
                            || reg_pinned(pr)
                            || occupants(vreg_to_arm, pr).len() != 1
                        {
                            continue 'cand;
                        }
                        let (v_lo, v_hi) = if is_lo { (v, partner) } else { (partner, v) };
                        // Both candidate registers may hold the same pair —
                        // one unit, not two.
                        if !units
                            .iter()
                            .any(|u| matches!(u, SpillEvictUnit::Pair(l, _) if *l == v_lo))
                        {
                            units.push(SpillEvictUnit::Pair(v_lo, v_hi));
                        }
                    } else {
                        units.push(SpillEvictUnit::Single(v));
                    }
                }
                // Aliased register (const-CSE): never evict — the other
                // alias would read a reused register (spill-bijection
                // hazard, same guard as the single evictor).
                _ => continue 'cand,
            }
        }
        // Pair-aware Belady key: the soonest next use across everything this
        // eviction displaces (usize::MAX for dead values or an already-free
        // register). Strict `>` keeps the FIRST best candidate — fixed array
        // order, fully deterministic.
        let key = units
            .iter()
            .flat_map(|u| match u {
                SpillEvictUnit::Pair(l, h) => vec![*l, *h],
                SpillEvictUnit::Single(v) => vec![*v],
            })
            .map(next_use)
            .min()
            .unwrap_or(usize::MAX);
        if best.as_ref().is_none_or(|(bk, _, _)| key > *bk) {
            best = Some((key, ci, units));
        }
    }
    let (_, ci, units) = best?;
    let (p_lo, p_hi) = SPILL_I64_PAIR_CANDIDATES[ci];
    for unit in units {
        match unit {
            SpillEvictUnit::Pair(v_lo, v_hi) => {
                // #325 pair-slot convention: 8-byte aligned, lo then hi.
                *next_spill_offset = (*next_spill_offset + 7) & !7;
                let off = *next_spill_offset;
                *next_spill_offset += 8;
                let r_lo = vreg_to_arm[&v_lo];
                let r_hi = vreg_to_arm[&v_hi];
                arm_instrs.push(ArmOp::Str {
                    rd: r_lo,
                    addr: crate::rules::MemAddr::imm(Reg::SP, off),
                });
                arm_instrs.push(ArmOp::Str {
                    rd: r_hi,
                    addr: crate::rules::MemAddr::imm(Reg::SP, off + 4),
                });
                spilled_vregs.insert(v_lo, off);
                spilled_vregs.insert(v_hi, off + 4);
                vreg_to_arm.remove(&v_lo);
                vreg_to_arm.remove(&v_hi);
            }
            SpillEvictUnit::Single(v) => {
                let off = *next_spill_offset;
                *next_spill_offset += 4;
                let r = vreg_to_arm[&v];
                arm_instrs.push(ArmOp::Str {
                    rd: r,
                    addr: crate::rules::MemAddr::imm(Reg::SP, off),
                });
                spilled_vregs.insert(v, off);
                vreg_to_arm.remove(&v);
            }
        }
    }
    Some((p_lo, p_hi))
}

impl Default for OptimizerBridge {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::Reg;

    // ---- base-CSE planner (VCR-RA lever 3, #468) ----

    fn inst(op: Opcode) -> Instruction {
        Instruction {
            id: 0,
            opcode: op,
            block_id: 0,
            is_dead: false,
        }
    }
    fn vr(n: u32) -> OptReg {
        OptReg(n)
    }
    /// `[Const addr, Const val, MemStore]` triples for `(addr, val)` pairs, using
    /// fresh vregs per pair (single-use addresses, the foldable shape).
    fn const_addr_stores(pairs: &[(i32, i32)]) -> Vec<Instruction> {
        let mut out = Vec::new();
        for (i, (addr, val)) in pairs.iter().enumerate() {
            let av = (i as u32) * 2;
            let vv = av + 1;
            out.push(inst(Opcode::Const {
                dest: vr(av),
                value: *addr,
            }));
            out.push(inst(Opcode::Const {
                dest: vr(vv),
                value: *val,
            }));
            out.push(inst(Opcode::MemStore {
                src: vr(vv),
                addr: vr(av),
                offset: 0,
            }));
        }
        out
    }

    #[test]
    fn plan_base_cse_folds_two_or_more_const_addr_stores() {
        let ir = const_addr_stores(&[(0, 11), (4, 22), (8, 33)]);
        let plan = plan_base_cse(&ir, &[]).expect("activates with 3 foldable stores");
        assert_eq!(plan.fold.len(), 3);
        assert_eq!(plan.skip_const.len(), 3);
        // addr vreg 0 → folded immediate 0; vreg 2 → 4; vreg 4 → 8.
        assert_eq!(plan.fold.get(&0), Some(&0));
        assert_eq!(plan.fold.get(&2), Some(&4));
        assert_eq!(plan.fold.get(&4), Some(&8));
    }

    #[test]
    fn plan_base_cse_declines_below_two_folds() {
        let ir = const_addr_stores(&[(0, 11)]);
        assert_eq!(plan_base_cse(&ir, &[]), None);
    }

    /// #543 Phase 2: accesses inside a marked volatile DMA window are excluded
    /// from the fold set; accesses outside the window still fold (surgical,
    /// per-access back-off — not a whole-function decline).
    #[test]
    fn plan_base_cse_excludes_volatile_window_accesses_543() {
        use synth_core::backend::VolatileRange;
        // addr vregs: 0→0x100, 2→0x104 (window), 4→0x80, 6→0x84 (outside).
        let ir = const_addr_stores(&[(0x100, 11), (0x104, 22), (0x80, 33), (0x84, 44)]);
        let win = [VolatileRange {
            base: 0x100,
            len: 16,
        }];
        let plan = plan_base_cse(&ir, &win).expect("outside accesses still activate the plan");
        assert_eq!(plan.fold.len(), 2, "only the two outside accesses fold");
        assert_eq!(plan.fold.get(&4), Some(&0x80));
        assert_eq!(plan.fold.get(&6), Some(&0x84));
        assert!(
            !plan.fold.contains_key(&0) && !plan.fold.contains_key(&2),
            "window accesses must keep their verbatim per-access codegen"
        );
        assert!(!plan.skip_const.contains(&0) && !plan.skip_const.contains(&2));
    }

    /// #543 Phase 2: if the volatile exclusions leave fewer than two folds the
    /// whole plan declines — byte-identical to base-CSE never running.
    #[test]
    fn plan_base_cse_declines_when_volatile_leaves_below_two_folds_543() {
        use synth_core::backend::VolatileRange;
        let ir = const_addr_stores(&[(0x100, 11), (0x104, 22), (0x80, 33)]);
        let win = [VolatileRange {
            base: 0x100,
            len: 16,
        }];
        assert_eq!(plan_base_cse(&ir, &win), None);
    }

    /// #543 Phase 2: half-open range semantics of the intersection test, with
    /// the conservative 4-byte access window.
    #[test]
    fn intersects_volatile_is_half_open_and_width_conservative_543() {
        use synth_core::backend::VolatileRange;
        let win = [VolatileRange {
            base: 0x100,
            len: 16,
        }];
        // Exactly at the window end [0x110,0x114): no intersection.
        assert!(!intersects_volatile(0x110, &win));
        // Last in-window byte address 0x10F: intersects.
        assert!(intersects_volatile(0x10F, &win));
        // [0xFC,0x100) ends exactly at the base: no intersection.
        assert!(!intersects_volatile(0xFC, &win));
        // [0xFD,0x101) straddles the base: intersects.
        assert!(intersects_volatile(0xFD, &win));
        // u32-boundary range must not wrap (i64 arithmetic).
        let hi = [VolatileRange {
            base: 0xFFFF_FFF0,
            len: 0x10,
        }];
        assert!(intersects_volatile(0xFFFF_FFF4, &hi));
        assert!(!intersects_volatile(0xFFFF_FFE0, &hi));
    }

    /// #543 Phase 2: the STATIC access offset participates in the intersection —
    /// `i32.store offset=12 (i32.const 0xF8)` lands at 0x104, inside the window,
    /// even though the const base 0xF8 is below it.
    #[test]
    fn plan_base_cse_volatile_check_includes_static_offset_543() {
        use synth_core::backend::VolatileRange;
        let mut ir = const_addr_stores(&[(0x80, 33), (0x84, 44)]);
        // Const 0xF8 + access offset 12 → effective address 0x104.
        ir.push(inst(Opcode::Const {
            dest: vr(100),
            value: 0xF8,
        }));
        ir.push(inst(Opcode::Const {
            dest: vr(101),
            value: 55,
        }));
        ir.push(inst(Opcode::MemStore {
            src: vr(101),
            addr: vr(100),
            offset: 12,
        }));
        let win = [VolatileRange {
            base: 0x100,
            len: 16,
        }];
        let plan = plan_base_cse(&ir, &win).expect("the two outside accesses still fold");
        assert_eq!(plan.fold.len(), 2);
        assert!(
            !plan.fold.contains_key(&100),
            "offset-folded effective address 0x104 is in the window → excluded"
        );
        // Without the window the same access folds to 0x104.
        let plan_free = plan_base_cse(&ir, &[]).expect("activates");
        assert_eq!(plan_free.fold.get(&100), Some(&0x104));
    }

    #[test]
    fn plan_base_cse_declines_on_disqualifying_op() {
        // A Select anywhere needs R11 for the synthetic-select temp → decline.
        let mut ir = const_addr_stores(&[(0, 11), (4, 22)]);
        ir.push(inst(Opcode::Select {
            dest: vr(100),
            val_true: vr(101),
            val_false: vr(102),
            cond: vr(103),
        }));
        assert_eq!(plan_base_cse(&ir, &[]), None);
    }

    #[test]
    fn plan_base_cse_declines_on_control_flow() {
        // A `CondBranch` (br_if) makes the function multi-block — outside v1 scope
        // (and clear of the optimized path's separately-tracked multi-block bug).
        let mut ir = const_addr_stores(&[(0, 11), (4, 22)]);
        ir.push(inst(Opcode::CondBranch {
            cond: vr(100),
            target: 0,
        }));
        assert_eq!(plan_base_cse(&ir, &[]), None);
    }

    #[test]
    fn plan_base_cse_allows_trailing_structural_label() {
        // A bare `Label` (the function-end marker with nothing branching to it)
        // does NOT split control flow, so base-CSE still activates.
        let mut ir = const_addr_stores(&[(0, 11), (4, 22)]);
        ir.push(inst(Opcode::Label { id: 99 }));
        let plan = plan_base_cse(&ir, &[]).expect("activates despite a structural label");
        assert_eq!(plan.fold.len(), 2);
    }

    #[test]
    fn plan_base_cse_declines_imm12_overflow_addr() {
        // 0x1000 + 0 exceeds the imm12 window → that access does not fold; with
        // only one other foldable store the function falls below threshold.
        let ir = const_addr_stores(&[(0x1000, 11), (4, 22)]);
        let plan = plan_base_cse(&ir, &[]);
        // Only the (4,22) store folds → 1 fold → below the ≥2 threshold → None.
        assert_eq!(plan, None);
    }

    #[test]
    fn plan_base_cse_declines_multi_use_addr() {
        // An address vreg used by TWO stores is not single-use → not folded.
        // (Both stores reuse addr vreg 0; the second's value is vreg 2.)
        let ir = vec![
            inst(Opcode::Const {
                dest: vr(0),
                value: 4,
            }),
            inst(Opcode::Const {
                dest: vr(1),
                value: 11,
            }),
            inst(Opcode::MemStore {
                src: vr(1),
                addr: vr(0),
                offset: 0,
            }),
            inst(Opcode::Const {
                dest: vr(2),
                value: 22,
            }),
            inst(Opcode::MemStore {
                src: vr(2),
                addr: vr(0),
                offset: 0,
            }),
        ];
        // addr vreg 0 has use_count 2 → neither store folds → None.
        assert_eq!(plan_base_cse(&ir, &[]), None);
    }

    #[test]
    fn plan_base_cse_folds_static_offset_into_immediate() {
        // A non-zero static access offset folds into the immediate (ADDR + off).
        let ir = vec![
            inst(Opcode::Const {
                dest: vr(0),
                value: 0,
            }),
            inst(Opcode::Const {
                dest: vr(1),
                value: 11,
            }),
            inst(Opcode::MemStore {
                src: vr(1),
                addr: vr(0),
                offset: 16,
            }),
            inst(Opcode::Const {
                dest: vr(2),
                value: 0,
            }),
            inst(Opcode::Const {
                dest: vr(3),
                value: 22,
            }),
            inst(Opcode::MemStore {
                src: vr(3),
                addr: vr(2),
                offset: 32,
            }),
        ];
        let plan = plan_base_cse(&ir, &[]).expect("activates");
        assert_eq!(plan.fold.get(&0), Some(&16)); // 0 + 16
        assert_eq!(plan.fold.get(&2), Some(&32)); // 0 + 32
    }

    #[test]
    fn test_optimizer_bridge_basic() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    // ─── #377: --safety-bounds on the OPTIMIZED path ────────────────────────

    /// Lower `wasm_ops` through the full optimized path with the given bounds
    /// mode.
    fn lower_with_bounds(
        wasm_ops: &[WasmOp],
        num_params: usize,
        bounds: BoundsCheckConfig,
    ) -> Result<Vec<ArmOp>> {
        let mut bridge = OptimizerBridge::with_config(OptimizationConfig::all());
        bridge.set_bounds_check(bounds);
        let (ir, _cfg, _stats) = bridge.optimize_full(wasm_ops)?;
        bridge.ir_to_arm(&ir, num_params)
    }

    /// The #377/#752 wraparound-safe guard shape immediately before the
    /// access: `SUB R12,R10,#k; CMP R10,R12; BHS +0; UDF; CMP addr,R12;
    /// BLS +0; UDF`. Returns how many complete guards appear.
    fn count_guards(ops: &[ArmOp]) -> usize {
        use crate::rules::{Operand2, Reg};
        ops.windows(7)
            .filter(|w| {
                matches!(
                    &w[0],
                    ArmOp::Sub {
                        rd: Reg::R12,
                        rn: Reg::R10,
                        op2: Operand2::Imm(_),
                    }
                ) && matches!(
                    &w[1],
                    ArmOp::Cmp {
                        rn: Reg::R10,
                        op2: Operand2::Reg(Reg::R12)
                    }
                ) && matches!(
                    &w[2],
                    ArmOp::BCondOffset {
                        cond: Condition::HS,
                        offset: 0
                    }
                ) && matches!(&w[3], ArmOp::Udf { imm: 0 })
                    && matches!(
                        &w[4],
                        ArmOp::Cmp {
                            op2: Operand2::Reg(Reg::R12),
                            ..
                        }
                    )
                    && matches!(
                        &w[5],
                        ArmOp::BCondOffset {
                            cond: Condition::LS,
                            offset: 0
                        }
                    )
                    && matches!(&w[6], ArmOp::Udf { imm: 0 })
            })
            .count()
    }

    /// #377: every one of the four optimized-path memory opcodes gets the
    /// software guard (previously: byte-identical to `none` — a silent no-op).
    #[test]
    fn optimized_path_software_bounds_guards_all_memory_shapes_377() {
        // (LocalGet addr, [value]) → i32.store / i32.load / i32.store16 / i32.load8_u
        let cases: Vec<(Vec<WasmOp>, usize)> = vec![
            (
                vec![
                    WasmOp::LocalGet(0),
                    WasmOp::LocalGet(1),
                    WasmOp::I32Store {
                        offset: 4,
                        align: 2,
                    },
                ],
                2,
            ),
            (
                vec![
                    WasmOp::LocalGet(0),
                    WasmOp::I32Load {
                        offset: 0,
                        align: 2,
                    },
                ],
                1,
            ),
            (
                vec![
                    WasmOp::LocalGet(0),
                    WasmOp::LocalGet(1),
                    WasmOp::I32Store16 {
                        offset: 0,
                        align: 1,
                    },
                ],
                2,
            ),
            (
                vec![
                    WasmOp::LocalGet(0),
                    WasmOp::I32Load8U {
                        offset: 0,
                        align: 0,
                    },
                ],
                1,
            ),
        ];
        for (ops, num_params) in cases {
            let none = lower_with_bounds(&ops, num_params, BoundsCheckConfig::None).unwrap();
            let sw = lower_with_bounds(&ops, num_params, BoundsCheckConfig::Software).unwrap();
            assert_eq!(count_guards(&none), 0, "no guard under None: {ops:?}");
            assert_eq!(
                count_guards(&sw),
                1,
                "exactly one guard under Software: {ops:?} → {sw:?}"
            );
            assert!(
                sw.len() == none.len() + 7,
                "guard adds exactly 7 ops (#752 wraparound-safe shape): {ops:?}"
            );
        }
    }

    /// #377/#752: the guard constant is `k = offset + access_size` subtracted
    /// from the bound (`SUB R12, R10, #k`) — the SAME shape as the direct
    /// selector's `software_bounds_guard` (it IS that function; no mirror).
    #[test]
    fn optimized_path_software_guard_uses_end_of_access_377() {
        use crate::rules::{Operand2, Reg};
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Store {
                offset: 4,
                align: 2,
            },
        ];
        let sw = lower_with_bounds(&ops, 2, BoundsCheckConfig::Software).unwrap();
        assert!(
            sw.iter().any(|op| matches!(
                op,
                ArmOp::Sub {
                    rd: Reg::R12,
                    rn: Reg::R10,
                    op2: Operand2::Imm(8),
                }
            )),
            "guard constant must be k = 4 (offset) + 4 (size) = 8: {sw:?}"
        );
    }

    /// #377: `Mpu` emits no inline guard on the optimized path — identical to
    /// `None` (hardware enforcement is external; path parity with the direct
    /// selector's `is_passthrough` handling).
    #[test]
    fn optimized_path_mpu_is_passthrough_377() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
        ];
        let none = lower_with_bounds(&ops, 2, BoundsCheckConfig::None).unwrap();
        let mpu = lower_with_bounds(&ops, 2, BoundsCheckConfig::Mpu).unwrap();
        assert_eq!(none, mpu, "Mpu must be codegen-identical to None");
    }

    /// #377: `Masking` DECLINES memory-accessing functions to the direct
    /// selector (in-place AND is unsound on this path) — never a silent no-op.
    #[test]
    fn optimized_path_masking_declines_memory_access_377() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
        ];
        let err = lower_with_bounds(&ops, 2, BoundsCheckConfig::Masking).unwrap_err();
        assert!(
            err.to_string().contains("#377"),
            "masking must decline with the #377 message, got: {err}"
        );
        // ...but a function with NO memory access stays on the optimized path.
        let pure = vec![WasmOp::LocalGet(0), WasmOp::I32Const(1), WasmOp::I32Add];
        assert!(lower_with_bounds(&pure, 1, BoundsCheckConfig::Masking).is_ok());
    }

    /// #377: with bounds checks OFF the lowering is untouched — the flag-off
    /// stream (and thus every frozen fixture, none of which set
    /// `--safety-bounds`) is byte-identical to a bridge that never heard of
    /// bounds modes.
    #[test]
    fn optimized_path_none_is_byte_identical_377() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Store {
                offset: 4,
                align: 2,
            },
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        let default_bridge = {
            let bridge = OptimizerBridge::with_config(OptimizationConfig::all());
            let (ir, _cfg, _stats) = bridge.optimize_full(&ops).unwrap();
            bridge.ir_to_arm(&ir, 2).unwrap()
        };
        let explicit_none = lower_with_bounds(&ops, 2, BoundsCheckConfig::None).unwrap();
        assert_eq!(default_bridge, explicit_none);
    }

    #[test]
    fn test_optimizer_bridge_disabled() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::none());
        let wasm_ops = vec![WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // No passes should have run
        assert_eq!(stats.passes_run, 0);
    }

    #[test]
    fn test_optimizer_bridge_fast() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::fast());
        let wasm_ops = vec![
            WasmOp::I32Const(5),
            WasmOp::I32Const(0),
            WasmOp::I32Add, // Should be simplified to just 5
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Fast config should run some passes
        assert!(stats.passes_run >= 3);
    }

    #[test]
    fn test_empty_wasm() {
        let bridge = OptimizerBridge::new();
        let stats = bridge.optimize(&[]).unwrap();

        assert_eq!(stats.removed, 0);
        assert_eq!(stats.modified, 0);
        assert_eq!(stats.added, 0);
    }

    #[test]
    fn test_wasm_division() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![WasmOp::I32Const(20), WasmOp::I32Const(4), WasmOp::I32DivS];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_bitwise() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::I32Const(15),
            WasmOp::I32Const(7),
            WasmOp::I32And,
            WasmOp::I32Const(8),
            WasmOp::I32Or,
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_shifts() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::I32Const(1),
            WasmOp::I32Const(3),
            WasmOp::I32Shl, // 1 << 3 = 8
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_comparison() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::I32Const(10),
            WasmOp::I32Const(5),
            WasmOp::I32LtS, // 10 < 5 = 0
            WasmOp::I32Const(3),
            WasmOp::I32Const(7),
            WasmOp::I32GtU, // 3 > 7 = 0
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run optimizations
        assert!(stats.passes_run > 0);
    }

    #[test]
    fn test_wasm_complex_program() {
        let bridge = OptimizerBridge::with_config(OptimizationConfig::all());
        let wasm_ops = vec![
            // Compute (a & b) | (c << 2)
            WasmOp::LocalGet(0), // a
            WasmOp::LocalGet(1), // b
            WasmOp::I32And,      // a & b
            WasmOp::LocalGet(2), // c
            WasmOp::I32Const(2),
            WasmOp::I32Shl,      // c << 2
            WasmOp::I32Or,       // (a & b) | (c << 2)
            WasmOp::LocalSet(3), // store result
        ];

        let stats = bridge.optimize(&wasm_ops).unwrap();

        // Should have run all passes
        assert_eq!(stats.passes_run, 5);
    }

    // ========================================================================
    // Branchless Control Flow Pattern Tests
    // ========================================================================

    #[test]
    fn test_simple_if_else_to_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: cond, If, val1, Else, val2, End
        // Should become: val1, val2, cond, Select
        let wasm_ops = vec![
            WasmOp::LocalGet(0), // condition
            WasmOp::If,
            WasmOp::I32Const(10), // then value
            WasmOp::Else,
            WasmOp::I32Const(20), // else value
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10)); // then value
        assert_eq!(preprocessed[1], WasmOp::I32Const(20)); // else value
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0)); // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_nested_if_else_to_nested_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: outer_cond, If, inner_cond, If, val1, Else, val2, End, Else, val3, End
        // Should become two nested selects
        let wasm_ops = vec![
            WasmOp::LocalGet(0), // outer condition
            WasmOp::If,
            WasmOp::LocalGet(1), // inner condition
            WasmOp::If,
            WasmOp::I32Const(10), // val1 (both true)
            WasmOp::Else,
            WasmOp::I32Const(20), // val2 (outer true, inner false)
            WasmOp::End,
            WasmOp::Else,
            WasmOp::I32Const(30), // val3 (outer false)
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // The outer condition (LocalGet 0 → R0) must be saved before the inner select
        // runs, because the inner select overwrites R0 with its result.
        // Expected: save outer_cond, inner select, then outer select using saved cond.
        // outer_cond, LocalSet(255), val1, val2, inner_cond, Select, val3, LocalGet(255), Select
        assert_eq!(preprocessed.len(), 9);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(0)); // outer condition (to save)
        assert_eq!(preprocessed[1], WasmOp::LocalSet(255)); // save to synthetic local
        assert_eq!(preprocessed[2], WasmOp::I32Const(10)); // val1
        assert_eq!(preprocessed[3], WasmOp::I32Const(20)); // val2
        assert_eq!(preprocessed[4], WasmOp::LocalGet(1)); // inner condition
        assert_eq!(preprocessed[5], WasmOp::Select); // inner select
        assert_eq!(preprocessed[6], WasmOp::I32Const(30)); // val3
        assert_eq!(preprocessed[7], WasmOp::LocalGet(255)); // load saved outer condition
        assert_eq!(preprocessed[8], WasmOp::Select); // outer select
    }

    #[test]
    fn test_br_if_block_to_select() {
        let bridge = OptimizerBridge::new();

        // Pattern: Block, val1, cond, BrIf(0), Drop, val2, End
        // Should become: val1, val2, cond, Select
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::I32Const(10), // val1 (early exit value)
            WasmOp::LocalGet(0),  // condition
            WasmOp::BrIf(0),      // if cond, exit with val1
            WasmOp::Drop,
            WasmOp::I32Const(20), // val2 (fallthrough value)
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::I32Const(10)); // val1
        assert_eq!(preprocessed[1], WasmOp::I32Const(20)); // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0)); // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_br_if_block_with_local_values() {
        let bridge = OptimizerBridge::new();

        // br_if pattern with LocalGet values
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::LocalGet(1), // val1 from local
            WasmOp::LocalGet(0), // condition
            WasmOp::BrIf(0),
            WasmOp::Drop,
            WasmOp::LocalGet(2), // val2 from local
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should be transformed to: val1, val2, cond, Select
        assert_eq!(preprocessed.len(), 4);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(1)); // val1
        assert_eq!(preprocessed[1], WasmOp::LocalGet(2)); // val2
        assert_eq!(preprocessed[2], WasmOp::LocalGet(0)); // condition
        assert_eq!(preprocessed[3], WasmOp::Select);
    }

    #[test]
    fn test_no_transformation_for_non_matching_pattern() {
        let bridge = OptimizerBridge::new();

        // A pattern that doesn't match - if with complex then block
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::I32Const(10),
            WasmOp::I32Const(5),
            WasmOp::I32Add, // Complex then block (not a simple value)
            WasmOp::Else,
            WasmOp::I32Const(20),
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Should NOT be transformed - pattern doesn't match
        assert_eq!(preprocessed.len(), 8);
        assert_eq!(preprocessed[0], WasmOp::LocalGet(0));
        assert_eq!(preprocessed[1], WasmOp::If);
    }

    #[test]
    fn test_is_condition_producer() {
        // Test the helper function
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::LocalGet(0)));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32Const(1)));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32Eqz));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32Eq));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32LtS));
        assert!(OptimizerBridge::is_condition_producer(&WasmOp::I32GtU));

        // These should NOT be condition producers
        assert!(!OptimizerBridge::is_condition_producer(&WasmOp::I32Add));
        assert!(!OptimizerBridge::is_condition_producer(&WasmOp::If));
        assert!(!OptimizerBridge::is_condition_producer(&WasmOp::Block));
    }

    #[test]
    fn test_is_simple_value() {
        // Test the helper function
        assert!(OptimizerBridge::is_simple_value(&WasmOp::I32Const(42)));
        assert!(OptimizerBridge::is_simple_value(&WasmOp::LocalGet(0)));
        assert!(OptimizerBridge::is_simple_value(&WasmOp::GlobalGet(1)));

        // These should NOT be simple values
        assert!(!OptimizerBridge::is_simple_value(&WasmOp::I32Add));
        assert!(!OptimizerBridge::is_simple_value(&WasmOp::If));
        assert!(!OptimizerBridge::is_simple_value(&WasmOp::Select));
    }

    #[test]
    fn test_multiple_sequential_patterns() {
        let bridge = OptimizerBridge::new();

        // Two sequential simple if-else patterns
        let wasm_ops = vec![
            // First if-else
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::I32Const(1),
            WasmOp::Else,
            WasmOp::I32Const(2),
            WasmOp::End,
            // Store first result
            WasmOp::LocalSet(2),
            // Second if-else
            WasmOp::LocalGet(1),
            WasmOp::If,
            WasmOp::I32Const(3),
            WasmOp::Else,
            WasmOp::I32Const(4),
            WasmOp::End,
        ];

        let preprocessed = bridge.preprocess_wasm_ops(&wasm_ops);

        // Both patterns should be transformed
        // First: 1, 2, local.get(0), select
        // LocalSet(2)
        // Second: 3, 4, local.get(1), select
        assert_eq!(preprocessed.len(), 9);
        assert_eq!(preprocessed[3], WasmOp::Select);
        assert_eq!(preprocessed[4], WasmOp::LocalSet(2));
        assert_eq!(preprocessed[8], WasmOp::Select);
    }

    // =========================================================================
    // PR #86 patch coverage: ir_to_arm i64 regalloc respects AAPCS params.
    //
    // Pre-fix, the i64 lowering hardcoded R0:R1 / R2:R3 for the destination
    // pair which clobbered incoming AAPCS arg regs. The fix routes every
    // i64 dest through alloc_i64_pair so callee-saved (R4..R11) pairs are
    // preferred when params are still live. These tests exercise that path.
    // =========================================================================

    #[test]
    fn test_ir_to_arm_i64_const_with_params_does_not_clobber_r0_r3() {
        // Pretend the function has 4 i32 params live in R0..R3, and emit
        // an I64Const. The new alloc_i64_pair must pick a callee-saved pair
        // (R4..R11), not R0:R1 — for the I64Const itself. The epilogue is
        // ALLOWED to copy the result into R0:R1 (that's the AAPCS return
        // convention), so we exclude trailing Mov-to-R0/R1 with a
        // callee-saved source from the assertion.
        let bridge = OptimizerBridge::new();
        let instrs = vec![Instruction {
            id: 0,
            opcode: Opcode::I64Const {
                dest_lo: OptReg(100),
                dest_hi: OptReg(101),
                value: 0x1122_3344_5566_7788,
            },
            block_id: 0,
            is_dead: false,
        }];
        let arm = bridge.ir_to_arm(&instrs, 4).expect("valid IR lowers");
        // The I64Const itself is encoded with Movw/Movt — those MUST NOT
        // target R0..R3. The epilogue Mov-into-R0/R1 is part of the AAPCS
        // return convention and is correct.
        for op in &arm {
            if let ArmOp::Movw { rd, .. } | ArmOp::Movt { rd, .. } = op {
                let is_param = matches!(
                    rd,
                    crate::rules::Reg::R0
                        | crate::rules::Reg::R1
                        | crate::rules::Reg::R2
                        | crate::rules::Reg::R3
                );
                assert!(
                    !is_param,
                    "I64Const with num_params=4 clobbered AAPCS param via Movw/Movt: {:?}",
                    op
                );
            }
        }
        // And we should have produced *some* code that loads the value.
        assert!(!arm.is_empty(), "I64Const should emit instructions");
    }

    #[test]
    fn test_ir_to_arm_i64_const_zero_params_can_use_callee_saved() {
        // With zero params, alloc_i64_pair should still pick a callee-saved
        // pair (R4:R5 first), since param_reserved_regs is empty.
        let bridge = OptimizerBridge::new();
        let instrs = vec![Instruction {
            id: 0,
            opcode: Opcode::I64Const {
                dest_lo: OptReg(0),
                dest_hi: OptReg(1),
                value: 0xdead_beefu64 as i64,
            },
            block_id: 0,
            is_dead: false,
        }];
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        assert!(!arm.is_empty());
    }

    #[test]
    fn test_ir_to_arm_i64_add_operand_regs_and_param_decline_518() {
        // Build IR that loads two i64 values via I64Load (addr 0/1) then adds
        // them. Two assertions:
        //  (1) #518: when those I64Loads are PARAM reads (addr < num_params) the
        //      optimized path DECLINES (it cannot AAPCS-home an i64 param pair),
        //      so ir_to_arm returns Err and the backend falls back to the direct
        //      selector. Correct param lowering is covered end-to-end by
        //      scripts/repro/i64_param_518_differential.py.
        //  (2) for NON-param i64 values (addr >= num_params) it still lowers,
        //      emitting Adds/Adc that use the operand registers, not hardcoded
        //      ones.
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            // I64Load addr=0 → R0:R1
            Instruction {
                id: 0,
                opcode: Opcode::I64Load {
                    dest_lo: OptReg(10),
                    dest_hi: OptReg(11),
                    addr: 0,
                },
                block_id: 0,
                is_dead: false,
            },
            // I64Load addr=1 → R2:R3
            Instruction {
                id: 1,
                opcode: Opcode::I64Load {
                    dest_lo: OptReg(12),
                    dest_hi: OptReg(13),
                    addr: 1,
                },
                block_id: 0,
                is_dead: false,
            },
            // I64Add of the two pairs.
            Instruction {
                id: 2,
                opcode: Opcode::I64Add {
                    dest_lo: OptReg(14),
                    dest_hi: OptReg(15),
                    src1_lo: OptReg(10),
                    src1_hi: OptReg(11),
                    src2_lo: OptReg(12),
                    src2_hi: OptReg(13),
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        // (1) addr 0/1 ARE params (num_params=4) → decline (#518).
        assert!(
            bridge.ir_to_arm(&instrs, 4).is_err(),
            "#518: reading an i64 param must decline the optimized path"
        );
        // (2) same IR, but num_params=0 → addr 0/1 are non-param i64 locals →
        //     lowers, using operand registers for the ADDS/ADC.
        let arm = bridge
            .ir_to_arm(&instrs, 0)
            .expect("non-param i64 IR lowers");
        let has_adds = arm.iter().any(|op| matches!(op, ArmOp::Adds { .. }));
        let has_adc = arm.iter().any(|op| matches!(op, ArmOp::Adc { .. }));
        assert!(has_adds, "i64.add should emit ADDS for the low half");
        assert!(has_adc, "i64.add should emit ADC for the high half");
    }

    #[test]
    fn test_ir_to_arm_i64_sub_emits_subs_sbc() {
        // I64Sub characteristic: SUBS for low + SBC for high.
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(0),
                    dest_hi: OptReg(1),
                    value: 100,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(2),
                    dest_hi: OptReg(3),
                    value: 50,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::I64Sub {
                    dest_lo: OptReg(4),
                    dest_hi: OptReg(5),
                    src1_lo: OptReg(0),
                    src1_hi: OptReg(1),
                    src2_lo: OptReg(2),
                    src2_hi: OptReg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        let has_subs = arm.iter().any(|op| matches!(op, ArmOp::Subs { .. }));
        let has_sbc = arm.iter().any(|op| matches!(op, ArmOp::Sbc { .. }));
        assert!(has_subs, "i64.sub should emit SUBS for the low half");
        assert!(has_sbc, "i64.sub should emit SBC for the high half");
    }

    #[test]
    fn test_ir_to_arm_i64_or_emits_two_orr() {
        // I64Or → two ORR (low-half and high-half).
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(0),
                    dest_hi: OptReg(1),
                    value: 0x0F,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(2),
                    dest_hi: OptReg(3),
                    value: 0xF0,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::I64Or {
                    dest_lo: OptReg(4),
                    dest_hi: OptReg(5),
                    src1_lo: OptReg(0),
                    src1_hi: OptReg(1),
                    src2_lo: OptReg(2),
                    src2_hi: OptReg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        let orr_count = arm
            .iter()
            .filter(|op| matches!(op, ArmOp::Orr { .. }))
            .count();
        assert!(orr_count >= 2, "i64.or should emit ORR twice (lo and hi)");
    }

    #[test]
    fn test_ir_to_arm_i64_const_with_2_params_uses_first_callee_saved() {
        // With num_params=2, R0/R1 are reserved. alloc_i64_pair starts from
        // (R4,R5) which is unconditionally free here.
        let bridge = OptimizerBridge::new();
        let instrs = vec![Instruction {
            id: 0,
            opcode: Opcode::I64Const {
                dest_lo: OptReg(0),
                dest_hi: OptReg(1),
                value: 1,
            },
            block_id: 0,
            is_dead: false,
        }];
        let arm = bridge.ir_to_arm(&instrs, 2).expect("valid IR lowers");
        // Should not have written to R0 or R1 (the reserved param regs).
        for op in &arm {
            if let ArmOp::Mov {
                rd: crate::rules::Reg::R0,
                ..
            }
            | ArmOp::Mov {
                rd: crate::rules::Reg::R1,
                ..
            }
            | ArmOp::Movw {
                rd: crate::rules::Reg::R0,
                ..
            }
            | ArmOp::Movw {
                rd: crate::rules::Reg::R1,
                ..
            }
            | ArmOp::Movt {
                rd: crate::rules::Reg::R0,
                ..
            }
            | ArmOp::Movt {
                rd: crate::rules::Reg::R1,
                ..
            } = op
            {
                // The i64-result epilogue moves the result into R0:R1 AT THE
                // END — so a single Mov-to-R0 from the result pair is fine,
                // but Movw/Movt-to-R0/R1 means the I64Const itself clobbered
                // the param. Filter out the epilogue Movs by looking at
                // their position and source pattern: an epilogue Mov uses
                // Operand2::Reg(callee-saved). For this test, we simply
                // assert no Movw/Movt targets the reserved set.
                if matches!(op, ArmOp::Movw { .. } | ArmOp::Movt { .. }) {
                    panic!(
                        "I64Const with num_params=2 clobbered AAPCS register: {:?}",
                        op
                    );
                }
            }
        }
    }

    // ========================================================================
    // Issue #94: u64-packed FFI return — direct hi/lo extraction
    // ========================================================================
    //
    // The canonical wasm sequence emitted by Rust → wasm for extracting the
    // upper 32 bits of a u64-packed return value is:
    //
    //     local.get $packed_i64    ;; the packed u64 in an i64 local
    //     i64.const 32
    //     i64.shr_u
    //     i32.wrap_i64
    //
    // Pre-fix, synth lowered this to ~38 bytes of generic 64-bit shift
    // emulation. After the fix, it should collapse to a single
    // `mov rd_hi, #0` plus a vreg rename — the hi half of the input pair
    // is already in a register.

    #[cfg(test)]
    fn count_arm_byte_size(arm: &[ArmOp]) -> usize {
        // Delegate to the production size table. Before PR #511 this was a
        // hand-maintained mirror of `estimate_arm_byte_size` (a drifted copy
        // with its own `_ => 4` default and a partial op set); #511 extracted
        // that table to `estimate_arm_byte_size` AND established the real
        // independent check — the `estimator_encoder_agreement` oracle, which
        // pins the table against the actual Thumb-2 encoder. With the encoder
        // as ground truth, the local proxy was redundant: point the tests at
        // the production estimator so a regression in it is what moves these
        // counts.
        arm.iter().map(estimate_arm_byte_size).sum()
    }

    /// Print before/after sizes for the canonical issue #94 pattern. This
    /// "test" is informational — it passes regardless and is intended to be
    /// run with `cargo test ... -- --nocapture` to surface the win in CI logs.
    #[test]
    fn test_issue94_size_demo() {
        let bridge = OptimizerBridge::new();

        // After-fix: shift-by-32 hits the constant-aware fast path.
        let after_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(32),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let (instrs, _, _) = bridge.optimize_full(&after_ops).unwrap();
        // #518: num_params=0 → non-param i64 source (i64-param reads decline).
        let arm_after = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        let bytes_after = count_arm_byte_size(&arm_after);

        // Pre-fix proxy: shift-by-7 takes the generic ArmOp::I64ShrU path,
        // which is byte-identical to the unoptimized shift-by-32 emit.
        let before_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(7),
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];
        let (instrs, _, _) = bridge.optimize_full(&before_ops).unwrap();
        let arm_before = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        let bytes_before = count_arm_byte_size(&arm_before);

        println!(
            "\n[issue #94 demo] hi32 extract: BEFORE = {} bytes, AFTER = {} bytes (saved {})",
            bytes_before,
            bytes_after,
            bytes_before.saturating_sub(bytes_after)
        );
        println!("[issue #94 demo] AFTER ops emitted = {}", arm_after.len());
        for op in &arm_after {
            println!("[issue #94 demo]   {:?}", op);
        }
    }

    /// Issue #94: `i64.shr_u 32` followed by `i32.wrap_i64` should NOT emit
    /// a runtime 64-bit shift. The hi half of the source pair is already in
    /// a register; we just need to rename + zero out the (now-unused) hi half.
    #[test]
    fn test_issue94_shr_u_32_lowers_to_register_rename() {
        let bridge = OptimizerBridge::new();
        // (i64) -> i32, body = `local.get 0; i64.const 32; i64.shr_u; i32.wrap_i64`
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(32), // shift amount
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        // #518: num_params = 0 → the i64 source is a NON-PARAM local. An i64
        // PARAM read is now declined to the direct selector (the optimized path
        // can't AAPCS-home a param pair), so this peephole is exercised on a
        // non-param i64; the i64-param path's correctness is covered by
        // scripts/repro/i64_param_518_differential.py.
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");

        // After fix: NO ArmOp::I64ShrU should be emitted. The 38-byte runtime
        // shift sequence is the bug we're fixing.
        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrU { .. }));
        assert!(
            !has_runtime_shift,
            "i64.shr_u with constant 32 should NOT emit ArmOp::I64ShrU; got: {:#?}",
            arm
        );

        // Total emitted byte size should drop well below the 38-byte runtime
        // shift alone. The pre-fix lower bound was 38 bytes for the shift
        // plus several bytes for the constant-32 load and epilogue moves.
        let bytes = count_arm_byte_size(&arm);
        assert!(
            bytes < 30,
            "expected < 30 bytes after fix; got {} bytes: {:#?}",
            bytes,
            arm
        );
    }

    /// Issue #94: signed variant. `i64.shr_s 32` extracts the upper 32 bits
    /// just like `shr_u`, but the result is sign-extended into the (still-
    /// unused) hi half via a single `asr rd_hi, rn_hi, #31`.
    #[test]
    fn test_issue94_shr_s_32_lowers_to_register_rename_with_sign_extend() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(32),
            WasmOp::I64ShrS,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        // #518: num_params=0 → non-param i64 source (i64-param reads decline).
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");

        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrS { .. }));
        assert!(
            !has_runtime_shift,
            "i64.shr_s with constant 32 should NOT emit ArmOp::I64ShrS; got: {:#?}",
            arm
        );

        // We expect exactly one ASR (for the sign-extend of the hi half).
        let asr_count = arm
            .iter()
            .filter(|op| matches!(op, ArmOp::Asr { .. }))
            .count();
        assert_eq!(
            asr_count, 1,
            "expected one ASR for sign extend; got: {:#?}",
            arm
        );

        let bytes = count_arm_byte_size(&arm);
        assert!(
            bytes < 30,
            "expected < 30 bytes after fix; got {} bytes: {:#?}",
            bytes,
            arm
        );
    }

    /// Issue #94: `i64.and 0xFFFFFFFF` (lo32 mask) followed by `i32.wrap_i64`
    /// should NOT emit two AND.W instructions; the lo half is unchanged and
    /// the hi half is zero. Becomes a register rename + `mov rd_hi, #0`.
    #[test]
    fn test_issue94_and_mask_low32_lowers_to_register_rename() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(0xFFFF_FFFF),
            WasmOp::I64And,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        // #518: num_params=0 → non-param i64 source (i64-param reads decline).
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");

        // After fix: at most one AND should remain, and it shouldn't be the
        // pair of ANDs from the generic i64.and lowering. (We allow zero ANDs
        // because the lo half is unchanged via vreg rename.)
        let and_count = arm
            .iter()
            .filter(|op| matches!(op, ArmOp::And { .. }))
            .count();
        assert!(
            and_count == 0,
            "i64.and 0xFFFFFFFF should not emit any AND.W; got {} ANDs in {:#?}",
            and_count,
            arm
        );
    }

    /// Sanity: a non-32 shift constant should still emit the full ArmOp::I64ShrU
    /// (we don't want to silently regress the general case).
    #[test]
    fn test_issue94_shr_u_non_32_still_emits_runtime_shift() {
        let bridge = OptimizerBridge::new();
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I64Const(7), // not 32 — generic path
            WasmOp::I64ShrU,
            WasmOp::I32WrapI64,
        ];

        let (instrs, _, _) = bridge.optimize_full(&wasm_ops).unwrap();
        // #518: num_params=0 → non-param i64 source (i64-param reads decline).
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");

        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrU { .. }));
        assert!(
            has_runtime_shift,
            "i64.shr_u with non-32 constant must still emit ArmOp::I64ShrU; got: {:#?}",
            arm
        );
    }

    /// Direct IR-level test (independent of wasm_to_ir's vreg numbering):
    /// construct the IR by hand and verify the lowering eliminates I64ShrU.
    #[test]
    fn test_issue94_ir_level_shr_u_32() {
        let bridge = OptimizerBridge::new();
        // Pattern:
        //   v0:v1 = I64Const 0x0123_4567_89AB_CDEF
        //   v2:v3 = I64Const 32
        //   v4:v5 = I64ShrU v0:v1, v2:v3
        //
        // Expected: no ArmOp::I64ShrU is emitted; v4 maps to the same ARM
        // register as v1 (the hi of the source pair).
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(0),
                    dest_hi: OptReg(1),
                    value: 0x0123_4567_89AB_CDEFi64,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::I64Const {
                    dest_lo: OptReg(2),
                    dest_hi: OptReg(3),
                    value: 32,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 4,
                opcode: Opcode::I64ShrU {
                    dest_lo: OptReg(4),
                    dest_hi: OptReg(5),
                    src1_lo: OptReg(0),
                    src1_hi: OptReg(1),
                    src2_lo: OptReg(2),
                    src2_hi: OptReg(3),
                },
                block_id: 0,
                is_dead: false,
            },
        ];

        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        let has_runtime_shift = arm.iter().any(|op| matches!(op, ArmOp::I64ShrU { .. }));
        assert!(
            !has_runtime_shift,
            "IR-level: i64.shr_u with constant 32 should NOT emit ArmOp::I64ShrU; got: {:#?}",
            arm
        );
    }

    #[test]
    fn fold_mem_offset_gates_on_imm12_382() {
        // Small offsets (<= 0xFFF) are left in the access immediate so existing
        // output stays byte-identical; large offsets fold into the const base.
        assert_eq!(fold_mem_offset(0x2000_0100, 100), (0x2000_0100, 100));
        assert_eq!(fold_mem_offset(0x2000_0100, 0xFFF), (0x2000_0100, 0xFFF));
        // Boundary: 0x1000 (4096) is the first offset that must fold.
        assert_eq!(fold_mem_offset(0x2000_0100, 0x1000), (0x2000_1100, 0));
        assert_eq!(fold_mem_offset(0x2000_0100, 5000), (0x2000_1488, 0));
        // Arithmetic identity holds: (base + off) + 0 == base + off.
        let (b, imm) = fold_mem_offset(0x2000_0100, 5000);
        assert_eq!(
            b.wrapping_add(imm as u32),
            0x2000_0100u32.wrapping_add(5000)
        );
    }

    #[test]
    fn memstore_large_offset_folds_into_base_382() {
        // #382: a MemStore with offset > imm12 must NOT emit a `[R12, #offset]`
        // whose immediate exceeds 0xFFF (the encoder would refuse it and the
        // function would be skipped). The offset is folded into the MOVW/MOVT
        // base instead, leaving the access immediate at 0.
        let bridge = OptimizerBridge::new();
        let instrs = vec![
            Instruction {
                id: 0,
                opcode: Opcode::Const {
                    dest: OptReg(0),
                    value: 0,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 1,
                opcode: Opcode::Const {
                    dest: OptReg(1),
                    value: 0xDEAD,
                },
                block_id: 0,
                is_dead: false,
            },
            Instruction {
                id: 2,
                opcode: Opcode::MemStore {
                    src: OptReg(1),
                    addr: OptReg(0),
                    offset: 5000,
                },
                block_id: 0,
                is_dead: false,
            },
        ];
        let arm = bridge.ir_to_arm(&instrs, 0).expect("valid IR lowers");
        // No load/store may carry an immediate > 0xFFF.
        for op in &arm {
            if let ArmOp::Str { addr, .. } = op {
                assert!(
                    addr.offset.unsigned_abs() <= 0xFFF,
                    "STR immediate {:#x} exceeds imm12 — offset was not folded: {:#?}",
                    addr.offset,
                    arm
                );
            }
        }
        // The base must be materialized as 0x20000100 + 5000 = 0x20001488.
        let has_folded_base = arm
            .iter()
            .any(|op| matches!(op, ArmOp::Movw { imm16, .. } if *imm16 == 0x1488));
        assert!(
            has_folded_base,
            "expected MOVW #0x1488 (0x20000100 + 5000 low half); got: {:#?}",
            arm
        );
    }

    // ---- VCR-RA-001 allocation-time spill-on-exhaustion (#242, #496) ----

    /// Straight-line i32 IR with 6 simultaneously-live binop results over two
    /// params — one more than the R4-R8 scratch pool holds — followed by a
    /// non-commutative fold. Flag-off this exhausts `alloc_i32_scratch` and
    /// declines (#496); flag-on it must spill and compile.
    fn pressure_ir() -> Vec<Instruction> {
        let ops = vec![
            Opcode::Load {
                dest: vr(0),
                addr: 0,
            },
            Opcode::Load {
                dest: vr(1),
                addr: 1,
            },
            Opcode::Add {
                dest: vr(2),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::Sub {
                dest: vr(3),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::Xor {
                dest: vr(4),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::Or {
                dest: vr(5),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::And {
                dest: vr(6),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::Mul {
                dest: vr(7),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::Sub {
                dest: vr(8),
                src1: vr(2),
                src2: vr(3),
            },
            Opcode::Xor {
                dest: vr(9),
                src1: vr(8),
                src2: vr(4),
            },
            Opcode::Add {
                dest: vr(10),
                src1: vr(9),
                src2: vr(5),
            },
            Opcode::Sub {
                dest: vr(11),
                src1: vr(10),
                src2: vr(6),
            },
            Opcode::Xor {
                dest: vr(12),
                src1: vr(11),
                src2: vr(7),
            },
            Opcode::Return {
                value: Some(vr(12)),
            },
        ];
        ops.into_iter().map(inst).collect()
    }

    #[test]
    fn test_496_pressure_ir_declines_flag_off() {
        // RED baseline: without the lever, scratch-pool exhaustion declines the
        // whole function to the direct selector (#496) — never a silent R12
        // borrow.
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(false);
        let err = bridge
            .ir_to_arm(&pressure_ir(), 2)
            .expect_err("6 live values over a 5-reg pool must decline flag-off");
        assert!(
            err.to_string().contains("#496"),
            "decline must be the #496 exhaustion decline; got: {err}"
        );
    }

    #[test]
    fn test_242_spill_on_exhaust_compiles_pressure_ir() {
        // GREEN: with the lever, the same function compiles on the optimized
        // path by spilling to frame slots at allocation time.
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let arm = bridge
            .ir_to_arm(&pressure_ir(), 2)
            .expect("flag-on: exhaustion spills instead of declining");
        // At least one spill store must exist,
        let spill_stores: Vec<i32> = arm
            .iter()
            .filter_map(|op| match op {
                ArmOp::Str { rd: _, addr } if addr.base == Reg::SP => Some(addr.offset),
                _ => None,
            })
            .collect();
        assert!(
            !spill_stores.is_empty(),
            "pressure function must spill; got: {arm:#?}"
        );
        // ... and every frame reload must read a slot some earlier store wrote
        // (the balance invariant — an unmatched LDR is the read-of-garbage
        // spill bug class).
        let mut written: std::collections::HashSet<i32> = std::collections::HashSet::new();
        for op in &arm {
            match op {
                ArmOp::Str { addr, .. } if addr.base == Reg::SP => {
                    written.insert(addr.offset);
                }
                ArmOp::Ldr { addr, .. } if addr.base == Reg::SP => {
                    assert!(
                        written.contains(&addr.offset),
                        "LDR [SP, #{}] reads a slot never written: {arm:#?}",
                        addr.offset
                    );
                }
                _ => {}
            }
        }
        // The R12 exhaustion fallback must never ship (this IR has no memory
        // ops, so no legitimate R12 use exists either).
        for op in &arm {
            if let ArmOp::Str { rd, .. } | ArmOp::Ldr { rd, .. } | ArmOp::Mov { rd, .. } = op {
                assert_ne!(*rd, Reg::R12, "R12 borrow shipped flag-on: {arm:#?}");
            }
        }
        // The frame must be set up and torn down (SUB at entry, ADD before BX).
        assert!(
            matches!(
                arm.first(),
                Some(ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    ..
                })
            ),
            "spill frame prologue missing: {arm:#?}"
        );
        let bx_pos = arm
            .iter()
            .position(|op| matches!(op, ArmOp::Bx { .. }))
            .expect("return present");
        assert!(
            matches!(
                &arm[bx_pos - 1],
                ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    ..
                }
            ),
            "spill frame epilogue (ADD SP) missing before BX: {arm:#?}"
        );
    }

    #[test]
    fn test_242_spill_on_exhaust_belady_first_victim() {
        // At the exhausting Mul (6th live dest), the pool holds v2..v6 in
        // R4..R8, with next uses at fold positions 8,8,9,10,11 respectively.
        // Belady evicts the FARTHEST next use — v6 in R8 (position 11) — not
        // the oldest allocation (v2 in R4, which LRU would pick).
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let arm = bridge.ir_to_arm(&pressure_ir(), 2).expect("compiles");
        let first_spill = arm
            .iter()
            .find_map(|op| match op {
                ArmOp::Str { rd, addr } if addr.base == Reg::SP => Some(*rd),
                _ => None,
            })
            .expect("pressure function must spill");
        assert_eq!(
            first_spill,
            Reg::R8,
            "Belady must evict the farthest-next-use victim (v6 in R8): {arm:#?}"
        );
    }

    #[test]
    fn test_242_spill_on_exhaust_noop_below_pressure() {
        // A function that never exhausts the pool must produce IDENTICAL bytes
        // with the lever on and off — the pre-step only acts at the pressure
        // edge.
        let ops = vec![
            Opcode::Load {
                dest: vr(0),
                addr: 0,
            },
            Opcode::Load {
                dest: vr(1),
                addr: 1,
            },
            Opcode::Add {
                dest: vr(2),
                src1: vr(0),
                src2: vr(1),
            },
            Opcode::Xor {
                dest: vr(3),
                src1: vr(2),
                src2: vr(1),
            },
            Opcode::Return { value: Some(vr(3)) },
        ];
        let ir: Vec<Instruction> = ops.into_iter().map(inst).collect();
        let mut on = OptimizerBridge::new();
        on.set_spill_on_exhaust(true);
        let mut off = OptimizerBridge::new();
        off.set_spill_on_exhaust(false);
        assert_eq!(
            on.ir_to_arm(&ir, 2).expect("compiles"),
            off.ir_to_arm(&ir, 2).expect("compiles"),
            "below the pressure edge the lever must be a no-op"
        );
    }

    #[test]
    fn test_242_spill_on_exhaust_supported_scope() {
        // The honest v1 scope: i64 pairs, control flow, calls, and non-param
        // locals stay on the #496 decline path even flag-on.
        assert!(spill_on_exhaust_supported(
            &Opcode::Add {
                dest: vr(0),
                src1: vr(1),
                src2: vr(2)
            },
            2
        ));
        assert!(spill_on_exhaust_supported(
            &Opcode::Const {
                dest: vr(0),
                value: 7
            },
            2
        ));
        // Param local (addr < num_params) and the synthetic select local 255
        // are in scope; other non-param locals are not.
        assert!(spill_on_exhaust_supported(
            &Opcode::Load {
                dest: vr(0),
                addr: 1
            },
            2
        ));
        assert!(spill_on_exhaust_supported(
            &Opcode::Store {
                src: vr(0),
                addr: 255
            },
            2
        ));
        assert!(!spill_on_exhaust_supported(
            &Opcode::Store {
                src: vr(0),
                addr: 2
            },
            2
        ));
        // #587: the modeled i64 subset is IN scope now...
        assert!(spill_on_exhaust_supported(
            &Opcode::I64Add {
                dest_lo: vr(0),
                dest_hi: vr(1),
                src1_lo: vr(2),
                src1_hi: vr(3),
                src2_lo: vr(4),
                src2_hi: vr(5)
            },
            2
        ));
        // ... but the unmodeled i64 remainder (shifts: encoder clobbers the
        // amount pair in place) keeps declining.
        assert!(!spill_on_exhaust_supported(
            &Opcode::I64Shl {
                dest_lo: vr(0),
                dest_hi: vr(1),
                src1_lo: vr(2),
                src1_hi: vr(3),
                src2_lo: vr(4),
                src2_hi: vr(5)
            },
            2
        ));
        // Param i64 loads are in scope; non-param i64 locals are not.
        assert!(spill_on_exhaust_supported(
            &Opcode::I64Load {
                dest_lo: vr(0),
                dest_hi: vr(1),
                addr: 0
            },
            2
        ));
        assert!(!spill_on_exhaust_supported(
            &Opcode::I64Load {
                dest_lo: vr(0),
                dest_hi: vr(1),
                addr: 2
            },
            2
        ));
        assert!(!spill_on_exhaust_supported(
            &Opcode::Branch { target: 0 },
            2
        ));
        assert!(!spill_on_exhaust_supported(
            &Opcode::CondBranch {
                cond: vr(0),
                target: 0
            },
            2
        ));
        assert!(!spill_on_exhaust_supported(
            &Opcode::Call {
                dest: vr(0),
                func_idx: 0
            },
            2
        ));
        // A single unsupported opcode disables the lever for the whole
        // function: pressure IR + one unmodeled i64 op (a shift) must still
        // decline flag-on.
        let mut ir = pressure_ir();
        ir.insert(
            ir.len() - 1,
            // Sources re-use already-defined vregs so the handler (which
            // still RUNS — the decline is only flagged at end of build)
            // resolves them; only the scope gating is under test here.
            inst(Opcode::I64Shl {
                dest_lo: vr(100),
                dest_hi: vr(101),
                src1_lo: vr(0),
                src1_hi: vr(1),
                src2_lo: vr(2),
                src2_hi: vr(3),
            }),
        );
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let err = bridge
            .ir_to_arm(&ir, 2)
            .expect_err("unsupported opcode must keep the #496 decline");
        assert!(err.to_string().contains("#496"), "got: {err}");
    }

    // ---- #587: i64 register-PAIR exhaustion — pair-aware Belady eviction ----

    /// Five simultaneously-live i64 constants (5 pairs over the 4 candidate
    /// pairs) folded by non-commutative ops — the pair-exhaustion pressure
    /// shape. `num_params = 0` so no AAPCS registers are reserved.
    fn pressure_i64_ir() -> Vec<Instruction> {
        let ops = vec![
            Opcode::I64Const {
                dest_lo: vr(0),
                dest_hi: vr(1),
                value: 0x1111_1111_2222_2222,
            },
            Opcode::I64Const {
                dest_lo: vr(2),
                dest_hi: vr(3),
                value: 0x3333_3333_4444_4444,
            },
            Opcode::I64Const {
                dest_lo: vr(4),
                dest_hi: vr(5),
                value: 0x5555_5555_6666_6666,
            },
            Opcode::I64Const {
                dest_lo: vr(6),
                dest_hi: vr(7),
                value: 0x7777_7777_8888_8888,
            },
            // 5th live pair: even-pair exhaustion happens HERE.
            Opcode::I64Const {
                dest_lo: vr(8),
                dest_hi: vr(9),
                value: 0x0123_4567_89AB_CDEF,
            },
            Opcode::I64Add {
                dest_lo: vr(10),
                dest_hi: vr(11),
                src1_lo: vr(6),
                src1_hi: vr(7),
                src2_lo: vr(8),
                src2_hi: vr(9),
            },
            Opcode::I64Sub {
                dest_lo: vr(12),
                dest_hi: vr(13),
                src1_lo: vr(4),
                src1_hi: vr(5),
                src2_lo: vr(10),
                src2_hi: vr(11),
            },
            Opcode::I64Xor {
                dest_lo: vr(14),
                dest_hi: vr(15),
                src1_lo: vr(2),
                src1_hi: vr(3),
                src2_lo: vr(12),
                src2_hi: vr(13),
            },
            Opcode::I64Add {
                dest_lo: vr(16),
                dest_hi: vr(17),
                src1_lo: vr(0),
                src1_hi: vr(1),
                src2_lo: vr(14),
                src2_hi: vr(15),
            },
        ];
        ops.into_iter().map(inst).collect()
    }

    #[test]
    fn test_587_i64_pair_pressure_declines_flag_off() {
        // RED baseline: pair exhaustion declines to the direct selector
        // (#496) flag-off — never the (R4,R5) aliasing fallback.
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(false);
        let err = bridge
            .ir_to_arm(&pressure_i64_ir(), 0)
            .expect_err("5 live pairs over 4 candidates must decline flag-off");
        assert!(err.to_string().contains("#496"), "got: {err}");
    }

    #[test]
    fn test_587_i64_pair_pressure_compiles_flag_on() {
        // GREEN: flag-on, pair-aware Belady eviction keeps the function on
        // the optimized path.
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let arm = bridge
            .ir_to_arm(&pressure_i64_ir(), 0)
            .expect("flag-on: pair exhaustion spills instead of declining");
        // Spill slots must exist, and every reload must read a written slot.
        let mut written: std::collections::HashSet<i32> = std::collections::HashSet::new();
        let mut spill_stores = 0usize;
        for op in &arm {
            match op {
                ArmOp::Str { addr, .. } if addr.base == Reg::SP => {
                    written.insert(addr.offset);
                    spill_stores += 1;
                }
                ArmOp::Ldr { addr, .. } if addr.base == Reg::SP => {
                    assert!(
                        written.contains(&addr.offset),
                        "LDR [SP, #{}] reads a slot never written: {arm:#?}",
                        addr.offset
                    );
                }
                _ => {}
            }
        }
        assert!(spill_stores >= 2, "pair pressure must spill: {arm:#?}");
        // Pair slots are 8-byte aligned lo/hi couples (#325 convention):
        // every written offset belongs to an (8k, 8k+4) couple.
        for off in &written {
            let base = off & !7;
            assert!(
                written.contains(&base) && written.contains(&(base + 4)),
                "slot #{off} is not part of an 8-aligned pair couple: {written:?}"
            );
        }
        // No R12 borrow may ship (no memory ops in this IR, so no legitimate
        // R12 use exists either).
        for op in &arm {
            if let ArmOp::Str { rd, .. } | ArmOp::Ldr { rd, .. } | ArmOp::Mov { rd, .. } = op {
                assert_ne!(*rd, Reg::R12, "R12 borrow shipped flag-on: {arm:#?}");
            }
        }
        // Frame prologue/epilogue must bracket the body.
        assert!(
            matches!(
                arm.first(),
                Some(ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    ..
                })
            ),
            "spill frame prologue missing: {arm:#?}"
        );
    }

    #[test]
    fn test_587_i64_below_pressure_flag_is_noop() {
        // Two live pairs never exhaust the 4 candidates: flag on/off must be
        // byte-identical (the pre-step only acts at the pressure edge).
        let ops = vec![
            Opcode::I64Const {
                dest_lo: vr(0),
                dest_hi: vr(1),
                value: 42,
            },
            Opcode::I64Const {
                dest_lo: vr(2),
                dest_hi: vr(3),
                value: 7,
            },
            Opcode::I64Add {
                dest_lo: vr(4),
                dest_hi: vr(5),
                src1_lo: vr(0),
                src1_hi: vr(1),
                src2_lo: vr(2),
                src2_hi: vr(3),
            },
        ];
        let ir: Vec<Instruction> = ops.into_iter().map(inst).collect();
        let mut on = OptimizerBridge::new();
        on.set_spill_on_exhaust(true);
        let mut off = OptimizerBridge::new();
        off.set_spill_on_exhaust(false);
        assert_eq!(
            on.ir_to_arm(&ir, 0).expect("compiles"),
            off.ir_to_arm(&ir, 0).expect("compiles"),
            "below the pressure edge the lever must be a no-op"
        );
    }

    #[test]
    fn test_587_two_singles_evicted_to_free_a_pair() {
        // Case (b) of the pair evictor: freeing a legal even pair by
        // displacing TWO independent i32 singles. Four singles fill R4-R7 and
        // two i64 pairs fill (R8,R9)/(R10,R11); the third i64 const finds no
        // free candidate. Next-uses are arranged so the pairs and the R6/R7
        // singles are needed SOON and the R4/R5 singles LAST — pair-aware
        // Belady must free (R4,R5) by evicting its two singles.
        let mut ops = vec![Opcode::Load {
            dest: vr(0),
            addr: 0,
        }];
        // v1..v4 live i32 derivations (fill R4..R7).
        for k in 0..4u32 {
            ops.push(Opcode::Add {
                dest: vr(1 + k),
                src1: vr(0),
                src2: vr(0),
            });
        }
        ops.push(Opcode::I64Const {
            dest_lo: vr(20),
            dest_hi: vr(21),
            value: 0x0102_0304_0506_0708,
        }); // A → (R8,R9)
        ops.push(Opcode::I64Const {
            dest_lo: vr(22),
            dest_hi: vr(23),
            value: 0x1122_3344_5566_7788,
        }); // B → (R10,R11)
        ops.push(Opcode::I64Const {
            dest_lo: vr(24),
            dest_hi: vr(25),
            value: 0x0A0B_0C0D_0E0F_1011,
        }); // C: no free candidate — two-singles eviction fires HERE
        ops.push(Opcode::I64Add {
            dest_lo: vr(26),
            dest_hi: vr(27),
            src1_lo: vr(20),
            src1_hi: vr(21),
            src2_lo: vr(24),
            src2_hi: vr(25),
        }); // A soon
        ops.push(Opcode::I64Xor {
            dest_lo: vr(28),
            dest_hi: vr(29),
            src1_lo: vr(22),
            src1_hi: vr(23),
            src2_lo: vr(26),
            src2_hi: vr(27),
        }); // B soon
        // R6/R7 singles next...
        ops.push(Opcode::Xor {
            dest: vr(30),
            src1: vr(3),
            src2: vr(0),
        });
        ops.push(Opcode::Xor {
            dest: vr(31),
            src1: vr(4),
            src2: vr(0),
        });
        // ... and the R4/R5 singles LAST (farthest combined next use).
        ops.push(Opcode::Xor {
            dest: vr(32),
            src1: vr(1),
            src2: vr(0),
        });
        ops.push(Opcode::Xor {
            dest: vr(33),
            src1: vr(2),
            src2: vr(0),
        });
        let ir: Vec<Instruction> = ops.into_iter().map(inst).collect();
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let arm = bridge
            .ir_to_arm(&ir, 1)
            .expect("two-singles eviction frees a legal even pair");
        // The first two spill stores are the two-singles eviction of R4+R5
        // (v1 and v2, the farthest combined next use).
        let store_regs: Vec<Reg> = arm
            .iter()
            .filter_map(|op| match op {
                ArmOp::Str { rd, addr } if addr.base == Reg::SP => Some(*rd),
                _ => None,
            })
            .collect();
        assert!(
            store_regs.len() >= 2 && store_regs[0] == Reg::R4 && store_regs[1] == Reg::R5,
            "freeing (R4,R5) must displace its two singles first; got STRs {store_regs:?}: {arm:#?}"
        );
    }

    // ---- VCR-VER-001: constant-divisor trap-guard elision (#242) ----

    /// `p0 / C` as IR: a single-def Const divisor feeding a DivS/DivU.
    fn const_div_ir(div: bool, signed: bool, c: i32) -> Vec<Instruction> {
        let ops = vec![
            Opcode::Load {
                dest: vr(0),
                addr: 0,
            },
            Opcode::Const {
                dest: vr(1),
                value: c,
            },
            match (div, signed) {
                (true, true) => Opcode::DivS {
                    dest: vr(2),
                    src1: vr(0),
                    src2: vr(1),
                },
                (true, false) => Opcode::DivU {
                    dest: vr(2),
                    src1: vr(0),
                    src2: vr(1),
                },
                (false, true) => Opcode::RemS {
                    dest: vr(2),
                    src1: vr(0),
                    src2: vr(1),
                },
                (false, false) => Opcode::RemU {
                    dest: vr(2),
                    src1: vr(0),
                    src2: vr(1),
                },
            },
        ];
        ops.into_iter().map(inst).collect()
    }

    fn udf_count(arm: &[ArmOp]) -> usize {
        arm.iter()
            .filter(|op| matches!(op, ArmOp::Udf { .. }))
            .count()
    }

    /// `const_div_ir` under REGISTER PRESSURE: six pad constants live across
    /// the division exhaust the R4-R8 pool, so the flag-on pre-step must act
    /// (the population the guard elision is scoped to).
    fn pressure_div_ir(div: bool, signed: bool, c: i32) -> Vec<Instruction> {
        let mut ops = vec![Opcode::Load {
            dest: vr(0),
            addr: 0,
        }];
        for i in 0..6u32 {
            ops.push(Opcode::Const {
                dest: vr(1 + i),
                value: (11 * (i + 1)) as i32,
            });
        }
        ops.push(Opcode::Const {
            dest: vr(7),
            value: c,
        });
        ops.push(match (div, signed) {
            (true, true) => Opcode::DivS {
                dest: vr(8),
                src1: vr(0),
                src2: vr(7),
            },
            (true, false) => Opcode::DivU {
                dest: vr(8),
                src1: vr(0),
                src2: vr(7),
            },
            (false, true) => Opcode::RemS {
                dest: vr(8),
                src1: vr(0),
                src2: vr(7),
            },
            (false, false) => Opcode::RemU {
                dest: vr(8),
                src1: vr(0),
                src2: vr(7),
            },
        });
        // Fold the pads + the quotient so everything is live across the div.
        let mut acc = 8u32;
        for i in 0..6u32 {
            ops.push(Opcode::Add {
                dest: vr(9 + i),
                src1: vr(acc),
                src2: vr(1 + i),
            });
            acc = 9 + i;
        }
        ops.into_iter().map(inst).collect()
    }

    #[test]
    fn test_242_div_const_guards_elided_on_exhausted_function() {
        // Nonzero, non-minus-one constant divisor UNDER PRESSURE (the spill
        // machinery fires): both DivS guards go.
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let arm = bridge
            .ir_to_arm(&pressure_div_ir(true, true, 1000), 1)
            .unwrap();
        assert!(
            bridge.spill_on_exhaust_fired(),
            "precondition: the pressure shape must exercise the machinery"
        );
        assert_eq!(udf_count(&arm), 0, "no trap guard may survive: {arm:#?}");
        assert!(
            arm.iter().any(|op| matches!(op, ArmOp::Sdiv { .. })),
            "the division itself must remain"
        );
        // DivU / RemS / RemU: the zero guard goes too.
        for (div, signed) in [(true, false), (false, true), (false, false)] {
            let arm = bridge
                .ir_to_arm(&pressure_div_ir(div, signed, 7), 1)
                .unwrap();
            assert_eq!(udf_count(&arm), 0, "div={div} signed={signed}: {arm:#?}");
        }
    }

    #[test]
    fn test_242_div_const_guards_kept_flag_off() {
        // Flag off: byte-identical to shipping — every guard stays.
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(false);
        let arm = bridge
            .ir_to_arm(&const_div_ir(true, true, 1000), 1)
            .unwrap();
        assert_eq!(udf_count(&arm), 2, "flag-off keeps both DivS guards");
        assert!(!bridge.spill_on_exhaust_fired());
    }

    #[test]
    fn test_242_div_const_guards_kept_on_untouched_function_flag_on() {
        // THE SCOPING CONTRACT (`vcr_ver_001_gate_242`): a function the
        // exhaustion machinery never touches must stay byte-identical flag-on
        // — the wrapper detects elision-without-action and rebuilds with the
        // guards in place.
        let mut on = OptimizerBridge::new();
        on.set_spill_on_exhaust(true);
        let arm_on = on.ir_to_arm(&const_div_ir(true, true, 1000), 1).unwrap();
        assert!(!on.spill_on_exhaust_fired(), "no pressure: nothing fired");
        let mut off = OptimizerBridge::new();
        off.set_spill_on_exhaust(false);
        let arm_off = off.ir_to_arm(&const_div_ir(true, true, 1000), 1).unwrap();
        assert_eq!(arm_on, arm_off, "flag-on must be byte-identical here");
        assert_eq!(udf_count(&arm_on), 2);
    }

    #[test]
    fn test_242_div_const_guards_kept_for_trapping_constants() {
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        // C = 0 always traps: both guards stay (the zero guard IS the trap).
        let arm = bridge
            .ir_to_arm(&pressure_div_ir(true, true, 0), 1)
            .unwrap();
        assert_eq!(udf_count(&arm), 2, "zero divisor keeps every guard");
        // C = -1: zero guard elided, INT_MIN/-1 overflow guard MUST stay.
        let arm = bridge
            .ir_to_arm(&pressure_div_ir(true, true, -1), 1)
            .unwrap();
        assert_eq!(udf_count(&arm), 1, "-1 divisor keeps the overflow guard");
        assert!(
            arm.iter().any(|op| matches!(op, ArmOp::Udf { imm: 1 })),
            "the surviving guard is the overflow trap"
        );
        // RemS by -1 never overflows: zero guard elided, nothing else exists.
        let arm = bridge
            .ir_to_arm(&pressure_div_ir(false, true, -1), 1)
            .unwrap();
        assert_eq!(udf_count(&arm), 0, "rem_s by -1 needs no guard");
    }

    #[test]
    fn test_242_div_const_map_distrusts_redefined_vreg() {
        // The divisor vreg is redefined after the Const — the single-def scan
        // must poison it and KEEP the guards (a stale constant here would be
        // a silent unsoundness, the #582 class).
        let mut ops = const_div_ir(true, true, 1000);
        ops.insert(
            2,
            inst(Opcode::Add {
                dest: vr(1), // redefines the "constant" vreg
                src1: vr(0),
                src2: vr(0),
            }),
        );
        let mut bridge = OptimizerBridge::new();
        bridge.set_spill_on_exhaust(true);
        let arm = bridge.ir_to_arm(&ops, 1).unwrap();
        assert_eq!(
            udf_count(&arm),
            2,
            "redefined divisor vreg: every guard must stay: {arm:#?}"
        );
    }
}
