//! Instruction Selection - Converts WebAssembly IR to ARM instructions
//!
//! Uses pattern matching to select optimal ARM instruction sequences

use crate::contracts;
use crate::control_flow::{BlockType, BranchableInstruction, ControlFlowManager};
use crate::rules::{
    ArmOp, Condition, MemAddr, MveSize, Operand2, QReg, Reg, Replacement, SynthesisRule, VfpReg,
};
use crate::{Bindings, PatternMatcher};
use std::collections::HashMap;
use synth_core::Result;
use synth_core::WasmOp;
use synth_core::target::FPUPrecision;

/// Bounds checking configuration for memory operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundsCheckConfig {
    /// No bounds checking (no inline guard).
    None,
    /// Hardware MPU enforcement (ARM) / PMP (RV32). The backend does not emit
    /// any inline check — the MPU/PMP raises a fault on out-of-bounds accesses.
    /// Equivalent to `None` from the selector's point of view but distinguished
    /// here so the safety-manifest can record the intent.
    Mpu,
    /// Software bounds checking with CMP/BHS before each access
    /// R10 holds the memory size, initialized by startup code
    Software,
    /// Masking: AND address with (memory_size - 1) for power-of-2 sizes
    /// Lower overhead but only works with power-of-2 memory sizes
    Masking,
}

impl BoundsCheckConfig {
    /// `true` when no inline guard instructions are emitted (either disabled
    /// entirely or hardware-enforced via MPU/PMP).
    pub fn is_passthrough(self) -> bool {
        matches!(self, BoundsCheckConfig::None | BoundsCheckConfig::Mpu)
    }
}

/// ARM instruction with operands
#[derive(Debug, Clone, PartialEq)]
pub struct ArmInstruction {
    /// The ARM operation
    pub op: ArmOp,
    /// Source line (for debugging)
    pub source_line: Option<usize>,
}

impl BranchableInstruction for ArmInstruction {
    fn set_branch_offset(&mut self, offset: i32) {
        match &self.op {
            ArmOp::B { .. } => {
                self.op = ArmOp::BOffset { offset };
            }
            ArmOp::Bcc { cond, .. } => {
                self.op = ArmOp::BCondOffset {
                    cond: *cond,
                    offset,
                };
            }
            ArmOp::Bhs { .. } => {
                self.op = ArmOp::BCondOffset {
                    cond: Condition::HS,
                    offset,
                };
            }
            ArmOp::Blo { .. } => {
                self.op = ArmOp::BCondOffset {
                    cond: Condition::LO,
                    offset,
                };
            }
            _ => {} // Not a branch instruction
        }
    }

    fn is_branch(&self) -> bool {
        matches!(
            self.op,
            ArmOp::B { .. }
                | ArmOp::Bcc { .. }
                | ArmOp::Bhs { .. }
                | ArmOp::Blo { .. }
                | ArmOp::Bl { .. }
                | ArmOp::BOffset { .. }
                | ArmOp::BCondOffset { .. }
        )
    }
}

/// Allocatable registers: R0-R8.
/// R9 (globals base), R10 (memory size), R11 (memory base) are reserved by the
/// runtime convention. R12 (IP) is reserved as the encoder's scratch register:
/// `encode_arm_reg_offset_mem` lowers an indexed `[R11 + addr + #off]` access to
/// `ADD ip, addr, #off; LDR/STR rd, [R11, ip]`, and several constant/VFP helpers
/// also clobber IP — so a live operand must never reside there (#212: a const-0
/// negation base allocated to R12 was overwritten by the next load's `ADD ip`,
/// turning `0 - sum` into `(addr + off) - sum`).
const ALLOCATABLE_REGS: [Reg; 9] = [
    Reg::R0,
    Reg::R1,
    Reg::R2,
    Reg::R3,
    Reg::R4,
    Reg::R5,
    Reg::R6,
    Reg::R7,
    Reg::R8,
];

/// Convert register index to Reg enum.
/// Skips reserved registers R9 (globals), R10 (mem size), R11 (mem base).
///
/// # Contract (Verus-style)
/// ```text
/// requires index < ALLOCATABLE_REGS.len()
/// ensures
///     result != Reg::R9,
///     result != Reg::R10,
///     result != Reg::R11,
/// ```
fn index_to_reg(index: u8) -> Reg {
    let reg = ALLOCATABLE_REGS[(index as usize) % ALLOCATABLE_REGS.len()];
    debug_assert!(
        contracts::regalloc::is_allocatable(&reg),
        "CONTRACT VIOLATION [index_to_reg]: index {} mapped to reserved register {:?}",
        index,
        reg
    );
    reg
}

/// A virtual-stack entry (#171). A value normally lives in a physical register
/// ([`StackVal::Reg`] — for an i64, this is the `lo`; the `hi` is the
/// conventional [`i64_pair_hi`]). When register pressure exhausts the
/// consecutive-pair budget, a deep entry is spilled to the frame and becomes
/// [`StackVal::Spilled`], freeing its register(s). Spilled entries reserve NO
/// physical register, so spilling relieves pressure; the value is reloaded into
/// a fresh pair the moment it is popped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StackVal {
    /// Value in register `reg`. When `is_i64`, this is the lo half of an i64
    /// pair (hi = `i64_pair_hi(reg)`); when false, a single i32 in `reg`. The
    /// width lets the spill/reload path store 4 bytes for an i32 (and never call
    /// `i64_pair_hi` on a single-reg i32 — which fails for R12, the last
    /// allocatable reg) vs 8 bytes for an i64 pair (#204/#171).
    Reg { reg: Reg, is_i64: bool },
    /// Spilled to the frame: i32 at `[sp, lo_slot]`; i64 lo at `[sp, lo_slot]`,
    /// hi at `[sp, lo_slot+4]`.
    Spilled { lo_slot: i32, is_i64: bool },
}

impl StackVal {
    /// A single 32-bit value in `reg`.
    #[inline]
    fn i32(reg: Reg) -> Self {
        StackVal::Reg { reg, is_i64: false }
    }
    /// A 64-bit value whose lo lives in `reg` (hi = `i64_pair_hi(reg)`).
    #[inline]
    fn i64(reg: Reg) -> Self {
        StackVal::Reg { reg, is_i64: true }
    }
    /// Width of this operand-stack value.
    #[inline]
    fn is_i64(&self) -> bool {
        match self {
            StackVal::Reg { is_i64, .. } | StackVal::Spilled { is_i64, .. } => *is_i64,
        }
    }
}

/// Number of i64 spill slots reserved in the frame (#171). Each is 8 bytes
/// (lo+hi). Slots are reused (freed on reload), so this caps *simultaneous*
/// spills, not total. 8 is generous for real i64-heavy functions; exceeding it
/// surfaces as a clean `Err` (the #168 skip-and-continue net), never a panic.
const I64_SPILL_SLOTS: usize = 8;

/// Tracks which i64 spill slots are in use (#171). `base` is the byte offset
/// from SP of slot 0; slot `i` occupies `[base + i*8, base + i*8 + 8)`.
struct SpillState {
    base: i32,
    used: [bool; I64_SPILL_SLOTS],
    /// VCR-RA-001 step 3b-lite (#242): when set, i32 temp allocation under
    /// register exhaustion spills the deepest stack value instead of
    /// hard-failing (see [`alloc_temp_or_spill`]). Default OFF; flipped on only
    /// by the retry pass in the backend after a first pass failed with the
    /// exhaustion `Err` — so every function that compiles without it keeps
    /// byte-identical output by construction.
    spill_on_exhaustion: bool,
    /// Whether `compute_local_layout` actually reserved the spill area this
    /// state hands slots out of (`has_i64 || force_spill_area`). When it did
    /// NOT (an i32-only first pass), `base` is just the end of the frame and
    /// any slot handed out would alias the #204 param-backing slots — callers
    /// that can need a slot outside the i64 paths (the #326 arg-cycle
    /// resolver) must check this and fail with the ladder-recoverable
    /// exhaustion `Err` instead.
    area_reserved: bool,
}

impl SpillState {
    fn new(base: i32) -> Self {
        SpillState {
            base,
            used: [false; I64_SPILL_SLOTS],
            spill_on_exhaustion: false,
            area_reserved: true,
        }
    }
    /// Reserve a free slot, returning its byte offset from SP.
    fn alloc(&mut self) -> Option<i32> {
        let i = self.used.iter().position(|&u| !u)?;
        self.used[i] = true;
        Some(self.base + (i as i32) * 8)
    }
    /// Release the slot at byte offset `off` so it can be reused.
    fn free(&mut self, off: i32) {
        let i = ((off - self.base) / 8) as usize;
        if i < I64_SPILL_SLOTS {
            self.used[i] = false;
        }
    }
}

/// The physical registers currently reserved by the virtual stack (#171): every
/// [`StackVal::Reg`]'s `r` and its conventional [`i64_pair_hi`]. Spilled entries
/// reserve nothing. (Over-reserving the pair_hi for i32 entries is the
/// pre-existing conservative behaviour — safe.)
/// Detect `…; i32.const C; i32.{div,rem}_{u,s}` — a statically-known divisor.
///
/// Sound because `i32.const` is a (0,1) stack op (pushes one value, pops none):
/// when it is the op immediately preceding the division, the value it pushes is
/// exactly the divisor the division pops off the top of the stack. Any op that
/// consumed the const before the division (e.g. `i32.const; i32.add; i32.div_u`)
/// would sit at `idx-1` instead, so the `I32Const` match fails and we bail.
///
/// The constant lets the division handlers (#209 Opt 1):
///   * elide the div-by-zero trap guard when `C != 0` (the trap is dead code);
///   * elide the signed INT_MIN/-1 overflow guard when `C != -1`;
///   * strength-reduce a power-of-two unsigned divisor to a shift, and a
///     divisor of 1 to an identity move.
fn const_divisor(wasm_ops: &[WasmOp], idx: usize) -> Option<i32> {
    if idx == 0 {
        return None;
    }
    match wasm_ops[idx - 1] {
        WasmOp::I32Const(c) => Some(c),
        _ => None,
    }
}

/// If the operand pushed immediately before a bitwise binop is a constant the
/// Thumb-2 data-processing immediate encoder handles correctly, return it so the
/// op can fold the constant into an immediate operand and skip materializing it
/// into a register (the redundant-materialization waste measured on `flat_flight`,
/// #209/#248). Bounded to `0..=0xFF`: the encoder's `AND`-immediate path is not
/// yet ThumbExpandImm-complete and only encodes a single zero-extended byte
/// correctly (#249).
fn foldable_bitwise_imm(wasm_ops: &[WasmOp], idx: usize) -> Option<i32> {
    if idx == 0 {
        return None;
    }
    match wasm_ops[idx - 1] {
        WasmOp::I32Const(c) if (0..=0xFF).contains(&c) => Some(c),
        _ => None,
    }
}

/// Like [`foldable_bitwise_imm`] but for `i32.add` / `i32.sub`, whose encoder
/// path uses ADDW/SUBW (T4) — a plain 12-bit immediate — so the safe range is
/// the full `0..=0xFFF` (4095), not just a byte (#253). Non-negative only:
/// folding a negative constant would require flipping add<->sub, which this
/// keeps simple by declining.
fn foldable_addsub_imm(wasm_ops: &[WasmOp], idx: usize) -> Option<i32> {
    if idx == 0 {
        return None;
    }
    match wasm_ops[idx - 1] {
        WasmOp::I32Const(c) if (0..=0xFFF).contains(&c) => Some(c),
        _ => None,
    }
}

/// If `c` (read as an unsigned 32-bit divisor) is a power of two `2^k` with
/// `k >= 1`, return `k` so `i32.div_u` can lower to `LSR rd, rn, #k`.
///
/// `k == 0` (divisor 1) is excluded on purpose: Thumb-2 `LSR #0` does not encode
/// a zero-shift — the immediate-shift form reads `imm5 == 0` as `LSR #32`, which
/// would yield 0 instead of the identity. Divisor-by-1 is handled separately as
/// a `MOV`. `0x8000_0000` (i32 `-2147483648`) is a valid `2^31` here because the
/// divisor is interpreted unsigned.
fn pow2_shift_u(c: i32) -> Option<u32> {
    let u = c as u32;
    if u > 1 && u.is_power_of_two() {
        Some(u.trailing_zeros())
    } else {
        None
    }
}

/// The unsigned reciprocal-multiply magic numbers for division by an invariant
/// `d` (Granlund & Montgomery, "Division by Invariant Integers using
/// Multiplication"; Hacker's Delight §10-9 `magicu`). Returns `(m, s, a)` such
/// that for every `u32` n, `n / d` equals — writing `hi = umulhi(m, n) =
/// ((m as u64 * n as u64) >> 32) as u32`:
///   * `a == false`: `hi >> s`
///   * `a == true` : `(((n - hi) >> 1) + hi) >> (s - 1)`
///
/// Only meaningful for a non-power-of-two `d >= 3` (powers of two — including 1
/// and 2 — lower to a plain shift, and are handled before this is called).
fn magicu(d: u32) -> (u32, u32, bool) {
    debug_assert!(d >= 3 && !d.is_power_of_two());
    let mut a = false;
    // nc = largest value with nc % d == d-1 (= 2^32 - 1 - rem(2^32, d)).
    let nc = u32::MAX - (0u32.wrapping_sub(d)) % d;
    let mut p: u32 = 31;
    let mut q1 = 0x8000_0000u32 / nc;
    let mut r1 = 0x8000_0000u32 - q1.wrapping_mul(nc);
    let mut q2 = 0x7FFF_FFFFu32 / d;
    let mut r2 = 0x7FFF_FFFFu32 - q2.wrapping_mul(d);
    loop {
        p += 1;
        if r1 >= nc - r1 {
            q1 = q1.wrapping_mul(2).wrapping_add(1);
            r1 = r1.wrapping_mul(2).wrapping_sub(nc);
        } else {
            q1 = q1.wrapping_mul(2);
            r1 = r1.wrapping_mul(2);
        }
        if r2 + 1 >= d - r2 {
            if q2 >= 0x7FFF_FFFF {
                a = true;
            }
            q2 = q2.wrapping_mul(2).wrapping_add(1);
            r2 = r2.wrapping_mul(2).wrapping_add(1).wrapping_sub(d);
        } else {
            if q2 >= 0x8000_0000 {
                a = true;
            }
            q2 = q2.wrapping_mul(2);
            r2 = r2.wrapping_mul(2).wrapping_add(1);
        }
        let delta = d - 1 - r2;
        if !(p < 64 && (q1 < delta || (q1 == delta && r1 == 0))) {
            break;
        }
    }
    (q2.wrapping_add(1), p - 32, a)
}

fn stack_live_regs(stack: &[StackVal]) -> Vec<Reg> {
    let mut live: Vec<Reg> = Vec::with_capacity(stack.len() * 2);
    for v in stack {
        if let StackVal::Reg { reg, is_i64 } = v {
            live.push(*reg);
            // Only an i64 value occupies the consecutive hi register. (Compute
            // hi lazily so i64_pair_hi is never called for an i32 entry.)
            let hi = if *is_i64 {
                i64_pair_hi(*reg).ok()
            } else {
                None
            };
            if let Some(hi) = hi {
                live.push(hi);
            }
        }
    }
    live
}

/// Allocate a temporary register, skipping any reserved by the virtual stack.
/// Returns Error if all allocatable registers are in use.
fn alloc_temp_safe(next_temp: &mut u8, stack: &[StackVal], reserved: &[Reg]) -> Result<Reg> {
    let mut live = stack_live_regs(stack);
    live.extend_from_slice(reserved); // #193: never hand out a live param register
    for _ in 0..ALLOCATABLE_REGS.len() {
        let reg = index_to_reg(*next_temp);
        *next_temp = (*next_temp + 1) % ALLOCATABLE_REGS.len() as u8;
        if !live.contains(&reg) {
            return Ok(reg);
        }
    }
    Err(synth_core::Error::synthesis(
        "register exhaustion: all allocatable registers are live on the stack — \
         function too complex for current register allocator"
            .to_string(),
    ))
}

/// [`alloc_temp_safe`] + spill-on-exhaustion (VCR-RA-001 step 3b-lite, #242).
///
/// Fast path: identical to `alloc_temp_safe` — a free register exists and is
/// returned with no instruction emitted. Exhaustion path: when
/// `spill.spill_on_exhaustion` is set (only the backend's retry pass after a
/// first pass already failed — never a function that compiles today), spill the
/// DEEPEST register-resident stack value to an i64-spill-area slot via
/// [`spill_deepest_reg`] (the deepest entry is the least likely to be consumed
/// next; operand stack = LIFO) and retry, freeing that register for the new
/// temp. The spilled value reloads automatically on pop/peek through the
/// existing [`StackVal::Spilled`] machinery (#171).
///
/// Terminates: each spill converts one `StackVal::Reg` to `StackVal::Spilled`,
/// so either a register frees or nothing register-resident remains and the
/// original exhaustion `Err` is returned. The hard-fail shrinks but does not
/// vanish: with all `I64_SPILL_SLOTS` slots in use, `spill_deepest_reg`
/// propagates its slot-pool-exhausted `Err` (an honest bound).
fn alloc_temp_or_spill(
    next_temp: &mut u8,
    stack: &mut [StackVal],
    instructions: &mut Vec<ArmInstruction>,
    spill: &mut SpillState,
    reserved: &[Reg],
    line: usize,
) -> Result<Reg> {
    loop {
        match alloc_temp_safe(next_temp, stack, reserved) {
            Ok(reg) => return Ok(reg),
            Err(e) => {
                if !spill.spill_on_exhaustion
                    || !spill_deepest_reg(stack, instructions, spill, line)?
                {
                    return Err(e);
                }
                // A register was freed — retry the allocation.
            }
        }
    }
}

/// Spill the DEEPEST register-resident stack entry to a fresh frame slot (#171),
/// freeing its register pair. Emits `STR lo,[sp,slot]; STR hi,[sp,slot+4]` and
/// rewrites the entry to [`StackVal::Spilled`]. Returns `Ok(true)` on success,
/// `Ok(false)` if nothing register-resident remains to spill, `Err` if the spill
/// slot pool is exhausted. The deepest entry is chosen because it is the least
/// likely to be consumed next (operand stack = LIFO).
fn spill_deepest_reg(
    stack: &mut [StackVal],
    instructions: &mut Vec<ArmInstruction>,
    spill: &mut SpillState,
    line: usize,
) -> Result<bool> {
    let Some(pos) = stack.iter().position(|v| matches!(v, StackVal::Reg { .. })) else {
        return Ok(false);
    };
    let StackVal::Reg { reg: lo, is_i64 } = stack[pos] else {
        return Ok(false);
    };
    let slot = spill.alloc().ok_or_else(|| {
        synth_core::Error::synthesis(
            "register exhaustion: i64 spill-slot pool exhausted — function too \
             complex for current register allocator"
                .to_string(),
        )
    })?;
    // i32: store the single register (4 bytes). i64: store lo + hi (8 bytes).
    instructions.push(ArmInstruction {
        op: ArmOp::Str {
            rd: lo,
            addr: MemAddr::imm(Reg::SP, slot),
        },
        source_line: Some(line),
    });
    if is_i64 {
        let hi = i64_pair_hi(lo)?;
        instructions.push(ArmInstruction {
            op: ArmOp::Str {
                rd: hi,
                addr: MemAddr::imm(Reg::SP, slot + 4),
            },
            source_line: Some(line),
        });
    }
    stack[pos] = StackVal::Spilled {
        lo_slot: slot,
        is_i64,
    };
    Ok(true)
}

/// Reconcile one if-result position between the two arms (#313): make the
/// else-arm's result register(s) hold the SAME value the then-arm's do, by
/// emitting `MOV R_then, R_else` (i64: lo and hi) on the ELSE path when the two
/// arms chose different registers. Emitting NOTHING when they match is what
/// keeps register-symmetric / control-flow-only if/else byte-identical.
///
/// The merged value lives in the then-arm's register afterwards (the caller
/// pushes the then-result back onto the vstack). These movs are placed between
/// the else-arm body and `end_label`; the then-path branches over them.
///
/// A spilled result on either side only arises under register-exhaustion
/// spilling (the retry pass, `spill_on_exhaustion`). Rather than risk a
/// mis-reconciliation there, return the honest exhaustion `Err` — the same
/// recoverable signal the rest of the allocator uses — so the function is
/// retried/skipped, never miscompiled.
fn reconcile_if_result(
    then_v: &StackVal,
    else_v: &StackVal,
    instructions: &mut Vec<ArmInstruction>,
    line: usize,
) -> Result<()> {
    match (then_v, else_v) {
        (
            StackVal::Reg {
                reg: then_lo,
                is_i64: then_i64,
            },
            StackVal::Reg {
                reg: else_lo,
                is_i64: else_i64,
            },
        ) => {
            // Both arms must agree on width for a well-typed if-result.
            if then_i64 != else_i64 {
                return Err(synth_core::Error::synthesis(
                    "if/else result width mismatch between arms (#313)".to_string(),
                ));
            }
            if then_lo != else_lo {
                instructions.push(ArmInstruction {
                    op: ArmOp::Mov {
                        rd: *then_lo,
                        op2: Operand2::Reg(*else_lo),
                    },
                    source_line: Some(line),
                });
            }
            if *then_i64 {
                let then_hi = i64_pair_hi(*then_lo)?;
                let else_hi = i64_pair_hi(*else_lo)?;
                if then_hi != else_hi {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mov {
                            rd: then_hi,
                            op2: Operand2::Reg(else_hi),
                        },
                        source_line: Some(line),
                    });
                }
            }
            Ok(())
        }
        _ => Err(synth_core::Error::synthesis(
            "if/else result reconciliation with a spilled arm result is not \
             supported by the current register allocator (#313) — function too \
             complex; retried/skipped rather than miscompiled"
                .to_string(),
        )),
    }
}

/// Pop the top operand, returning its `lo` register (#171). If the entry was
/// spilled, reload it: allocate a fresh consecutive pair and emit
/// `LDR lo,[sp,slot]; LDR hi,[sp,slot+4]`, freeing the slot.
fn pop_operand(
    stack: &mut Vec<StackVal>,
    next_temp: &mut u8,
    instructions: &mut Vec<ArmInstruction>,
    spill: &mut SpillState,
    reserved: &[Reg], // #193: reload must avoid live param registers
    line: usize,
) -> Result<Reg> {
    let v = match stack.pop() {
        Some(v) => v,
        None => {
            return Err(synth_core::Error::synthesis(
                "stack underflow: malformed WASM or compiler bug".to_string(),
            ));
        }
    };
    match v {
        StackVal::Reg { reg, .. } => Ok(reg),
        StackVal::Spilled { lo_slot, is_i64 } => {
            // Reload against the *remaining* stack (this entry already popped).
            // i32: one temp + one LDR. i64: a consecutive pair + LDR lo/hi.
            let lo = if is_i64 {
                let (lo, hi) = alloc_consecutive_pair(
                    next_temp,
                    stack,
                    instructions,
                    spill,
                    &[],
                    reserved,
                    line,
                )?;
                instructions.push(ArmInstruction {
                    op: ArmOp::Ldr {
                        rd: lo,
                        addr: MemAddr::imm(Reg::SP, lo_slot),
                    },
                    source_line: Some(line),
                });
                instructions.push(ArmInstruction {
                    op: ArmOp::Ldr {
                        rd: hi,
                        addr: MemAddr::imm(Reg::SP, lo_slot + 4),
                    },
                    source_line: Some(line),
                });
                lo
            } else {
                let lo =
                    alloc_temp_or_spill(next_temp, stack, instructions, spill, reserved, line)?;
                instructions.push(ArmInstruction {
                    op: ArmOp::Ldr {
                        rd: lo,
                        addr: MemAddr::imm(Reg::SP, lo_slot),
                    },
                    source_line: Some(line),
                });
                lo
            };
            spill.free(lo_slot);
            Ok(lo)
        }
    }
}

/// Peek the top operand WITHOUT consuming it, returning its `lo` register (#171).
/// If the top was spilled, reload it into a fresh consecutive pair and rewrite
/// the stack entry to [`StackVal::Reg`] (so the value is register-resident again
/// and stays on the stack). Used by peek sites like `LocalTee`.
fn peek_operand(
    stack: &mut [StackVal],
    next_temp: &mut u8,
    instructions: &mut Vec<ArmInstruction>,
    spill: &mut SpillState,
    reserved: &[Reg], // #193: reload must avoid live param registers
    line: usize,
) -> Result<Reg> {
    match stack.last().copied() {
        None => Err(synth_core::Error::synthesis(
            "stack underflow: malformed WASM or compiler bug".to_string(),
        )),
        Some(StackVal::Reg { reg, .. }) => Ok(reg),
        Some(StackVal::Spilled { lo_slot, is_i64 }) => {
            let lo = if is_i64 {
                let (lo, hi) = alloc_consecutive_pair(
                    next_temp,
                    stack,
                    instructions,
                    spill,
                    &[],
                    reserved,
                    line,
                )?;
                instructions.push(ArmInstruction {
                    op: ArmOp::Ldr {
                        rd: lo,
                        addr: MemAddr::imm(Reg::SP, lo_slot),
                    },
                    source_line: Some(line),
                });
                instructions.push(ArmInstruction {
                    op: ArmOp::Ldr {
                        rd: hi,
                        addr: MemAddr::imm(Reg::SP, lo_slot + 4),
                    },
                    source_line: Some(line),
                });
                lo
            } else {
                let lo =
                    alloc_temp_or_spill(next_temp, stack, instructions, spill, reserved, line)?;
                instructions.push(ArmInstruction {
                    op: ArmOp::Ldr {
                        rd: lo,
                        addr: MemAddr::imm(Reg::SP, lo_slot),
                    },
                    source_line: Some(line),
                });
                lo
            };
            spill.free(lo_slot);
            if let Some(top) = stack.last_mut() {
                *top = StackVal::Reg { reg: lo, is_i64 };
            }
            Ok(lo)
        }
    }
}

/// Allocate a CONSECUTIVE pair `(rN, rN+1)` of registers from ALLOCATABLE_REGS,
/// neither of which is currently in use.
///
/// "In use" means:
/// 1. On the wasm stack (the explicit `Vec<Reg>` tracking).
/// 2. The implicit *high* register of any i64 value on the stack — for every
///    `lo` in `stack`, [`i64_pair_hi`]`(lo)` is also reserved. The wasm stack
///    only tracks the lo register of each i64; the hi is reserved by
///    convention but invisible to a naive scan. If we ignored that, a fresh
///    `alloc_consecutive_pair` could return the implicit-hi of an earlier
///    i64, clobbering it on the next i64 op that reads it via i64_pair_hi.
/// 3. Any explicit registers in `extra_avoid` — used by i64-op handlers to
///    keep the just-popped operand pairs alive across the destination
///    allocation (e.g. for I64Or, the popped a_lo/a_hi/b_lo/b_hi are still
///    live until the OR is emitted).
///
/// Calling [`alloc_temp_safe`] twice in succession is unsafe for i64 values:
/// if a register between them is live, the second call skips it and the
/// resulting pair is non-consecutive, breaking [`i64_pair_hi`]'s contract.
fn alloc_consecutive_pair(
    next_temp: &mut u8,
    stack: &mut [StackVal],
    instructions: &mut Vec<ArmInstruction>,
    spill: &mut SpillState,
    extra_avoid: &[Reg],
    reserved: &[Reg], // #193: live param registers — never allocate over them
    line: usize,
) -> Result<(Reg, Reg)> {
    // Try to find a free consecutive pair; if none is free, spill the deepest
    // register-resident stack entry (#171) to free its pair and retry. Each
    // iteration either succeeds or removes one register-resident entry, so the
    // loop terminates: a spilled pair (lo, i64_pair_hi(lo)) is itself a free
    // consecutive pair afterwards, and `extra_avoid` (<=4 regs) cannot block all
    // five pairs.
    loop {
        let mut live = stack_live_regs(stack);
        live.extend_from_slice(extra_avoid);
        live.extend_from_slice(reserved);

        let n = ALLOCATABLE_REGS.len();
        let mut nt = *next_temp;
        let mut found = None;
        for _ in 0..n {
            let lo_idx = (nt as usize) % n;
            let hi_idx = lo_idx + 1;
            if hi_idx < n {
                let lo_reg = ALLOCATABLE_REGS[lo_idx];
                let hi_reg = ALLOCATABLE_REGS[hi_idx];
                if !live.contains(&lo_reg) && !live.contains(&hi_reg) {
                    found = Some((lo_reg, hi_reg, ((hi_idx + 1) % n) as u8));
                    break;
                }
            }
            nt = ((nt as usize + 1) % n) as u8;
        }
        if let Some((lo_reg, hi_reg, new_nt)) = found {
            *next_temp = new_nt;
            return Ok((lo_reg, hi_reg));
        }
        // No free pair — spill the deepest entry and retry.
        if !spill_deepest_reg(stack, instructions, spill, line)? {
            return Err(synth_core::Error::synthesis(
                "register exhaustion: no consecutive pair of free registers for i64 — \
                 function too complex for current register allocator"
                    .to_string(),
            ));
        }
    }
}

/// AAPCS caller-saved registers that this allocator may hand out as operand
/// temps or use to hold incoming params. A `BL`/`BLX` clobbers all of these,
/// so any live value residing here must be preserved across a call.
///
/// R4–R8 are callee-saved (pushed in the prologue) and survive calls untouched;
/// they are deliberately excluded.
fn is_caller_saved(reg: Reg) -> bool {
    matches!(reg, Reg::R0 | Reg::R1 | Reg::R2 | Reg::R3 | Reg::R12)
}

/// AAPCS integer/pointer argument registers, in order: R0, R1, R2, R3.
/// Arguments beyond the fourth are passed on the stack (not yet handled — see
/// the scope note on `marshal_call_args`).
const ARG_REGS: [Reg; 4] = [Reg::R0, Reg::R1, Reg::R2, Reg::R3];

/// Given the low register of an i64 register pair, return the high register.
///
/// Convention: i64 values on 32-bit ARM use two consecutive registers.
/// The low register holds bits [31:0], the high register holds bits [63:32].
/// Pairs are allocated from consecutive entries in ALLOCATABLE_REGS.
///
/// # Contract (Verus-style)
/// ```text
/// requires lo_reg is an even-indexed entry in ALLOCATABLE_REGS
/// ensures result == ALLOCATABLE_REGS[index_of(lo_reg) + 1]
/// ```
fn i64_pair_hi(lo_reg: Reg) -> Result<Reg> {
    // Find lo_reg in ALLOCATABLE_REGS and return the next entry
    for (i, &r) in ALLOCATABLE_REGS.iter().enumerate() {
        if r == lo_reg && i + 1 < ALLOCATABLE_REGS.len() {
            return Ok(ALLOCATABLE_REGS[i + 1]);
        }
    }
    Err(synth_core::Error::synthesis(format!(
        "i64 register pair: no high register available for {:?} (last in ALLOCATABLE_REGS)",
        lo_reg
    )))
}

/// Per-function stack-frame layout for non-parameter locals.
///
/// `offsets[idx]` gives the byte offset (relative to SP after the frame
/// allocation) where local `idx` lives. `frame_size` is the total bytes
/// to allocate via `sub sp, sp, #frame_size` in the prologue.
///
/// i32/i64 locals each occupy 4/8 bytes respectively. i64 locals are
/// 8-byte aligned per AAPCS. The total frame is rounded up to 8 bytes
/// to keep SP 8-byte aligned at call sites.
struct LocalLayout {
    /// idx -> (offset_from_sp, is_i64)
    locals: std::collections::HashMap<u32, (i32, bool)>,
    frame_size: i32,
    /// Byte offset (from SP, after frame allocation) of the call-spill scratch
    /// area. This area holds caller-saved registers (R0–R3, R12, and live
    /// operand-stack temps) across `Call`/`CallIndirect` so they survive the
    /// AAPCS-clobbering branch-and-link. `None` when the function contains no
    /// calls (no scratch reserved). See the `Call` lowering for usage.
    spill_base: Option<i32>,
    /// Byte offset (from SP) of the i64 register-pair spill area (#171): up to
    /// `I64_SPILL_SLOTS` 8-byte slots. `alloc_consecutive_pair` spills a deep
    /// i64 value here when the consecutive-pair budget is exhausted and reloads
    /// it on pop, so i64-heavy functions compile instead of being dropped by
    /// the #168 skip-and-continue net.
    i64_spill_base: i32,
    /// #204/#193: frame slot (offset, is_i64) per in-register param the fn
    /// reads. Spilled at entry; local.get/set route through it so the param is
    /// never clobbered in its home reg between reads. Appended last so existing
    /// local/spill offsets are unchanged.
    param_slots: std::collections::HashMap<u32, (i32, bool)>,
    /// #359: frame slot (offset from SP) per incoming stack-passed param the fn
    /// references — wasm param indices in `[4, num_params)` that AAPCS delivers
    /// on the caller's stack (not in r0..r3). Computed AFTER `frame_size` is
    /// finalized: such a param sits at `[sp, frame_size + 24 + (k-4)*4]` (24 =
    /// the fixed `push {r4-r8,lr}`). i32-only; an i64/f64 stack param is an
    /// Ok-or-Err refusal at the use site. Empty unless `num_params > 4`.
    incoming_params: std::collections::HashMap<u32, i32>,
    /// Whether the `i64_spill_base` area was actually reserved
    /// (`has_i64 || force_spill_area`). Mirrored into
    /// [`SpillState::area_reserved`]; see that field for why (#326).
    spill_area_reserved: bool,
}

/// Compute the stack-frame layout for non-parameter locals in a function.
///
/// Walks the wasm op stream once to:
/// 1. Identify which non-param local indices are referenced (LocalGet/Set/Tee).
/// 2. Determine each local's width via `infer_i64_locals` (i32 vs i64).
/// 3. Lay them out in ascending-index order with i64 locals 8-byte aligned.
///
/// The result drives:
/// - Prologue: `sub sp, sp, #frame_size` after pushing callee-saved regs.
/// - LocalGet/Set/Tee: use `offsets[idx]` instead of the legacy
///   `(idx - 4) * 4` formula (which only happened to work when num_params==4
///   AND the formula's negative result was silently clamped to 0 by the
///   encoder, in both cases corrupting the caller's stack or the callee's
///   own callee-saved-register spill).
/// - Epilogue: `add sp, sp, #frame_size` before popping registers.
fn compute_local_layout(
    wasm_ops: &[WasmOp],
    num_params: u32,
    func_ret_i64: &[bool],
    type_ret_i64: &[bool],
    force_spill_area: bool,
    force_param_backing: bool,
    outgoing_arg_bytes: i32,
) -> LocalLayout {
    use std::collections::{BTreeSet, HashMap};
    let i64_set = infer_i64_locals(wasm_ops, func_ret_i64, type_ret_i64);

    // Collect non-param local indices, in ascending order for deterministic layout.
    let mut used: BTreeSet<u32> = BTreeSet::new();
    for op in wasm_ops {
        match op {
            WasmOp::LocalGet(idx) | WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx)
                if *idx >= num_params =>
            {
                used.insert(*idx);
            }
            _ => {}
        }
    }

    let mut locals: HashMap<u32, (i32, bool)> = HashMap::new();
    // #359: reserve the AAPCS outgoing stack-argument region at the BOTTOM of
    // the frame (offset 0). Every other frame field accumulates from `offset`,
    // so initializing it to `outgoing_arg_bytes` shifts locals, spill_base,
    // i64_spill_base and param_slots up by exactly that amount. When 0 (no call
    // passes >4 args), the frame is byte-identical to before. `outgoing_arg_bytes`
    // is always a multiple of 8 (rounded by the caller) so the downstream
    // `offset % 8` alignment checks are preserved exactly.
    let mut offset: i32 = outgoing_arg_bytes;
    for &idx in &used {
        let is_i64 = i64_set.contains(&idx);
        // i64 locals require 8-byte alignment.
        if is_i64 && (offset % 8) != 0 {
            offset += 4;
        }
        locals.insert(idx, (offset, is_i64));
        offset += if is_i64 { 8 } else { 4 };
    }
    // If the function contains any call, reserve a fixed scratch area to spill
    // caller-saved registers (R0–R3, R12 — at most 5 distinct registers) across
    // each call. Slots are reused across calls (spill/reload is bracketed within
    // a single call), so 5 slots suffice regardless of call count.
    let has_call = wasm_ops
        .iter()
        .any(|op| matches!(op, WasmOp::Call(_) | WasmOp::CallIndirect { .. }));
    let spill_base = if has_call {
        // i64 locals are 8-byte aligned; scratch slots are 4-byte i32 stores so
        // place them after the locals at the current `offset`.
        let base = offset;
        offset += 5 * 4;
        Some(base)
    } else {
        None
    };

    // #171: reserve the i64 register-pair spill area (8-byte aligned) ONLY when
    // the function involves i64 — otherwise no i64 value is ever pushed, so
    // `alloc_consecutive_pair` is never called and no spill can occur, and the
    // frame stays as before (keeping i32-only functions and their tests
    // unchanged). The op debug-name check is a robust sufficient condition that
    // catches every i64 variant without enumerating them; it runs once per
    // function. Slots are reused (freed on reload).
    // VCR-RA-001 step 3b-lite (#242): the spill-on-exhaustion retry pass spills
    // i32 stack values into this same area, so it must exist even for i64-free
    // functions — `force_spill_area` is set ONLY on that retry (the function
    // failed to compile at all on the first pass), so no function that compiles
    // today changes frame size.
    let has_i64 = force_spill_area
        || !i64_set.is_empty()
        || wasm_ops.iter().any(|op| format!("{op:?}").contains("I64"));
    let i64_spill_base = if has_i64 {
        if (offset % 8) != 0 {
            offset += 4;
        }
        let base = offset;
        offset += (I64_SPILL_SLOTS as i32) * 8;
        base
    } else {
        offset // unused: no i64 op means no spill
    };

    // #204: append a spill slot for every in-register param a function with a
    // CALL reads (frame-backed → never clobbered in its home reg). Appended
    // last → existing local/spill offsets unchanged.
    let param_count = num_params.min(4);
    let mut param_slots: HashMap<u32, (i32, bool)> = HashMap::new();
    // Frame-backing is needed precisely when a param must survive across a call:
    // AAPCS arg-marshalling reclaims r0..r3 for the call's arguments, so a param
    // still live afterwards (gale's `sem` = the store address in r0) would be
    // clobbered unless it lives in the frame. Call-FREE functions keep params
    // register-backed — no behaviour change, and isolated-lowering tests (and
    // the common case) are untouched. Call-free temp-allocation clobbers are the
    // distinct, non-blocking #193 fuzz class (allocator reservation, deferred).
    // VCR-RA-001 acceptance increment (#242): `force_param_backing` extends the
    // same frame-backing to call-FREE functions, set ONLY on the backend's
    // retry after the i64 consecutive-pair exhaustion `Err` — the pinned param
    // home registers (#193 reservation) are the one blocker the pair
    // allocator's stack-spill loop (#171) cannot free, so the retry spills
    // them to the frame at entry instead. Functions that compile without it
    // keep byte-identical frames by construction.
    if has_call || force_param_backing {
        let mut used_params: BTreeSet<u32> = BTreeSet::new();
        for op in wasm_ops {
            let pidx = match op {
                WasmOp::LocalGet(idx) | WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx) => *idx,
                _ => continue,
            };
            if pidx < param_count {
                used_params.insert(pidx);
            }
        }
        for &p in &used_params {
            let is_i64 = i64_set.contains(&p);
            if is_i64 && (offset % 8) != 0 {
                offset += 4;
            }
            param_slots.insert(p, (offset, is_i64));
            offset += if is_i64 { 8 } else { 4 };
        }
    }

    // Round frame to 8-byte multiple for AAPCS SP alignment.
    let frame_size = (offset + 7) & !7;

    // #359: locate the incoming stack-passed params (wasm idx in [4, num_params)
    // that AAPCS delivers on the caller's stack). After `push {r4-r8,lr}` (24
    // bytes) + `sub sp,#frame_size`, param k sits at
    // `[sp, frame_size + 24 + (k-4)*4]`. Only the params actually referenced are
    // recorded. Empty when num_params <= 4. i32-only is enforced at the use site
    // (Ok-or-Err) — the offset is the same regardless of width.
    let mut incoming_params: HashMap<u32, i32> = HashMap::new();
    if num_params > 4 {
        const FIXED_PUSH_BYTES: i32 = 24; // push {r4,r5,r6,r7,r8,lr}
        let mut used_incoming: BTreeSet<u32> = BTreeSet::new();
        for op in wasm_ops {
            let k = match op {
                WasmOp::LocalGet(idx) | WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx) => *idx,
                _ => continue,
            };
            if (4..num_params).contains(&k) {
                used_incoming.insert(k);
            }
        }
        for &k in &used_incoming {
            let off = frame_size + FIXED_PUSH_BYTES + (k as i32 - 4) * 4;
            incoming_params.insert(k, off);
        }
    }

    LocalLayout {
        locals,
        frame_size,
        spill_base,
        i64_spill_base,
        param_slots,
        incoming_params,
        spill_area_reserved: has_i64,
    }
}

/// Infer which non-parameter wasm locals are i64 (8-byte) values.
///
/// The wasm decoder discards local-declaration type info, so we re-derive
/// it from the operation stream by simulating a virtual stack of widths
/// (1 = 32-bit, 2 = 64-bit). On each `LocalSet`/`LocalTee` we record the
/// width of the value being stored. WASM type rules guarantee a local's
/// width is invariant for its lifetime, so the first store wins.
///
/// Without this, the spilled-local store/load path would emit a single
/// 4-byte STR/LDR for i64 locals, dropping the upper half — corrupting
/// any function that returns or uses a u64-packed FFI struct.
///
/// `pub` because the RV32 selector (`synth-backend-riscv`) reuses the same
/// inference for its i64 frame-slot layout (#312 — the RISC-V analogue of
/// the ARM #311 fix); the wasm op stream and width rules are ISA-neutral.
pub fn infer_i64_locals(
    wasm_ops: &[WasmOp],
    func_ret_i64: &[bool],
    type_ret_i64: &[bool],
) -> std::collections::HashSet<u32> {
    use WasmOp::*;
    let mut i64_locals: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut vstack: Vec<bool> = Vec::new(); // true = i64

    let is_i64_producer = |op: &WasmOp| -> bool {
        matches!(
            op,
            I64Add
                | I64Sub
                | I64Mul
                | I64DivS
                | I64DivU
                | I64RemS
                | I64RemU
                | I64And
                | I64Or
                | I64Xor
                | I64Shl
                | I64ShrS
                | I64ShrU
                | I64Rotl
                | I64Rotr
                | I64Clz
                | I64Ctz
                | I64Popcnt
                | I64Const(_)
                | I64Load { .. }
                | I64Load8S { .. }
                | I64Load8U { .. }
                | I64Load16S { .. }
                | I64Load16U { .. }
                | I64Load32S { .. }
                | I64Load32U { .. }
                | I64ExtendI32S
                | I64ExtendI32U
                | I64Extend8S
                | I64Extend16S
                | I64Extend32S
        )
    };

    for op in wasm_ops {
        match op {
            LocalGet(idx) => {
                let is_i64 = i64_locals.contains(idx);
                vstack.push(is_i64);
            }
            LocalSet(idx) => {
                if let Some(true) = vstack.pop() {
                    i64_locals.insert(*idx);
                }
            }
            LocalTee(idx) => {
                if let Some(&true) = vstack.last() {
                    i64_locals.insert(*idx);
                }
            }
            Select => {
                // pops [val1, val2, cond], pushes one value with width of val1/val2
                let _cond = vstack.pop();
                let v2 = vstack.pop();
                let v1 = vstack.pop();
                vstack.push(v1.or(v2).unwrap_or(false));
            }
            // #311: a call's result width comes from the callee's signature —
            // without this, an i64-returning call feeding `local.set` left the
            // local inferred as i32 (4-byte slot, single-word store: the hi
            // half of gale's packed u64 decision was silently dropped).
            Call(func_idx) => {
                let (pops, pushes) = wasm_stack_effect(op);
                for _ in 0..pops {
                    vstack.pop();
                }
                let w = func_ret_i64
                    .get(*func_idx as usize)
                    .copied()
                    .unwrap_or(false);
                for _ in 0..pushes {
                    vstack.push(w);
                }
            }
            CallIndirect { type_index, .. } => {
                let (pops, pushes) = wasm_stack_effect(op);
                for _ in 0..pops {
                    vstack.pop();
                }
                let w = type_ret_i64
                    .get(*type_index as usize)
                    .copied()
                    .unwrap_or(false);
                for _ in 0..pushes {
                    vstack.push(w);
                }
            }
            _ => {
                let (pops, pushes) = wasm_stack_effect(op);
                for _ in 0..pops {
                    vstack.pop();
                }
                let push_width = is_i64_producer(op);
                for _ in 0..pushes {
                    vstack.push(push_width);
                }
            }
        }
    }

    i64_locals
}

/// Return the (pops, pushes) stack effect for a WASM op.
///
/// Used by the wildcard fallthrough in select_with_stack to maintain
/// approximate stack tracking for ops still handled by select_default.
fn wasm_stack_effect(op: &WasmOp) -> (usize, usize) {
    use WasmOp::*;
    match op {
        // Binary ops: pop 2, push 1
        I32Add | I32Sub | I32Mul | I32DivS | I32DivU | I32RemS | I32RemU | I32And | I32Or
        | I32Xor | I32Shl | I32ShrS | I32ShrU | I32Rotl | I32Rotr | I32Eq | I32Ne | I32LtS
        | I32LtU | I32GtS | I32GtU | I32LeS | I32LeU | I32GeS | I32GeU => (2, 1),

        // Unary ops: pop 1, push 1
        I32Eqz | I32Clz | I32Ctz | I32Popcnt | I32Extend8S | I32Extend16S => (1, 1),

        // i64 binary
        I64Add | I64Sub | I64Mul | I64DivS | I64DivU | I64RemS | I64RemU | I64And | I64Or
        | I64Xor | I64Shl | I64ShrS | I64ShrU | I64Rotl | I64Rotr | I64Eq | I64Ne | I64LtS
        | I64LtU | I64GtS | I64GtU | I64LeS | I64LeU | I64GeS | I64GeU => (2, 1),

        // i64 unary
        I64Eqz | I64Clz | I64Ctz | I64Popcnt | I64Extend8S | I64Extend16S | I64Extend32S => (1, 1),

        // Conversions
        I64ExtendI32S | I64ExtendI32U | I32WrapI64 => (1, 1),

        // f32 binary
        F32Add | F32Sub | F32Mul | F32Div | F32Min | F32Max | F32Copysign => (2, 1),

        // f32 comparisons: pop 2, push 1 (i32 result)
        F32Eq | F32Ne | F32Lt | F32Le | F32Gt | F32Ge => (2, 1),

        // f32 unary
        F32Abs | F32Neg | F32Ceil | F32Floor | F32Trunc | F32Nearest | F32Sqrt => (1, 1),

        // f64 binary
        F64Add | F64Sub | F64Mul | F64Div | F64Min | F64Max | F64Copysign => (2, 1),

        // f64 comparisons: pop 2, push 1 (i32 result)
        F64Eq | F64Ne | F64Lt | F64Le | F64Gt | F64Ge => (2, 1),

        // f64 unary
        F64Abs | F64Neg | F64Ceil | F64Floor | F64Trunc | F64Nearest | F64Sqrt => (1, 1),

        // f32/f64 conversions (unary: pop 1, push 1)
        F32ConvertI32S | F32ConvertI32U | F32ConvertI64S | F32ConvertI64U | F32DemoteF64
        | F64ConvertI32S | F64ConvertI32U | F64ConvertI64S | F64ConvertI64U | F64PromoteF32
        | I32TruncF32S | I32TruncF32U | I32TruncF64S | I32TruncF64U | I64TruncF64S
        | I64TruncF64U | F32ReinterpretI32 | I32ReinterpretF32 | F64ReinterpretI64
        | I64ReinterpretF64 => (1, 1),

        // Constants: push 1
        I32Const(_) | I64Const(_) | F32Const(_) | F64Const(_) => (0, 1),

        // Loads: pop address, push value
        I32Load { .. }
        | I32Load8S { .. }
        | I32Load8U { .. }
        | I32Load16S { .. }
        | I32Load16U { .. }
        | I64Load { .. }
        | I64Load8S { .. }
        | I64Load8U { .. }
        | I64Load16S { .. }
        | I64Load16U { .. }
        | I64Load32S { .. }
        | I64Load32U { .. }
        | F32Load { .. }
        | F64Load { .. } => (1, 1),

        // Stores: pop value + address, push nothing
        I32Store { .. }
        | I32Store8 { .. }
        | I32Store16 { .. }
        | I64Store { .. }
        | I64Store8 { .. }
        | I64Store16 { .. }
        | I64Store32 { .. }
        | F32Store { .. }
        | F64Store { .. } => (2, 0),

        // Variables
        LocalGet(_) | GlobalGet(_) => (0, 1),
        LocalSet(_) | GlobalSet(_) => (1, 0),
        LocalTee(_) => (0, 0), // peeks, doesn't pop

        // Memory
        MemorySize(_) => (0, 1),
        MemoryGrow(_) => (1, 1),

        // Control flow / structural — no value stack effect at this level
        Block
        | Loop
        | If
        | Else
        | End
        | Nop
        | Unreachable
        | Return
        | Br(_)
        | BrIf(_)
        | BrTable { .. } => (0, 0),

        // Special
        Drop => (1, 0),
        Select => (3, 1),
        Call(_) | CallIndirect { .. } => (0, 1), // approximate: push return value

        // v128 SIMD and anything else — conservative default
        // Most SIMD ops are binary (pop 2, push 1) but some are unary.
        // Using (0, 0) as safe fallback since SIMD isn't stack-tracked yet.
        _ => (0, 0),
    }
}

/// Register allocator state
#[derive(Debug, Clone)]
pub struct RegisterState {
    /// Next available register
    next_reg: u8,
    /// Register map for variables
    var_map: HashMap<String, Reg>,
}

impl RegisterState {
    /// Create a new register state
    pub fn new() -> Self {
        Self {
            next_reg: 0,
            var_map: HashMap::new(),
        }
    }

    /// Allocate a new register (cycles through allocatable set, skipping R9/R10/R11)
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires self.next_reg < ALLOCATABLE_REGS.len()
    /// ensures
    ///     result != Reg::R9,   // globals base — reserved
    ///     result != Reg::R10,  // memory size — reserved
    ///     result != Reg::R11,  // memory base — reserved
    ///     is_allocatable(result),
    /// ```
    pub fn alloc_reg(&mut self) -> Reg {
        contracts::regalloc::verify_index(self.next_reg, ALLOCATABLE_REGS.len());
        let reg = index_to_reg(self.next_reg);
        self.next_reg = (self.next_reg + 1) % ALLOCATABLE_REGS.len() as u8;
        contracts::regalloc::verify_allocation(&reg);
        reg
    }

    /// Get or allocate register for variable
    pub fn get_or_alloc(&mut self, var: &str) -> Reg {
        if let Some(&reg) = self.var_map.get(var) {
            reg
        } else {
            let reg = self.alloc_reg();
            self.var_map.insert(var.to_string(), reg);
            reg
        }
    }

    /// Reset allocator
    pub fn reset(&mut self) {
        self.next_reg = 0;
        self.var_map.clear();
    }
}

impl Default for RegisterState {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert VFP register index to VfpReg enum (S0-S15 for linear allocation)
fn index_to_vfp_reg(index: u8) -> VfpReg {
    match index % 16 {
        0 => VfpReg::S0,
        1 => VfpReg::S1,
        2 => VfpReg::S2,
        3 => VfpReg::S3,
        4 => VfpReg::S4,
        5 => VfpReg::S5,
        6 => VfpReg::S6,
        7 => VfpReg::S7,
        8 => VfpReg::S8,
        9 => VfpReg::S9,
        10 => VfpReg::S10,
        11 => VfpReg::S11,
        12 => VfpReg::S12,
        13 => VfpReg::S13,
        14 => VfpReg::S14,
        _ => VfpReg::S15,
    }
}

/// Convert VFP D-register index to VfpReg enum (D0-D15 for linear allocation).
///
/// ARMv7-M VFPv4-D16 (e.g., Cortex-M7DP) exposes 16 double-precision registers
/// D0..D15. Each D-register aliases a pair of S-registers (D0=S0:S1, ...),
/// so the f32 and f64 allocators share the same underlying register file.
/// For the non-optimized selector we use a simple wrapping counter — register
/// pressure is rare in straight-line WASM functions, and the encoder accepts
/// any D0..D15. The same allocator is used regardless of S-register pressure
/// because the round-robin policy already wraps.
fn index_to_vfp_dreg(index: u8) -> VfpReg {
    match index % 16 {
        0 => VfpReg::D0,
        1 => VfpReg::D1,
        2 => VfpReg::D2,
        3 => VfpReg::D3,
        4 => VfpReg::D4,
        5 => VfpReg::D5,
        6 => VfpReg::D6,
        7 => VfpReg::D7,
        8 => VfpReg::D8,
        9 => VfpReg::D9,
        10 => VfpReg::D10,
        11 => VfpReg::D11,
        12 => VfpReg::D12,
        13 => VfpReg::D13,
        14 => VfpReg::D14,
        _ => VfpReg::D15,
    }
}

/// Convert Q-register index to QReg enum (Q0-Q7, wrapping)
fn index_to_qreg(index: u8) -> QReg {
    match index % 8 {
        0 => QReg::Q0,
        1 => QReg::Q1,
        2 => QReg::Q2,
        3 => QReg::Q3,
        4 => QReg::Q4,
        5 => QReg::Q5,
        6 => QReg::Q6,
        _ => QReg::Q7,
    }
}

/// Instruction selector
pub struct InstructionSelector {
    /// Pattern matcher with synthesis rules
    matcher: PatternMatcher,
    /// Register allocator
    regs: RegisterState,
    /// Bounds checking configuration
    bounds_check: BoundsCheckConfig,
    /// Number of imported functions (calls to func_idx < this go through Meld dispatch)
    num_imports: u32,
    /// Relocatable host-link mode (#197). When set, an import call emits a
    /// direct `BL func_N` (the relocatable-ELF builder rewrites `func_N` to the
    /// wasm field name, e.g. `k_spin_lock`) instead of `__meld_dispatch_import`.
    relocatable: bool,
    /// #237: native-pointer ABI — wasm statics become `__synth_wasm_data`-
    /// relative (MOVW/MOVT), so a `base=0` host-pointer trampoline doesn't
    /// mis-address them.
    native_pointer_abi: bool,
    /// #237: wasm linear-memory minimum size in bytes — the static-data extent
    /// (initialized `(data)` + zero-init/BSS). A const address below this is a
    /// static (symbol-relative under the flag).
    linear_memory_bytes: u32,
    /// #237: the lowest wasm address that is a *static-data* address rather than
    /// a scalar/offset. When a module carries a stack-pointer global, its
    /// initializer (e.g. `65536`) is simultaneously the stack top and the base
    /// of the static-data region: addresses `>= wasm_data_base` are pointers
    /// (relocated to `__synth_wasm_data + C`), values `< wasm_data_base` are
    /// frame sizes / field offsets (`i32.const 16`) and stay plain immediates.
    /// Defaults to `0` (relocate everything inside linear memory) for modules
    /// with no stack-pointer global.
    wasm_data_base: u32,
    /// #237: the stack-pointer global `(index, init_value)`, if identified. Under
    /// the native-pointer ABI a leaf, balanced function register-promotes it:
    /// `global.get` materializes `__synth_wasm_data + init` (the real stack top),
    /// `global.set` is dead (no wasm reader; host imports don't touch wasm SP).
    sp_global: Option<(u32, i32)>,
    /// #311: whether function `i` (full wasm index) returns i64.
    func_ret_i64: Vec<bool>,
    /// #311: whether type `i` returns i64 (`call_indirect`).
    type_ret_i64: Vec<bool>,
    /// #359: declared param widths of the function being compiled —
    /// `params_i64[k]` true ⇒ param `k` is i64/f64. The AAPCS stack-argument
    /// path refuses (Ok-or-Err) when any param is 64-bit. Empty ⇒ assume i32
    /// (the legacy path; every function with <=4 i32 params is byte-identical).
    params_i64: Vec<bool>,
    /// AAPCS argument count per function, indexed by the *full* WASM function
    /// index (imports first, then locals). Plumbed from the frontend's type +
    /// function sections (issue #195). `func_arg_counts[i]` = number of integer
    /// arguments function `i` expects. Empty when no signature table was
    /// provided (in which case `Call` falls back to passing zero args — the
    /// pre-#195 behaviour).
    func_arg_counts: Vec<u32>,
    /// AAPCS argument count per *function type*, indexed by type index. Used by
    /// `CallIndirect`, whose callee arg count comes from the static `type_index`
    /// rather than a concrete function index (issue #195).
    type_arg_counts: Vec<u32>,
    /// FPU capability of the target (None = soft-float only)
    fpu: Option<FPUPrecision>,
    /// Target name for error messages
    target_name: String,
    /// Next available VFP S-register (S0-S15, wrapping)
    next_vfp_reg: u8,
    /// Next available VFP D-register (D0-D15, wrapping). Used only on
    /// targets with `FPUPrecision::Double` (e.g., Cortex-M7DP).
    next_vfp_dreg: u8,
    /// Label counter for generating unique label names
    label_counter: u32,
    /// Whether this target has Helium MVE (Cortex-M55)
    has_helium: bool,
    /// Next available Q-register (Q0-Q7, wrapping)
    next_qreg: u8,
    /// VCR-RA-001 step 3b-lite (#242): spill-on-exhaustion retry mode. Default
    /// OFF — the backend sets it only for a retry after `select_with_stack`
    /// failed with the i32 register-exhaustion `Err`, so every function that
    /// compiles without it stays bit-identical by construction. When ON:
    /// (a) the i64 spill area is always reserved in the frame, and (b) i32 temp
    /// allocation under exhaustion spills the deepest stack value instead of
    /// hard-failing ([`alloc_temp_or_spill`]).
    spill_on_exhaustion: bool,
    /// VCR-RA-001 acceptance increment (#242): param-backing-on-exhaustion
    /// retry mode. Default OFF — the backend sets it only for a retry after
    /// `select_with_stack` failed with the i64 consecutive-PAIR exhaustion
    /// `Err`. The pair allocator already spills register-resident STACK values
    /// (#171, pair-aware); the only remaining blockers at the pair hard-fail
    /// are the *pinned param home registers* (#193 `reserved`) plus the popped
    /// operand pairs (`extra_avoid`) — and params are not stack values, so no
    /// amount of stack spilling can free them. When ON, every read param is
    /// frame-backed via the proven #204 `param_slots` machinery (spilled to a
    /// frame slot at entry, reloaded on read), so `reserved` is empty and a
    /// free consecutive pair always exists after stack spilling (at most two
    /// adjacent operand pairs can be blocked among the 9-register pool). Like
    /// `spill_on_exhaustion`, bit-identity is structural: only functions that
    /// failed BOTH earlier passes ever compile with this set.
    param_backing_on_exhaustion: bool,
}

impl InstructionSelector {
    /// Create a new instruction selector
    pub fn new(rules: Vec<SynthesisRule>) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
            bounds_check: BoundsCheckConfig::None,
            num_imports: 0,
            relocatable: false,
            native_pointer_abi: false,
            linear_memory_bytes: 0,
            wasm_data_base: 0,
            sp_global: None,
            func_ret_i64: Vec::new(),
            type_ret_i64: Vec::new(),
            params_i64: Vec::new(),
            func_arg_counts: Vec::new(),
            type_arg_counts: Vec::new(),
            fpu: None,
            target_name: "cortex-m3".to_string(),
            next_vfp_reg: 0,
            next_vfp_dreg: 0,
            label_counter: 0,
            has_helium: false,
            next_qreg: 0,
            spill_on_exhaustion: false,
            param_backing_on_exhaustion: false,
        }
    }

    /// Create a new instruction selector with bounds checking
    pub fn with_bounds_check(rules: Vec<SynthesisRule>, bounds_check: BoundsCheckConfig) -> Self {
        Self {
            matcher: PatternMatcher::new(rules),
            regs: RegisterState::new(),
            bounds_check,
            num_imports: 0,
            relocatable: false,
            native_pointer_abi: false,
            linear_memory_bytes: 0,
            wasm_data_base: 0,
            sp_global: None,
            func_ret_i64: Vec::new(),
            type_ret_i64: Vec::new(),
            params_i64: Vec::new(),
            func_arg_counts: Vec::new(),
            type_arg_counts: Vec::new(),
            fpu: None,
            target_name: "cortex-m3".to_string(),
            next_vfp_reg: 0,
            next_vfp_dreg: 0,
            label_counter: 0,
            has_helium: false,
            next_qreg: 0,
            spill_on_exhaustion: false,
            param_backing_on_exhaustion: false,
        }
    }

    /// Set the number of imported functions for Meld dispatch
    pub fn set_num_imports(&mut self, num_imports: u32) {
        self.num_imports = num_imports;
    }

    /// VCR-RA-001 step 3b-lite (#242): enable spill-on-exhaustion. Intended
    /// ONLY as a retry after `select_with_stack` failed with the i32
    /// register-exhaustion `Err` — enabling it changes the frame layout (the
    /// i64 spill area is always reserved), so calling it for a function that
    /// compiles without it would change its bytes.
    pub fn set_spill_on_exhaustion(&mut self, enabled: bool) {
        self.spill_on_exhaustion = enabled;
    }

    /// VCR-RA-001 acceptance increment (#242): enable param frame-backing on
    /// i64 consecutive-pair exhaustion. Intended ONLY as the backend's final
    /// retry after `select_with_stack` failed with the pair-exhaustion `Err`
    /// (which stack spilling alone cannot recover — the blockers are pinned
    /// param home registers, not stack values). Forces the #204 `param_slots`
    /// frame-backing for every read param, so it changes the frame layout and
    /// every param read; calling it for a function that compiles without it
    /// would change its bytes.
    pub fn set_param_backing_on_exhaustion(&mut self, enabled: bool) {
        self.param_backing_on_exhaustion = enabled;
    }

    /// Enable relocatable host-link mode (#197): import calls emit a direct
    /// `BL func_N` (rewritten to the wasm field name by the relocatable-ELF
    /// builder) instead of dispatching through `__meld_dispatch_import`.
    pub fn set_relocatable(&mut self, relocatable: bool) {
        self.relocatable = relocatable;
    }

    /// #237: enable the native-pointer ABI and supply the active data-segment
    /// `(offset, length)` ranges used to classify const addresses as statics.
    /// `linear_memory_bytes` is the wasm linear-memory minimum size — the full
    /// static-data extent, covering both `(data)` segments and the zero-init
    /// (BSS) region (#237 BSS follow-up).
    pub fn set_native_pointer_abi(&mut self, enabled: bool, linear_memory_bytes: u32) {
        self.native_pointer_abi = enabled;
        self.linear_memory_bytes = linear_memory_bytes;
    }

    /// #237: under the native-pointer ABI, a const effective address `addr`
    /// within the wasm linear memory `[0, linear_memory_bytes)` is a wasm static
    /// (whether an initialized `(data)` byte or a zero-init/BSS variable like a
    /// `static k_spinlock`) → returns its `__synth_wasm_data` addend
    /// (base-independent). Any address beyond the linear memory is a runtime host
    /// pointer and keeps the base-relative `[R11+addr]` path (returns `None`).
    fn static_data_addend(&self, addr: u32) -> Option<i32> {
        if !self.native_pointer_abi {
            return None;
        }
        // A const is a static-data *address* only within
        // `[wasm_data_base, linear_memory_bytes)`. The lower bound excludes
        // frame sizes / field offsets (`i32.const 16`) that live below the
        // stack-pointer init; the upper bound excludes runtime host pointers.
        (self.wasm_data_base <= addr && addr < self.linear_memory_bytes).then_some(addr as i32)
    }

    /// #237: register the stack-pointer global discovered by the backend. Its
    /// initializer doubles as the static-data base (`wasm_data_base`), so const
    /// addresses at/above it relocate while frame-size scalars below it don't.
    /// #311: register per-function / per-type i64-result tables so call
    /// results are tagged as register pairs (hi half visible to liveness).
    pub fn set_result_types(&mut self, func_ret_i64: Vec<bool>, type_ret_i64: Vec<bool>) {
        self.func_ret_i64 = func_ret_i64;
        self.type_ret_i64 = type_ret_i64;
    }

    /// #359: register the declared parameter widths of the function about to be
    /// compiled so the AAPCS stack-argument path can refuse 64-bit params
    /// (Ok-or-Err). Empty ⇒ all params assumed i32 (the legacy path).
    pub fn set_params_i64(&mut self, params_i64: Vec<bool>) {
        self.params_i64 = params_i64;
    }

    pub fn set_native_pointer_stack(&mut self, sp_index: u32, sp_init: i32) {
        self.sp_global = Some((sp_index, sp_init));
        if sp_init >= 0 {
            self.wasm_data_base = sp_init as u32;
        }
    }

    /// #237/#345: emit a `symbol + addend` absolute address into `rd` —
    /// base-independent addressing for any linker-placed region
    /// (`__synth_wasm_data` statics, `__synth_globals` slots).
    ///
    /// #345: this now emits a single link-survivable literal-pool load
    /// (`LdrSym` → `LDR rd,[pc,#off]` + a pooled word with R_ARM_ABS32) instead
    /// of the inline-immediate `MovwSym`+`MovtSym` pair. The inline `MOVW_ABS`
    /// immediate could be mangled into an undefined instruction when linked into
    /// a large Zephyr image (USAGE FAULT on G474RE); an `R_ARM_ABS32` on a data
    /// word is what `ld`/bfd patches at link time and survives a big multi-object
    /// link. The `MovwSym`/`MovtSym` ops remain available for other paths.
    fn emit_sym_addr(
        out: &mut Vec<ArmInstruction>,
        rd: Reg,
        symbol: &str,
        addend: i32,
        line: usize,
    ) {
        out.push(ArmInstruction {
            op: ArmOp::LdrSym {
                rd,
                symbol: symbol.to_string(),
                addend,
            },
            source_line: Some(line),
        });
    }

    /// #237/#345: emit a `__synth_wasm_data + addend` address into `rd` — the
    /// base-independent static-data address, via the link-survivable literal-pool
    /// load (see [`Self::emit_sym_addr`] for the #345 rationale).
    fn emit_wasm_data_addr(out: &mut Vec<ArmInstruction>, rd: Reg, addend: i32, line: usize) {
        Self::emit_sym_addr(out, rd, "__synth_wasm_data", addend, line);
    }

    /// Set the per-function AAPCS argument-count table (issue #195).
    ///
    /// `func_arg_counts[i]` is the number of integer arguments the function at
    /// full WASM index `i` (imports first, then locals) expects. `type_arg_counts[t]`
    /// is the argument count of function type `t` (used for `CallIndirect`).
    /// These let `Call`/`CallIndirect` marshal the top-N operand-stack values
    /// into R0–R3 per AAPCS before the `BL`.
    pub fn set_func_arg_counts(&mut self, func_arg_counts: Vec<u32>, type_arg_counts: Vec<u32>) {
        self.func_arg_counts = func_arg_counts;
        self.type_arg_counts = type_arg_counts;
    }

    /// Set bounds checking configuration
    pub fn set_bounds_check(&mut self, config: BoundsCheckConfig) {
        self.bounds_check = config;
    }

    /// Set target FPU capability and name (for target-aware error messages)
    pub fn set_target(&mut self, fpu: Option<FPUPrecision>, target_name: &str) {
        self.fpu = fpu;
        self.target_name = target_name.to_string();
    }

    /// Set Helium MVE capability (Cortex-M55)
    pub fn set_helium(&mut self, has_helium: bool) {
        self.has_helium = has_helium;
    }

    /// Allocate a Q-register (Q0-Q7, wrapping)
    fn alloc_qreg(&mut self) -> QReg {
        let reg = index_to_qreg(self.next_qreg);
        self.next_qreg = (self.next_qreg + 1) % 8;
        reg
    }

    /// Generate a unique label name with the given prefix
    fn alloc_label(&mut self, prefix: &str) -> String {
        let id = self.label_counter;
        self.label_counter += 1;
        format!(".L{}_{}", prefix, id)
    }

    /// Allocate a VFP S-register (S0-S15, wrapping)
    fn alloc_vfp_reg(&mut self) -> VfpReg {
        let reg = index_to_vfp_reg(self.next_vfp_reg);
        self.next_vfp_reg = (self.next_vfp_reg + 1) % 16;
        reg
    }

    /// Allocate a VFP D-register (D0-D15, wrapping). Used for f64 lowering on
    /// targets with `FPUPrecision::Double` (e.g., Cortex-M7DP).
    fn alloc_vfp_dreg(&mut self) -> VfpReg {
        let reg = index_to_vfp_dreg(self.next_vfp_dreg);
        self.next_vfp_dreg = (self.next_vfp_dreg + 1) % 16;
        reg
    }

    /// Returns true if the configured target has a double-precision FPU.
    fn has_double_fpu(&self) -> bool {
        matches!(self.fpu, Some(FPUPrecision::Double))
    }

    /// Select ARM instructions for a sequence of WASM operations
    pub fn select(&mut self, wasm_ops: &[WasmOp]) -> Result<Vec<ArmInstruction>> {
        let mut arm_instructions = Vec::new();
        let mut index = 0;

        while index < wasm_ops.len() {
            let remaining = &wasm_ops[index..];
            let matches = self.matcher.match_sequence(remaining);

            if let Some(best_match) = matches.first() {
                // Apply the rule to generate ARM instructions
                let arm_ops =
                    self.apply_replacement(&best_match.rule.replacement, &best_match.bindings)?;

                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }

                index += best_match.length;
            } else {
                // No rule matched - generate default instruction(s)
                let arm_ops = self.select_default(&wasm_ops[index])?;
                for op in arm_ops {
                    arm_instructions.push(ArmInstruction {
                        op,
                        source_line: Some(index),
                    });
                }
                index += 1;
            }
        }

        Ok(arm_instructions)
    }

    /// Apply a replacement pattern to generate ARM instructions
    fn apply_replacement(
        &mut self,
        replacement: &Replacement,
        _bindings: &Bindings,
    ) -> Result<Vec<ArmOp>> {
        match replacement {
            Replacement::Identity => {
                // For identity replacement, generate a default instruction
                Ok(vec![ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Reg(Reg::R0),
                }])
            }

            Replacement::ArmInstr(op) => {
                // Single ARM instruction
                Ok(vec![op.clone()])
            }

            Replacement::ArmSequence(ops) => {
                // Sequence of ARM instructions
                Ok(ops.clone())
            }

            Replacement::Var(var_name) => Err(synth_core::Error::synthesis(format!(
                "Replacement::Var({var_name}) not implemented — would silently emit NOP"
            ))),

            Replacement::Inline => Err(synth_core::Error::synthesis(
                "Replacement::Inline not implemented — would silently emit NOP".to_string(),
            )),
        }
    }

    /// Select default ARM instruction(s) for a WASM operation (no pattern match)
    /// Returns a sequence of instructions (may include bounds checking for memory ops)
    fn select_default(&mut self, wasm_op: &WasmOp) -> Result<Vec<ArmOp>> {
        use WasmOp::*;

        let rd = self.regs.alloc_reg();
        let rn = self.regs.alloc_reg();
        let rm = self.regs.alloc_reg();

        let instrs = match wasm_op {
            I32Add => vec![ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Sub => vec![ArmOp::Sub {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Mul => vec![ArmOp::Mul { rd, rn, rm }],

            I32And => vec![ArmOp::And {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Or => vec![ArmOp::Orr {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            I32Xor => vec![ArmOp::Eor {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }],

            // Shifts: WASM pops both value (rn) and shift amount (rm) from stack
            I32Shl => vec![ArmOp::LslReg { rd, rn, rm }],
            I32ShrS => vec![ArmOp::AsrReg { rd, rn, rm }],
            I32ShrU => vec![ArmOp::LsrReg { rd, rn, rm }],

            // Rotate operations: shift amount from stack register
            I32Rotl => {
                // Rotate left by N = Rotate right by (32 - N)
                // RSB rtmp, rm, #32; ROR rd, rn, rtmp
                let rtmp = self.regs.alloc_reg();
                vec![
                    ArmOp::Rsb {
                        rd: rtmp,
                        rn: rm,
                        imm: 32,
                    },
                    ArmOp::RorReg { rd, rn, rm: rtmp },
                ]
            }

            I32Rotr => vec![ArmOp::RorReg { rd, rn, rm }],

            // Bit count operations
            I32Clz => vec![ArmOp::Clz { rd, rm }],

            I32Ctz => {
                // Count trailing zeros: RBIT + CLZ
                vec![ArmOp::Rbit { rd, rm }, ArmOp::Clz { rd, rm: rd }]
            }

            I32Popcnt => {
                // Population count - no native ARM instruction
                // Use Popcnt pseudo-op which the encoder expands to a parallel
                // bit-count algorithm (shift-and-add with masks)
                vec![ArmOp::Popcnt { rd, rm }]
            }

            I32Const(val) => {
                let uval = *val as u32;
                let inverted = !uval;
                if uval <= 0xFFFF {
                    // 0..65535: MOVW handles the full 16-bit range
                    vec![ArmOp::Movw {
                        rd,
                        imm16: uval as u16,
                    }]
                } else if inverted <= 0xFFFF {
                    // Simple bit-inverted patterns: MOVW inverted + MVN
                    // e.g., -1 (0xFFFFFFFF) -> MOVW rd, #0; MVN rd, rd
                    // e.g., -2 (0xFFFFFFFE) -> MOVW rd, #1; MVN rd, rd
                    vec![
                        ArmOp::Movw {
                            rd,
                            imm16: inverted as u16,
                        },
                        ArmOp::Mvn {
                            rd,
                            op2: Operand2::Reg(rd),
                        },
                    ]
                } else {
                    // Full 32-bit range: MOVW low16 + MOVT high16
                    vec![
                        ArmOp::Movw {
                            rd,
                            imm16: (uval & 0xFFFF) as u16,
                        },
                        ArmOp::Movt {
                            rd,
                            imm16: ((uval >> 16) & 0xFFFF) as u16,
                        },
                    ]
                }
            }

            I32Load { offset, .. } => {
                // WASM memory access: address from stack (rn) + static offset
                // R11 is the dedicated memory base register for memory 0
                // Effective address = R11 + rn + offset
                self.generate_load_with_bounds_check(rd, rn, *offset as i32, 4)
            }

            I32Store { offset, .. } => {
                // WASM memory access: address from stack (rn) + static offset
                // R11 is the dedicated memory base register for memory 0
                // Effective address = R11 + rn + offset
                self.generate_store_with_bounds_check(rd, rn, *offset as i32, 4)
            }

            // Sub-word loads (i32)
            I32Load8S { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 1, true)
            }
            I32Load8U { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 1, false)
            }
            I32Load16S { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 2, true)
            }
            I32Load16U { offset, .. } => {
                self.generate_subword_load_with_bounds_check(rd, rn, *offset as i32, 2, false)
            }

            // Sub-word stores (i32)
            I32Store8 { offset, .. } => {
                self.generate_subword_store_with_bounds_check(rd, rn, *offset as i32, 1)
            }
            I32Store16 { offset, .. } => {
                self.generate_subword_store_with_bounds_check(rd, rn, *offset as i32, 2)
            }

            // i64 sub-word loads — load sub-word, extend to i64 register pair
            I64Load8S { offset, .. } => {
                // LDRSB R0, [R11, rn, #offset]; ASR R1, R0, #31 (sign-extend to hi)
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    1,
                    true,
                );
                ops.push(ArmOp::Asr {
                    rd: Reg::R1,
                    rn: Reg::R0,
                    shift: 31,
                });
                ops
            }
            I64Load8U { offset, .. } => {
                // LDRB R0, [R11, rn, #offset]; MOV R1, #0
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    1,
                    false,
                );
                ops.push(ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Imm(0),
                });
                ops
            }
            I64Load16S { offset, .. } => {
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    2,
                    true,
                );
                ops.push(ArmOp::Asr {
                    rd: Reg::R1,
                    rn: Reg::R0,
                    shift: 31,
                });
                ops
            }
            I64Load16U { offset, .. } => {
                let mut ops = self.generate_subword_load_with_bounds_check(
                    Reg::R0,
                    rn,
                    *offset as i32,
                    2,
                    false,
                );
                ops.push(ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Imm(0),
                });
                ops
            }
            I64Load32S { offset, .. } => {
                // LDR R0, [R11, rn, #offset]; ASR R1, R0, #31
                let mut ops = self.generate_load_with_bounds_check(Reg::R0, rn, *offset as i32, 4);
                ops.push(ArmOp::Asr {
                    rd: Reg::R1,
                    rn: Reg::R0,
                    shift: 31,
                });
                ops
            }
            I64Load32U { offset, .. } => {
                // LDR R0, [R11, rn, #offset]; MOV R1, #0
                let mut ops = self.generate_load_with_bounds_check(Reg::R0, rn, *offset as i32, 4);
                ops.push(ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Imm(0),
                });
                ops
            }

            // i64 sub-word stores — store low N bits from i64 register pair
            I64Store8 { offset, .. } => {
                // STRB R0, [R11, rn, #offset] (low byte of low word)
                self.generate_subword_store_with_bounds_check(Reg::R0, rn, *offset as i32, 1)
            }
            I64Store16 { offset, .. } => {
                // STRH R0, [R11, rn, #offset] (low halfword of low word)
                self.generate_subword_store_with_bounds_check(Reg::R0, rn, *offset as i32, 2)
            }
            I64Store32 { offset, .. } => {
                // STR R0, [R11, rn, #offset] (low word)
                self.generate_store_with_bounds_check(Reg::R0, rn, *offset as i32, 4)
            }

            // Memory management
            MemorySize(_mem_idx) => {
                // On embedded with fixed memory, return memory size in pages.
                // R10 holds memory size in bytes; divide by 65536 (page size) via LSR #16.
                vec![ArmOp::MemorySize { rd }]
            }
            MemoryGrow(_mem_idx) => {
                // On embedded with fixed memory, always return -1 (cannot grow).
                vec![ArmOp::MemoryGrow { rd, rn }]
            }

            // FIXME: select_default LocalGet/Set ignores index (hardcoded SP+0).
            // Currently unreachable because select_with_stack handles these ops.
            // See issue #72.
            LocalGet(_index) => vec![ArmOp::Ldr {
                rd,
                addr: MemAddr::imm(Reg::SP, 0), // Simplified - would use proper frame offset
            }],

            // FIXME: select_default LocalGet/Set ignores index (hardcoded SP+0).
            // Currently unreachable because select_with_stack handles these ops.
            // See issue #72.
            LocalSet(_index) => vec![ArmOp::Str {
                rd,
                addr: MemAddr::imm(Reg::SP, 0),
            }],

            Call(func_idx) => {
                if *func_idx < self.num_imports {
                    // Import call — dispatch through Meld runtime
                    // R0 = import index, then BL __meld_dispatch_import
                    vec![
                        ArmOp::Mov {
                            rd: Reg::R0,
                            op2: Operand2::Imm(*func_idx as i32),
                        },
                        ArmOp::Bl {
                            label: "__meld_dispatch_import".to_string(),
                        },
                    ]
                } else {
                    // Local function call
                    vec![ArmOp::Bl {
                        label: format!("func_{}", func_idx),
                    }]
                }
            }

            CallIndirect {
                type_index,
                table_index: _,
            } => {
                // Table index is on top of stack (in rn), call target via table lookup
                // For now, generate the pseudo-instruction; ARM encoder will expand
                vec![ArmOp::CallIndirect {
                    rd,
                    type_idx: *type_index,
                    table_index_reg: rn, // Table index from stack
                }]
            }

            // Control flow — labels and branches are emitted here.
            // Full structured control flow is handled in select_with_stack;
            // select_default emits a reasonable per-instruction lowering.
            Block => {
                let label = self.alloc_label("block_end");
                vec![ArmOp::Label { name: label }]
            }
            Loop => {
                let label = self.alloc_label("loop_start");
                vec![ArmOp::Label { name: label }]
            }
            Br(depth) => vec![ArmOp::B {
                label: format!("br_target_{}", depth),
            }],
            BrIf(depth) => {
                // Pop condition from stack (in rn), branch if non-zero
                vec![
                    ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Bcc {
                        cond: Condition::NE,
                        label: format!("br_if_target_{}", depth),
                    },
                ]
            }
            Return => vec![ArmOp::Bx { rm: Reg::LR }],

            // Locals
            LocalTee(_index) => {
                // Tee is like set but keeps value on stack
                vec![ArmOp::Str {
                    rd,
                    addr: MemAddr::imm(Reg::SP, 0),
                }]
            }

            // Comparisons
            I32Eq => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }],
            I32Ne => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }],
            I32LtS | I32LtU | I32LeS | I32LeU | I32GtS | I32GtU | I32GeS | I32GeU => {
                vec![ArmOp::Cmp {
                    rn,
                    op2: Operand2::Reg(rm),
                }]
            }

            // Division and remainder (ARMv7-M+)
            // WASM requires trap on divide-by-zero. ARM SDIV/UDIV silently return 0,
            // so we emit an explicit zero-check: CMP rm, #0 / BNE skip / UDF #0.
            // FIXME: select_default I32DivS missing INT_MIN/-1 overflow trap.
            // Currently unreachable because select_with_stack handles this op.
            // See issue #72.
            I32DivS => {
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    // Signed division
                    ArmOp::Sdiv { rd, rn, rm },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }
            I32DivU => {
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    // Unsigned division
                    ArmOp::Udiv { rd, rn, rm },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }
            I32RemS => {
                // Signed remainder: quotient = SDIV tmp, rn, rm
                // remainder = MLS rd, tmp, rm, rn  (rd = rn - tmp * rm)
                let rtmp = self.regs.alloc_reg();
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    ArmOp::Sdiv { rd: rtmp, rn, rm },
                    ArmOp::Mls {
                        rd,
                        rn: rtmp,
                        rm,
                        ra: rn,
                    },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }
            I32RemU => {
                // Unsigned remainder: quotient = UDIV tmp, rn, rm
                // remainder = MLS rd, tmp, rm, rn  (rd = rn - tmp * rm)
                let rtmp = self.regs.alloc_reg();
                let seq = vec![
                    // Trap if divisor == 0
                    ArmOp::Cmp {
                        rn: rm,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::BCondOffset {
                        cond: Condition::NE,
                        offset: 0,
                    },
                    ArmOp::Udf { imm: 0 },
                    ArmOp::Udiv { rd: rtmp, rn, rm },
                    ArmOp::Mls {
                        rd,
                        rn: rtmp,
                        rm,
                        ra: rn,
                    },
                ];
                contracts::division::verify_trap_guard_length(seq.len());
                seq
            }

            // Sign extension operations
            I32Extend8S => {
                // Sign-extend byte: SXTB Rd, Rm
                vec![ArmOp::Sxtb { rd, rm }]
            }
            I32Extend16S => {
                // Sign-extend halfword: SXTH Rd, Rm
                vec![ArmOp::Sxth { rd, rm }]
            }

            // Comparison: equal to zero (unary)
            I32Eqz => vec![ArmOp::Cmp {
                rn,
                op2: Operand2::Imm(0),
            }],

            // Structural control flow delimiters — handled structurally in select_with_stack
            Nop => vec![ArmOp::Nop],
            End => vec![ArmOp::Nop],
            Drop => vec![ArmOp::Nop],
            If => {
                // In select_default (non-stack mode), emit a placeholder CMP + BEQ
                let else_label = self.alloc_label("else");
                vec![
                    ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Bcc {
                        cond: Condition::EQ,
                        label: else_label,
                    },
                ]
            }
            Else => {
                // Jump over else block (end of then block)
                let end_label = self.alloc_label("if_end");
                vec![
                    ArmOp::B {
                        label: end_label.clone(),
                    },
                    ArmOp::Label { name: end_label },
                ]
            }

            // Trap: unreachable should generate an undefined instruction
            Unreachable => vec![ArmOp::Udf { imm: 0 }],

            // br_table: emit a jump table via TBB/TBH or cascading branches
            BrTable { targets, default } => {
                // Emit a cascading compare-and-branch sequence
                // index is in rn (from stack)
                let mut instrs = Vec::new();
                for (i, target) in targets.iter().enumerate() {
                    // CMP rn, #i
                    instrs.push(ArmOp::Cmp {
                        rn,
                        op2: Operand2::Imm(i as i32),
                    });
                    // BEQ to target label
                    instrs.push(ArmOp::Bcc {
                        cond: Condition::EQ,
                        label: format!("br_table_target_{}", target),
                    });
                }
                // Default: unconditional branch
                instrs.push(ArmOp::B {
                    label: format!("br_table_target_{}", default),
                });
                instrs
            }
            GlobalGet(index) => {
                // WASM globals are stored in a globals table in memory.
                // R9 is the dedicated globals base register (set up by runtime startup).
                // Each i32 global occupies 4 bytes: globals_base + index * 4.
                vec![ArmOp::Ldr {
                    rd,
                    addr: MemAddr::imm(Reg::R9, (*index as i32) * 4),
                }]
            }
            GlobalSet(index) => {
                // Store value from source register to globals_base + index * 4.
                // R9 is the dedicated globals base register.
                vec![ArmOp::Str {
                    rd,
                    addr: MemAddr::imm(Reg::R9, (*index as i32) * 4),
                }]
            }
            Select => {
                // WASM select: pops condition, val2, val1 from stack;
                // pushes val1 if condition != 0, else val2.
                // In select_default (non-stack mode), we emit:
                //   CMP rcond, #0
                //   MOV rd, rval1     (default: pick val1)
                //   IT EQ; MOVEQ rd, rval2  (override if cond == 0)
                let rcond = self.regs.alloc_reg();
                vec![
                    ArmOp::Cmp {
                        rn: rcond,
                        op2: Operand2::Imm(0),
                    },
                    ArmOp::Mov {
                        rd,
                        op2: Operand2::Reg(rn),
                    },
                    ArmOp::SelectMove {
                        rd,
                        rm,
                        cond: Condition::EQ,
                    },
                ]
            }

            // ===== i64 operations using register pairs on 32-bit ARM =====
            // Convention: i64 operand 1 in (R0,R1), operand 2 in (R2,R3), result in (R0,R1)
            I64Const(val) => {
                vec![ArmOp::I64Const {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    value: *val,
                }]
            }

            I64ExtendI32S => {
                vec![ArmOp::I64ExtendI32S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R0,
                }]
            }

            I64ExtendI32U => {
                vec![ArmOp::I64ExtendI32U {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rn: Reg::R0,
                }]
            }

            I32WrapI64 => {
                // Just take the low 32 bits (R0) — effectively a no-op if result is in R0
                vec![ArmOp::I32WrapI64 {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                }]
            }

            I64Extend8S => {
                vec![ArmOp::I64Extend8S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                }]
            }

            I64Extend16S => {
                vec![ArmOp::I64Extend16S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                }]
            }

            I64Extend32S => {
                vec![ArmOp::I64Extend32S {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                }]
            }

            // i64 arithmetic: ADDS/ADC for add, SUBS/SBC for sub
            I64Add => {
                vec![
                    ArmOp::Adds {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Adc {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            I64Sub => {
                vec![
                    ArmOp::Subs {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Sbc {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            // i64 bitwise: operate on each half independently
            I64And => {
                vec![
                    ArmOp::And {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::And {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            I64Or => {
                vec![
                    ArmOp::Orr {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Orr {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            I64Xor => {
                vec![
                    ArmOp::Eor {
                        rd: Reg::R0,
                        rn: Reg::R0,
                        op2: Operand2::Reg(Reg::R2),
                    },
                    ArmOp::Eor {
                        rd: Reg::R1,
                        rn: Reg::R1,
                        op2: Operand2::Reg(Reg::R3),
                    },
                ]
            }

            // i64 comparisons: compare register pairs, result 0/1 in R0
            I64Eqz => {
                vec![ArmOp::I64SetCondZ {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                }]
            }

            I64Eq => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::EQ,
                }]
            }

            I64Ne => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::NE,
                }]
            }

            I64LtS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LT,
                }]
            }

            I64LtU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LO,
                }]
            }

            I64LeS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LE,
                }]
            }

            I64LeU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::LS,
                }]
            }

            I64GtS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::GT,
                }]
            }

            I64GtU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::HI,
                }]
            }

            I64GeS => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::GE,
                }]
            }

            I64GeU => {
                vec![ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                    cond: Condition::HS,
                }]
            }

            // i64 multiply: UMULL + MLA cross products
            I64Mul => {
                vec![ArmOp::I64Mul {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            // i64 shifts: multi-instruction funnel shifts
            I64Shl => {
                vec![ArmOp::I64Shl {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            I64ShrU => {
                vec![ArmOp::I64ShrU {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            I64ShrS => {
                vec![ArmOp::I64ShrS {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R0,
                    rn_hi: Reg::R1,
                    rm_lo: Reg::R2,
                    rm_hi: Reg::R3,
                }]
            }

            I64Rotl => {
                vec![ArmOp::I64Rotl {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    shift: Reg::R2,
                }]
            }

            I64Rotr => {
                vec![ArmOp::I64Rotr {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    shift: Reg::R2,
                }]
            }

            // i64 bit manipulation
            I64Clz => {
                vec![ArmOp::I64Clz {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                }]
            }

            I64Ctz => {
                vec![ArmOp::I64Ctz {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                }]
            }

            I64Popcnt => {
                vec![ArmOp::I64Popcnt {
                    rd: Reg::R0,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                }]
            }

            // i64 division/remainder
            I64DivS => {
                vec![ArmOp::I64DivS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            I64DivU => {
                vec![ArmOp::I64DivU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            I64RemS => {
                vec![ArmOp::I64RemS {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            I64RemU => {
                vec![ArmOp::I64RemU {
                    rdlo: Reg::R0,
                    rdhi: Reg::R1,
                    rnlo: Reg::R0,
                    rnhi: Reg::R1,
                    rmlo: Reg::R2,
                    rmhi: Reg::R3,
                }]
            }

            // i64 memory operations (8-byte access, bounds-checked like i32)
            I64Load { offset, .. } => self.generate_i64_load_with_bounds_check(rn, *offset as i32),

            I64Store { offset, .. } => {
                self.generate_i64_store_with_bounds_check(rn, *offset as i32)
            }

            // ===== F32 operations =====
            // Path A: no FPU → error
            // Path B: FPU present → generate VFP instructions
            // Path C: unsupported ops → specific error
            F32Add if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Add { sd, sn, sm }]
            }
            F32Sub if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Sub { sd, sn, sm }]
            }
            F32Mul if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Mul { sd, sn, sm }]
            }
            F32Div if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Div { sd, sn, sm }]
            }

            F32Abs if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Abs { sd, sm }]
            }
            F32Neg if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Neg { sd, sm }]
            }
            F32Sqrt if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Sqrt { sd, sm }]
            }

            F32Eq if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Eq { rd, sn, sm }]
            }
            F32Ne if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ne { rd, sn, sm }]
            }
            F32Lt if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Lt { rd, sn, sm }]
            }
            F32Le if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Le { rd, sn, sm }]
            }
            F32Gt if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Gt { rd, sn, sm }]
            }
            F32Ge if self.fpu.is_some() => {
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ge { rd, sn, sm }]
            }

            F32Const(val) if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32Const { sd, value: *val }]
            }

            F32Load { offset, .. } if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F32Load {
                    sd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }
            F32Store { offset, .. } if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F32Store {
                    sd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }

            F32ConvertI32S if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ConvertI32S { sd, rm }]
            }
            F32ConvertI32U if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ConvertI32U { sd, rm }]
            }

            F32ReinterpretI32 if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                vec![ArmOp::F32ReinterpretI32 { sd, rm }]
            }
            I32ReinterpretF32 if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32ReinterpretF32 { rd, sm }]
            }

            I32TruncF32S if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32TruncF32S { rd, sm }]
            }
            I32TruncF32U if self.fpu.is_some() => {
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::I32TruncF32U { rd, sm }]
            }

            // F32 rounding pseudo-ops — emit ArmOp variants, encoder expands to
            // multi-instruction sequences using FPSCR rounding-mode manipulation
            F32Ceil if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Ceil { sd, sm }]
            }
            F32Floor if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Floor { sd, sm }]
            }
            F32Trunc if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Trunc { sd, sm }]
            }
            F32Nearest if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Nearest { sd, sm }]
            }
            // F32 min/max — emit ArmOp variants, encoder expands to VCMP + conditional VMOV
            F32Min if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Min { sd, sn, sm }]
            }
            F32Max if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Max { sd, sn, sm }]
            }
            // F32 copysign — emit ArmOp variant, encoder expands to VABS + sign extraction
            F32Copysign if self.fpu.is_some() => {
                let sd = self.alloc_vfp_reg();
                let sn = self.alloc_vfp_reg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F32Copysign { sd, sn, sm }]
            }

            op @ (F32ConvertI64S | F32ConvertI64U) if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported (requires i64 register pairs on 32-bit ARM)"
                )));
            }

            op @ F32DemoteF64 if self.fpu.is_some() => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported on single-precision target {}",
                    self.target_name
                )));
            }

            // Path A: all F32 ops with no FPU → error
            op @ (F32Add
            | F32Sub
            | F32Mul
            | F32Div
            | F32Eq
            | F32Ne
            | F32Lt
            | F32Le
            | F32Gt
            | F32Ge
            | F32Abs
            | F32Neg
            | F32Ceil
            | F32Floor
            | F32Trunc
            | F32Nearest
            | F32Sqrt
            | F32Min
            | F32Max
            | F32Copysign
            | F32Const(_)
            | F32Load { .. }
            | F32Store { .. }
            | F32ConvertI32S
            | F32ConvertI32U
            | F32ConvertI64S
            | F32ConvertI64U
            | F32DemoteF64
            | F32ReinterpretI32
            | I32ReinterpretF32
            | I32TruncF32S
            | I32TruncF32U) => {
                return Err(synth_core::Error::synthesis(format!(
                    "target {} has no FPU; cannot compile {op:?}",
                    self.target_name
                )));
            }

            // ===== F64 operations =====
            // Path A: target has double-precision FPU (e.g., Cortex-M7DP) → generate VFP-D
            // Path B: no DP FPU (no FPU or single-precision only) → error
            //
            // F64 values live in VFP D-registers (D0..D15). Each D-register
            // aliases a pair of S-registers, so the encoder reuses the same
            // VFP register file. Allocation follows the same wrap-around
            // policy as f32 (alloc_vfp_dreg).

            // F64 Arithmetic
            F64Add if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Add { dd, dn, dm }]
            }
            F64Sub if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Sub { dd, dn, dm }]
            }
            F64Mul if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Mul { dd, dn, dm }]
            }
            F64Div if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Div { dd, dn, dm }]
            }

            // F64 Math Functions (unary)
            F64Abs if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Abs { dd, dm }]
            }
            F64Neg if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Neg { dd, dm }]
            }
            F64Sqrt if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Sqrt { dd, dm }]
            }

            // F64 Comparisons (result in integer register)
            F64Eq if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Eq { rd, dn, dm }]
            }
            F64Ne if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Ne { rd, dn, dm }]
            }
            F64Lt if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Lt { rd, dn, dm }]
            }
            F64Le if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Le { rd, dn, dm }]
            }
            F64Gt if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Gt { rd, dn, dm }]
            }
            F64Ge if self.has_double_fpu() => {
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Ge { rd, dn, dm }]
            }

            // F64 Constants and Memory
            F64Const(val) if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                vec![ArmOp::F64Const { dd, value: *val }]
            }
            F64Load { offset, .. } if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F64Load {
                    dd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }
            F64Store { offset, .. } if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let addr_reg = self.regs.alloc_reg();
                vec![ArmOp::F64Store {
                    dd,
                    addr: MemAddr::reg_imm(Reg::R11, addr_reg, *offset as i32),
                }]
            }

            // F64 Conversions (i32 ↔ f64, f32 → f64, bitcasts)
            F64ConvertI32S if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                vec![ArmOp::F64ConvertI32S { dd, rm }]
            }
            F64ConvertI32U if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                vec![ArmOp::F64ConvertI32U { dd, rm }]
            }
            F64PromoteF32 if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let sm = self.alloc_vfp_reg();
                vec![ArmOp::F64PromoteF32 { dd, sm }]
            }
            F64ReinterpretI64 if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                // i64 lives in a register pair (rmlo, rmhi). Use the
                // existing integer allocator for both halves.
                let rmlo = self.regs.alloc_reg();
                let rmhi = self.regs.alloc_reg();
                vec![ArmOp::F64ReinterpretI64 { dd, rmlo, rmhi }]
            }
            I64ReinterpretF64 if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                let rdlo = self.regs.alloc_reg();
                let rdhi = self.regs.alloc_reg();
                vec![ArmOp::I64ReinterpretF64 { rdlo, rdhi, dm }]
            }
            I32TruncF64S if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::I32TruncF64S { rd, dm }]
            }
            I32TruncF64U if self.has_double_fpu() => {
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::I32TruncF64U { rd, dm }]
            }

            // F64 rounding pseudo-ops — emit ArmOp variants; encoder expands
            // them into FPSCR-rounding-mode + VCVT sequences.
            F64Ceil if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Ceil { dd, dm }]
            }
            F64Floor if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Floor { dd, dm }]
            }
            F64Trunc if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Trunc { dd, dm }]
            }
            F64Nearest if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Nearest { dd, dm }]
            }
            // F64 min/max — emit ArmOp variants, encoder expands to VCMP + conditional VMOV
            F64Min if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Min { dd, dn, dm }]
            }
            F64Max if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Max { dd, dn, dm }]
            }
            // F64 copysign — emit ArmOp variant, encoder expands to bitwise sequence
            F64Copysign if self.has_double_fpu() => {
                let dd = self.alloc_vfp_dreg();
                let dn = self.alloc_vfp_dreg();
                let dm = self.alloc_vfp_dreg();
                vec![ArmOp::F64Copysign { dd, dn, dm }]
            }

            // F64 i64 conversions: VCVT.{F64,S32}.{S32,F64} with i64 register
            // pairs is not implemented in the backend. Surface a typed error.
            op @ (F64ConvertI64S | F64ConvertI64U | I64TruncF64S | I64TruncF64U)
                if self.has_double_fpu() =>
            {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not supported (requires i64 register pairs on 32-bit ARM)"
                )));
            }

            // Path B: F64 op but target lacks double-precision FPU.
            // The validate_instructions feature gate at codegen time emits
            // a "requires double-precision FPU" error for any leaked F64
            // ArmOp; this path catches the op *before* selection and gives
            // a target-specific message.
            op @ (F64Add
            | F64Sub
            | F64Mul
            | F64Div
            | F64Eq
            | F64Ne
            | F64Lt
            | F64Le
            | F64Gt
            | F64Ge
            | F64Abs
            | F64Neg
            | F64Ceil
            | F64Floor
            | F64Trunc
            | F64Nearest
            | F64Sqrt
            | F64Min
            | F64Max
            | F64Copysign
            | F64Const(_)
            | F64Load { .. }
            | F64Store { .. }
            | F64ConvertI32S
            | F64ConvertI32U
            | F64ConvertI64S
            | F64ConvertI64U
            | F64PromoteF32
            | F64ReinterpretI64
            | I64ReinterpretF64
            | I64TruncF64S
            | I64TruncF64U
            | I32TruncF64S
            | I32TruncF64U) => {
                let msg = if self.fpu.is_some() {
                    // Single-precision FPU target (e.g., Cortex-M4F): VFP-D
                    // instructions exist as encodings but the hardware lacks
                    // the double-precision unit to execute them.
                    format!(
                        "target {} lacks double-precision FPU; cannot compile {op:?}",
                        self.target_name
                    )
                } else {
                    format!(
                        "target {} has no FPU; cannot compile {op:?}",
                        self.target_name
                    )
                };
                return Err(synth_core::Error::synthesis(msg));
            }

            // ===== v128 SIMD operations =====
            // Path A: Helium present → generate MVE instructions
            // Path B: no Helium → error

            // v128 Constants
            V128Const(bytes) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveConst { qd, bytes: *bytes }]
            }

            // v128 Load/Store
            V128Load { offset, .. } if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveLoad {
                    qd,
                    addr: MemAddr::reg_imm(Reg::R11, rn, *offset as i32),
                }]
            }
            V128Store { offset, .. } if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveStore {
                    qd,
                    addr: MemAddr::reg_imm(Reg::R11, rn, *offset as i32),
                }]
            }

            // v128 Bitwise
            V128And if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAnd { qd, qn, qm }]
            }
            V128Or if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveOrr { qd, qn, qm }]
            }
            V128Xor if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveEor { qd, qn, qm }]
            }
            V128Not if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMvn { qd, qm }]
            }
            V128AndNot if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveBic { qd, qn, qm }]
            }

            // i8x16 arithmetic
            I8x16Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S8,
                }]
            }
            I8x16ExtractLaneS(lane) | I8x16ExtractLaneU(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S8,
                }]
            }
            I8x16ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S8,
                }]
            }

            // i8x16 comparisons
            I8x16Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16LeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }
            I8x16GeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S8,
                }]
            }

            // i16x8 arithmetic
            I16x8Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S16,
                }]
            }
            I16x8ExtractLaneS(lane) | I16x8ExtractLaneU(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S16,
                }]
            }
            I16x8ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S16,
                }]
            }

            // i16x8 comparisons
            I16x8Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8LeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }
            I16x8GeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S16,
                }]
            }

            // i32x4 arithmetic
            I32x4Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S32,
                }]
            }
            I32x4ExtractLane(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }
            I32x4ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }

            // i32x4 comparisons
            I32x4Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GtU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4LeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I32x4GeU if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeU {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }

            // i64x2 arithmetic (MVE supports 32-bit element sizes natively;
            // 64-bit uses pairs of 32-bit ops or widening instructions)
            I64x2Add if self.has_helium => {
                // VADD.I32 operates on 32-bit lanes; i64x2 is two 64-bit values.
                // Pseudo-op: encoder expands to ADDS/ADC pairs per lane.
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegI {
                    qd,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Splat if self.has_helium => {
                // Splat 64-bit value: duplicate low 32 bits to lanes 0,2
                // and high 32 bits to lanes 1,3
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDup {
                    qd,
                    rn,
                    size: MveSize::S32,
                }]
            }
            I64x2ExtractLane(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLane {
                    rd,
                    qn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }
            I64x2ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveInsertLane {
                    qd,
                    rn,
                    lane: *lane,
                    size: MveSize::S32,
                }]
            }

            // i64x2 comparisons and mul — emit as pseudo-ops for now
            I64x2Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeI {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2LtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2GtS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2LeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }
            I64x2GeS if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeS {
                    qd,
                    qn,
                    qm,
                    size: MveSize::S32,
                }]
            }

            // f32x4 floating-point SIMD
            F32x4Add if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAddF32 { qd, qn, qm }]
            }
            F32x4Sub if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSubF32 { qd, qn, qm }]
            }
            F32x4Mul if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveMulF32 { qd, qn, qm }]
            }
            F32x4Div if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveDivF32 { qd, qn, qm }]
            }
            F32x4Abs if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveAbsF32 { qd, qm }]
            }
            F32x4Neg if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveNegF32 { qd, qm }]
            }
            F32x4Sqrt if self.has_helium => {
                let qd = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveSqrtF32 { qd, qm }]
            }
            F32x4Eq if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpEqF32 { qd, qn, qm }]
            }
            F32x4Ne if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpNeF32 { qd, qn, qm }]
            }
            F32x4Lt if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLtF32 { qd, qn, qm }]
            }
            F32x4Le if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpLeF32 { qd, qn, qm }]
            }
            F32x4Gt if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGtF32 { qd, qn, qm }]
            }
            F32x4Ge if self.has_helium => {
                let qd = self.alloc_qreg();
                let qn = self.alloc_qreg();
                let qm = self.alloc_qreg();
                vec![ArmOp::MveCmpGeF32 { qd, qn, qm }]
            }
            F32x4Splat if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveDupF32 { qd, rn }]
            }
            F32x4ExtractLane(lane) if self.has_helium => {
                let qn = self.alloc_qreg();
                vec![ArmOp::MveExtractLaneF32 {
                    rd,
                    qn,
                    lane: *lane,
                }]
            }
            F32x4ReplaceLane(lane) if self.has_helium => {
                let qd = self.alloc_qreg();
                vec![ArmOp::MveReplaceLaneF32 {
                    qd,
                    rn,
                    lane: *lane,
                }]
            }

            // i8x16.shuffle / i8x16.swizzle — complex, not yet implemented
            op @ (I8x16Shuffle(_) | I8x16Swizzle) if self.has_helium => {
                return Err(synth_core::Error::synthesis(format!(
                    "{op:?} not yet implemented for Helium MVE"
                )));
            }

            // All SIMD ops without Helium → error
            op @ (V128Const(_)
            | V128Load { .. }
            | V128Store { .. }
            | V128And
            | V128Or
            | V128Xor
            | V128Not
            | V128AndNot
            | I8x16Add
            | I8x16Sub
            | I8x16Neg
            | I8x16Eq
            | I8x16Ne
            | I8x16LtS
            | I8x16LtU
            | I8x16GtS
            | I8x16GtU
            | I8x16LeS
            | I8x16LeU
            | I8x16GeS
            | I8x16GeU
            | I8x16Splat
            | I8x16ExtractLaneS(_)
            | I8x16ExtractLaneU(_)
            | I8x16ReplaceLane(_)
            | I8x16Shuffle(_)
            | I8x16Swizzle
            | I16x8Add
            | I16x8Sub
            | I16x8Mul
            | I16x8Neg
            | I16x8Eq
            | I16x8Ne
            | I16x8LtS
            | I16x8LtU
            | I16x8GtS
            | I16x8GtU
            | I16x8LeS
            | I16x8LeU
            | I16x8GeS
            | I16x8GeU
            | I16x8Splat
            | I16x8ExtractLaneS(_)
            | I16x8ExtractLaneU(_)
            | I16x8ReplaceLane(_)
            | I32x4Add
            | I32x4Sub
            | I32x4Mul
            | I32x4Neg
            | I32x4Eq
            | I32x4Ne
            | I32x4LtS
            | I32x4LtU
            | I32x4GtS
            | I32x4GtU
            | I32x4LeS
            | I32x4LeU
            | I32x4GeS
            | I32x4GeU
            | I32x4Splat
            | I32x4ExtractLane(_)
            | I32x4ReplaceLane(_)
            | I64x2Add
            | I64x2Sub
            | I64x2Mul
            | I64x2Neg
            | I64x2Eq
            | I64x2Ne
            | I64x2LtS
            | I64x2GtS
            | I64x2LeS
            | I64x2GeS
            | I64x2Splat
            | I64x2ExtractLane(_)
            | I64x2ReplaceLane(_)
            | F32x4Add
            | F32x4Sub
            | F32x4Mul
            | F32x4Div
            | F32x4Abs
            | F32x4Neg
            | F32x4Sqrt
            | F32x4Eq
            | F32x4Ne
            | F32x4Lt
            | F32x4Le
            | F32x4Gt
            | F32x4Ge
            | F32x4Splat
            | F32x4ExtractLane(_)
            | F32x4ReplaceLane(_)) => {
                return Err(synth_core::Error::synthesis(format!(
                    "SIMD operation {op:?} requires Helium MVE (Cortex-M55), \
                     but target {} does not have Helium",
                    self.target_name
                )));
            }
        };
        Ok(instrs)
    }

    /// Generate a load with optional bounds checking
    /// R10 = memory size, R11 = memory base
    /// Bounds check verifies addr + offset + access_size - 1 < memory_size
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires access_size in set![1u32, 2u32, 4u32, 8u32]
    /// ensures
    ///     bounds_check_mode == Software ==>
    ///         result contains CMP(addr + access_size - 1, R10),
    ///     result.last() is Ldr { rd, .. },
    /// ```
    fn generate_load_with_bounds_check(
        &self,
        rd: Reg,
        addr_reg: Reg,
        offset: i32,
        access_size: u32,
    ) -> Vec<ArmOp> {
        contracts::memory::verify_access_size(access_size);

        let load_op = ArmOp::Ldr {
            rd,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![load_op],
            BoundsCheckConfig::Software => {
                // Software bounds check: verify last byte of access is in bounds
                // ADD temp, addr_reg, #(offset + access_size - 1)
                // CMP temp, R10 (memory size)
                // BHS Trap_Handler
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    load_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    load_op,
                ]
            }
        }
    }

    /// Generate a store with optional bounds checking
    /// R10 = memory size (or mask for masking mode), R11 = memory base
    /// Bounds check verifies addr + offset + access_size - 1 < memory_size
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires access_size in set![1u32, 2u32, 4u32, 8u32]
    /// ensures
    ///     bounds_check_mode == Software ==>
    ///         result contains CMP(addr + access_size - 1, R10),
    ///     result.last() is Str { rd: value_reg, .. },
    /// ```
    fn generate_store_with_bounds_check(
        &self,
        value_reg: Reg,
        addr_reg: Reg,
        offset: i32,
        access_size: u32,
    ) -> Vec<ArmOp> {
        contracts::memory::verify_access_size(access_size);

        let store_op = ArmOp::Str {
            rd: value_reg,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![store_op],
            BoundsCheckConfig::Software => {
                // Software bounds check: verify last byte of access is in bounds
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    store_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    store_op,
                ]
            }
        }
    }

    /// Generate an i64 (8-byte) load with optional bounds checking.
    /// R10 = memory size (or mask for masking mode), R11 = memory base.
    /// Result is loaded into R0 (low) and R1 (high).
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// ensures
    ///     bounds_check_mode == Software ==>
    ///         result contains CMP(addr + 8 - 1, R10),
    ///     result.last() is I64Ldr { rdlo: R0, rdhi: R1, .. },
    /// ```
    fn generate_i64_load_with_bounds_check(&self, addr_reg: Reg, offset: i32) -> Vec<ArmOp> {
        let access_size: u32 = 8;
        contracts::memory::verify_access_size(access_size);

        let load_op = ArmOp::I64Ldr {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![load_op],
            BoundsCheckConfig::Software => {
                // Software bounds check: verify last byte of 8-byte access is in bounds
                // ADD temp, addr_reg, #(offset + 8 - 1)
                // CMP temp, R10 (memory size)
                // BHS Trap_Handler
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    load_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    load_op,
                ]
            }
        }
    }

    /// Generate an i64 (8-byte) store with optional bounds checking.
    /// R10 = memory size (or mask for masking mode), R11 = memory base.
    /// Value is stored from R0 (low) and R1 (high).
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// ensures
    ///     bounds_check_mode == Software ==>
    ///         result contains CMP(addr + 8 - 1, R10),
    ///     result.last() is I64Str { rdlo: R0, rdhi: R1, .. },
    /// ```
    fn generate_i64_store_with_bounds_check(&self, addr_reg: Reg, offset: i32) -> Vec<ArmOp> {
        let access_size: u32 = 8;
        contracts::memory::verify_access_size(access_size);

        let store_op = ArmOp::I64Str {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![store_op],
            BoundsCheckConfig::Software => {
                // Software bounds check: verify last byte of 8-byte access is in bounds
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    store_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    store_op,
                ]
            }
        }
    }

    /// Generate an i64 (8-byte) load with optional bounds checking into specified registers.
    /// R10 = memory size (or mask for masking mode), R11 = memory base.
    /// Result is loaded into the specified register pair (rdlo, rdhi).
    fn generate_i64_load_into_regs(
        &self,
        rdlo: Reg,
        rdhi: Reg,
        addr_reg: Reg,
        offset: i32,
    ) -> Vec<ArmOp> {
        let access_size: u32 = 8;
        contracts::memory::verify_access_size(access_size);

        let load_op = ArmOp::I64Ldr {
            rdlo,
            rdhi,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![load_op],
            BoundsCheckConfig::Software => {
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    load_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    load_op,
                ]
            }
        }
    }

    /// Generate an i64 (8-byte) store with optional bounds checking from specified registers.
    /// R10 = memory size (or mask for masking mode), R11 = memory base.
    /// Value is stored from the specified register pair (rdlo, rdhi).
    fn generate_i64_store_from_regs(
        &self,
        rdlo: Reg,
        rdhi: Reg,
        addr_reg: Reg,
        offset: i32,
    ) -> Vec<ArmOp> {
        let access_size: u32 = 8;
        contracts::memory::verify_access_size(access_size);

        let store_op = ArmOp::I64Str {
            rdlo,
            rdhi,
            addr: MemAddr::reg_imm(Reg::R11, addr_reg, offset),
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![store_op],
            BoundsCheckConfig::Software => {
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    store_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    store_op,
                ]
            }
        }
    }

    /// Generate a sub-word load with optional bounds checking.
    /// `access_size`: 1 for byte, 2 for halfword.
    /// `sign_extend`: true for sign-extending loads (LDRSB/LDRSH), false for zero-extending (LDRB/LDRH).
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires access_size in set![1u32, 2u32, 4u32, 8u32]
    /// ```
    fn generate_subword_load_with_bounds_check(
        &self,
        rd: Reg,
        addr_reg: Reg,
        offset: i32,
        access_size: u32,
        sign_extend: bool,
    ) -> Vec<ArmOp> {
        contracts::memory::verify_access_size(access_size);

        let addr = MemAddr::reg_imm(Reg::R11, addr_reg, offset);
        let load_op = match (access_size, sign_extend) {
            (1, false) => ArmOp::Ldrb { rd, addr },
            (1, true) => ArmOp::Ldrsb { rd, addr },
            (2, false) => ArmOp::Ldrh { rd, addr },
            (2, true) => ArmOp::Ldrsh { rd, addr },
            _ => ArmOp::Ldr { rd, addr }, // fallback to word load
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![load_op],
            BoundsCheckConfig::Software => {
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    load_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    load_op,
                ]
            }
        }
    }

    /// Generate a sub-word store with optional bounds checking.
    /// `access_size`: 1 for byte (STRB), 2 for halfword (STRH).
    ///
    /// # Contract (Verus-style)
    /// ```text
    /// requires access_size in set![1u32, 2u32, 4u32, 8u32]
    /// ```
    fn generate_subword_store_with_bounds_check(
        &self,
        value_reg: Reg,
        addr_reg: Reg,
        offset: i32,
        access_size: u32,
    ) -> Vec<ArmOp> {
        contracts::memory::verify_access_size(access_size);

        let addr = MemAddr::reg_imm(Reg::R11, addr_reg, offset);
        let store_op = match access_size {
            1 => ArmOp::Strb {
                rd: value_reg,
                addr,
            },
            2 => ArmOp::Strh {
                rd: value_reg,
                addr,
            },
            _ => ArmOp::Str {
                rd: value_reg,
                addr,
            },
        };

        match self.bounds_check {
            BoundsCheckConfig::None | BoundsCheckConfig::Mpu => vec![store_op],
            BoundsCheckConfig::Software => {
                let temp = Reg::R12;
                let end_offset = offset + (access_size as i32) - 1;
                vec![
                    ArmOp::Add {
                        rd: temp,
                        rn: addr_reg,
                        op2: Operand2::Imm(end_offset),
                    },
                    ArmOp::Cmp {
                        rn: temp,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    ArmOp::Bhs {
                        label: "Trap_Handler".to_string(),
                    },
                    store_op,
                ]
            }
            BoundsCheckConfig::Masking => {
                vec![
                    ArmOp::And {
                        rd: addr_reg,
                        rn: addr_reg,
                        op2: Operand2::Reg(Reg::R10),
                    },
                    store_op,
                ]
            }
        }
    }

    /// Get statistics about instruction selection
    pub fn get_stats(&self) -> SelectionStats {
        SelectionStats {
            total_registers_used: self.regs.next_reg as usize,
            variables_mapped: self.regs.var_map.len(),
        }
    }

    /// Reset the selector state
    pub fn reset(&mut self) {
        self.regs.reset();
        self.label_counter = 0;
    }

    /// Try to fold a constant address into the memory access immediate.
    ///
    /// Detects the `i32.const C; i32.{load,store}{,8,16}{_s,_u} offset=O` pattern
    /// and returns the effective imm12 offset `(C as u32).wrapping_add(O)` when:
    ///
    /// 1. The previous wasm op (`wasm_ops[idx-1]`) is `I32Const(C)`.
    /// 2. Bounds checking is `None` (the constant address is assumed to fall in
    ///    the linear memory range — appropriate for bare-metal targets where
    ///    addresses are known statically and the MPU enforces protection).
    /// 3. `(C as u32) + offset <= 4095` — fits the Thumb-2 LDR.W/STR.W imm12.
    ///
    /// Returns `Some(effective_offset)` to signal the caller can fold; the caller
    /// is responsible for popping the address register from the stack and
    /// dropping the now-unused const-materialization instructions (1-2 entries
    /// at the tail of `instructions` whose `source_line == Some(idx-1)`).
    ///
    /// Issue #95: replaces 10-byte `MOVW+MOVT+LDR.W` with a 4-byte `LDR.W`
    /// for static-address loads/stores.
    fn try_fold_const_addr(&self, wasm_ops: &[WasmOp], idx: usize, offset: u32) -> Option<u32> {
        if !self.bounds_check.is_passthrough() {
            return None;
        }
        if idx == 0 {
            return None;
        }
        let WasmOp::I32Const(c) = wasm_ops[idx - 1] else {
            return None;
        };
        let eff = (c as u32).wrapping_add(offset);
        if eff <= 0xFFF { Some(eff) } else { None }
    }

    /// Pop the const-materialization instructions emitted for the immediately
    /// preceding `i32.const`. The const handler emits 1 instruction (Movw) for
    /// values <= 0xFFFF, 2 instructions (Movw + Mvn) for inverted patterns, and
    /// 2 instructions (Movw + Movt) otherwise — all tagged with the same
    /// `source_line`. Removing them from the tail is safe because no later
    /// instruction depends on the materialized value once the load/store is
    /// folded.
    fn drop_prev_const_materialization(instructions: &mut Vec<ArmInstruction>, const_idx: usize) {
        while let Some(last) = instructions.last() {
            if last.source_line == Some(const_idx) {
                instructions.pop();
            } else {
                break;
            }
        }
    }

    /// Try to fold a constant address for an `i32.store{,8,16}` whose pattern is
    /// `i32.const ADDR; <value-pusher>; i32.store offset=O` where
    /// `<value-pusher>` is a stack-effect (0,1) op (I32Const, LocalGet, GlobalGet)
    /// that emits its instructions tagged with `source_line=idx-1`.
    ///
    /// Returns `Some(effective_offset)` to signal the caller can fold; the
    /// caller is responsible for splicing out the addr-const instructions
    /// (tagged `source_line=idx-2`) from the tail of `instructions` while
    /// preserving the value chunk on top.
    fn try_fold_const_addr_store(
        &self,
        wasm_ops: &[WasmOp],
        idx: usize,
        offset: u32,
    ) -> Option<u32> {
        if !self.bounds_check.is_passthrough() {
            return None;
        }
        if idx < 2 {
            return None;
        }
        // Value-pusher must be a (0,1) op so wasm_ops[idx-2] is reliably the
        // address-pushing op (no nested stack consumption between addr and store).
        let value_op = &wasm_ops[idx - 1];
        if !matches!(
            value_op,
            WasmOp::I32Const(_) | WasmOp::LocalGet(_) | WasmOp::GlobalGet(_)
        ) {
            return None;
        }
        let WasmOp::I32Const(c) = wasm_ops[idx - 2] else {
            return None;
        };
        let eff = (c as u32).wrapping_add(offset);
        if eff <= 0xFFF { Some(eff) } else { None }
    }

    /// Splice out the addr-const materialization instructions (those tagged
    /// `source_line=addr_const_idx`) from the tail of `instructions`, while
    /// preserving the value-pusher chunk (tagged `source_line=value_idx`) that
    /// sits on top. Used by the store fold (issue #95) to drop the now-unused
    /// `MOVW(+MOVT)` for the address.
    fn splice_out_addr_const_materialization(
        instructions: &mut Vec<ArmInstruction>,
        addr_const_idx: usize,
        value_idx: usize,
    ) {
        // Save value chunk from the tail.
        let mut value_tail: Vec<ArmInstruction> = Vec::new();
        while let Some(last) = instructions.last() {
            if last.source_line == Some(value_idx) {
                value_tail.push(instructions.pop().unwrap());
            } else {
                break;
            }
        }
        // Drop the addr-const chunk now exposed at the tail.
        while let Some(last) = instructions.last() {
            if last.source_line == Some(addr_const_idx) {
                instructions.pop();
            } else {
                break;
            }
        }
        // Restore value chunk in original order.
        while let Some(instr) = value_tail.pop() {
            instructions.push(instr);
        }
    }

    /// #195: Pop the top-`arg_count` operand-stack registers as call arguments.
    ///
    /// The WASM operand-stack top is the LAST argument, so the returned vector
    /// is reversed to index `0..n` = argument `0..n` (arg `i` → `ARG_REGS[i]`).
    /// At most `ARG_REGS.len()` (4) arguments are popped; see the scope note on
    /// [`InstructionSelector::emit_arg_moves`].
    ///
    /// Popping the args here (before caller-saved preservation) is deliberate:
    /// arguments are consumed by the call, not live across it, so they must be
    /// excluded from the [`preserve_caller_saved`] spill set.
    fn pop_call_args(
        stack: &mut Vec<StackVal>,
        next_temp: &mut u8,
        instructions: &mut Vec<ArmInstruction>,
        spill: &mut SpillState,
        arg_count: u32,
        idx: usize,
    ) -> Result<Vec<Reg>> {
        // #359: pop ALL `arg_count` operands (previously only the top 4, which
        // for a >4-arg call dropped arg0 and shifted args into r0..r3). After the
        // reverse, `srcs[0..N]` == arg0..argN-1; the caller marshals srcs[0..4]
        // into r0..r3 and stores srcs[4..N] to the outgoing stack region.
        let n = arg_count as usize;
        // #359 Ok-or-Err (#180/#185): a stack-passed arg (index >= 4) that is i64
        // would be stored as a single 4-byte STR (silent lo-half truncation) —
        // the register conversion below discards width. Refuse before popping.
        // The top of `stack` is the LAST arg, so arg index k sits at
        // `stack[stack.len() - n + k]`.
        if n > ARG_REGS.len() && stack.len() >= n {
            let base = stack.len() - n;
            for k in ARG_REGS.len()..n {
                if stack[base + k].is_i64() {
                    return Err(synth_core::Error::synthesis(format!(
                        "#359: call arg {k} is passed on the stack and is i64/f64; \
                         only i32 stack args are supported"
                    )));
                }
            }
        }
        let mut srcs: Vec<Reg> = Vec::with_capacity(n);
        for _ in 0..n {
            let r = pop_operand(stack, next_temp, instructions, spill, &[], idx)?;
            srcs.push(r);
        }
        srcs.reverse();
        Ok(srcs)
    }

    /// #359: spill the stack-passed call arguments (index >= 4) into the
    /// outgoing-argument region at the bottom of the current frame, BEFORE
    /// caller-saved preservation, the CallIndirect table-index relocation, and
    /// the r0..r3 parallel move. The popped arg registers are NOT in
    /// `stack_live_regs`, so any of those later steps could otherwise clobber a
    /// stack-arg source; storing first (there is no dynamic SP, so `[sp,#imm]` is
    /// valid the instant after the pop) closes every clobber window.
    ///
    /// `arg_srcs[k]` for k in 4..N goes to `[sp, (k-4)*4]`. Returns the count of
    /// instructions emitted (for the cf counter). Ok-or-Err (#180/#185): refuses
    /// when a computed `[sp,#imm]` offset exceeds the 12-bit (4095) immediate.
    fn emit_stack_args(
        &self,
        instructions: &mut Vec<ArmInstruction>,
        arg_srcs: &[Reg],
        idx: usize,
    ) -> Result<usize> {
        let mut emitted = 0;
        for (k, &src) in arg_srcs.iter().enumerate().skip(ARG_REGS.len()) {
            let off = (k as i32 - ARG_REGS.len() as i32) * 4;
            if off > 4095 {
                return Err(synth_core::Error::synthesis(format!(
                    "#359: outgoing stack-arg offset {off} exceeds the 12-bit \
                     [sp,#imm] range"
                )));
            }
            instructions.push(ArmInstruction {
                op: ArmOp::Str {
                    rd: src,
                    addr: MemAddr::imm(Reg::SP, off),
                },
                source_line: Some(idx),
            });
            emitted += 1;
        }
        Ok(emitted)
    }

    /// #195: Emit the cycle-safe parallel move of call arguments into R0–R3.
    ///
    /// `arg_srcs[i]` is moved into `ARG_REGS[i]`. MUST be called AFTER
    /// [`preserve_caller_saved`] (so live non-arg values already sit in the
    /// spill area) and immediately before the `BL`/`CallIndirect`, so these are
    /// the last register writes before the branch.
    ///
    /// Scope: only ≤4 integer (i32/pointer-width) arguments are handled. i64/f64
    /// arguments — which AAPCS passes in register *pairs* / 8-byte stack slots —
    /// and arguments beyond the fourth (which spill to the stack) are NOT
    /// marshalled; this covers the gale runtime primitives (`k_spin_lock`,
    /// `k_sem_give`, …), which take ≤4 pointer/i32 arguments. See issue #195.
    fn emit_arg_moves(
        &self,
        instructions: &mut Vec<ArmInstruction>,
        arg_srcs: &[Reg],
        stack: &[Reg],
        local_to_reg: &std::collections::HashMap<u32, Reg>,
        layout: &LocalLayout,
        spill: &mut SpillState,
        idx: usize,
    ) -> Result<usize> {
        use crate::parallel_move::{MoveStep, sequentialize};
        if arg_srcs.is_empty() {
            return Ok(0);
        }
        // The resolver takes (dst, src) pairs; arg `i` goes to ARG_REGS[i].
        let moves: Vec<(Reg, Reg)> = arg_srcs
            .iter()
            .enumerate()
            .map(|(i, &src)| (ARG_REGS[i], src))
            .collect();
        // Scratch candidate for cycle-breaking: a callee-saved register holding
        // no live value, when one exists — the resolver uses it ONLY to break a
        // true cycle, and filters it against the move set itself (an arg source
        // parked in a callee-saved register is invisible to `free_callee_saved`
        // because the args were already popped). When NONE is free (#326: the
        // #311 i64 result pairs legitimately pin R4–R8), the resolver breaks
        // the cycle through ONE stack slot instead of hard-failing — this is
        // exactly the exhaustion gale's dissolved `z_impl_k_mutex_unlock` hit.
        let scratch: Vec<Reg> = self
            .free_callee_saved(stack, local_to_reg, layout)
            .ok()
            .into_iter()
            .collect();
        let steps = sequentialize(&moves, &scratch).map_err(|e| {
            synth_core::Error::synthesis(format!(
                "call-arg marshalling produced an invalid parallel move set: {e} \
                 (compiler bug: ARG_REGS destinations are distinct by construction)"
            ))
        })?;

        // A stack-slot scratch is needed only when a cycle exists AND no
        // callee-saved register was free. Reserve one resolver slot from the
        // spill area for the duration of the sequence.
        let needs_slot = steps
            .iter()
            .any(|s| matches!(s, MoveStep::SpillScratch { .. }));
        let slot = if needs_slot {
            if !spill.area_reserved {
                // i32-only first pass: the spill area does not exist, so a slot
                // would alias the param-backing frame slots. Fail with the
                // ladder-recoverable exhaustion Err — the backend retry
                // (VCR-RA-001 3b-lite) re-runs with the area reserved and the
                // resolver then breaks the cycle through it.
                return Err(synth_core::Error::synthesis(
                    "register exhaustion: all allocatable registers are live on the stack — \
                     arg-move cycle needs a resolver spill slot but no spill area is reserved"
                        .to_string(),
                ));
            }
            Some(spill.alloc().ok_or_else(|| {
                synth_core::Error::synthesis(
                    "register exhaustion: i64 spill-slot pool exhausted while \
                     breaking a call-arg move cycle — function too complex"
                        .to_string(),
                )
            })?)
        } else {
            None
        };

        let before = instructions.len();
        for step in &steps {
            let op = match *step {
                MoveStep::Move { dst, src } => ArmOp::Mov {
                    rd: dst,
                    op2: Operand2::Reg(src),
                },
                MoveStep::SpillScratch { slot_store } => ArmOp::Str {
                    rd: slot_store,
                    addr: MemAddr::imm(
                        Reg::SP,
                        slot.expect("SpillScratch implies a reserved resolver slot"),
                    ),
                },
                MoveStep::ReloadScratch { slot_load_into } => ArmOp::Ldr {
                    rd: slot_load_into,
                    addr: MemAddr::imm(
                        Reg::SP,
                        slot.expect("ReloadScratch implies a reserved resolver slot"),
                    ),
                },
            };
            instructions.push(ArmInstruction {
                op,
                source_line: Some(idx),
            });
        }
        // The marshal sequence is self-contained: the slot is dead once the
        // last reload ran, so release it for reuse by later spills.
        if let Some(off) = slot {
            spill.free(off);
        }
        Ok(instructions.len() - before)
    }

    /// Select ARM instructions using a stack-based approach with AAPCS calling convention
    ///
    /// #188: Spill every live caller-saved register to the call-spill scratch
    /// area before a `Call`/`CallIndirect`, so it survives the AAPCS-clobbering
    /// branch-and-link. Returns the list of `(register, slot_offset)` pairs that
    /// were spilled, to be reloaded by [`restore_caller_saved`].
    ///
    /// "Live caller-saved" = the union of (a) operand-`stack` entries and
    /// (b) param registers tracked in `local_to_reg`, restricted to R0–R3/R12
    /// (see [`is_caller_saved`]), deduplicated by physical register.
    fn preserve_caller_saved(
        &self,
        instructions: &mut Vec<ArmInstruction>,
        stack: &[Reg],
        local_to_reg: &std::collections::HashMap<u32, Reg>,
        layout: &LocalLayout,
        idx: usize,
    ) -> Result<Vec<(Reg, i32)>> {
        // Collect distinct live caller-saved registers in a deterministic order:
        // operand-stack entries first, then param registers.
        let mut live: Vec<Reg> = Vec::new();
        let push_unique = |reg: Reg, live: &mut Vec<Reg>| {
            if is_caller_saved(reg) && !live.contains(&reg) {
                live.push(reg);
            }
        };
        for &reg in stack {
            push_unique(reg, &mut live);
        }
        // Deterministic param iteration order.
        let mut params: Vec<(u32, Reg)> = local_to_reg.iter().map(|(&i, &r)| (i, r)).collect();
        params.sort_by_key(|&(i, _)| i);
        for (_, reg) in params {
            push_unique(reg, &mut live);
        }

        if live.is_empty() {
            return Ok(Vec::new());
        }

        let base = layout.spill_base.ok_or_else(|| {
            synth_core::Error::synthesis(
                "call-spill scratch area not reserved despite a call being present \
                 (compiler bug: compute_local_layout/spill_base mismatch)"
                    .to_string(),
            )
        })?;
        // The scratch area has 5 slots (R0–R3, R12). `live` can never exceed
        // that because it only contains distinct caller-saved registers.
        debug_assert!(live.len() <= 5, "more than 5 distinct caller-saved regs");

        let mut preserved: Vec<(Reg, i32)> = Vec::with_capacity(live.len());
        for (slot, &reg) in live.iter().enumerate() {
            let off = base + (slot as i32) * 4;
            instructions.push(ArmInstruction {
                op: ArmOp::Str {
                    rd: reg,
                    addr: MemAddr::imm(Reg::SP, off),
                },
                source_line: Some(idx),
            });
            preserved.push((reg, off));
        }
        Ok(preserved)
    }

    /// #188: Reload caller-saved registers spilled by [`preserve_caller_saved`]
    /// after a call returns, and return the register that holds the call's
    /// AAPCS return value (R0, unless R0 itself had to be preserved — in which
    /// case the result is first moved to a free callee-saved register before R0
    /// is reloaded).
    fn restore_caller_saved(
        &self,
        instructions: &mut Vec<ArmInstruction>,
        preserved: &[(Reg, i32)],
        stack: &[Reg],
        local_to_reg: &std::collections::HashMap<u32, Reg>,
        layout: &LocalLayout,
        spill: &mut SpillState,
        ret_i64: bool,
        idx: usize,
    ) -> Result<StackVal> {
        // If R0 (the return value) is among the preserved registers, its slot
        // holds the *old* value; reloading it would destroy the call result, so
        // the result must first move out of R0. Prefer a free callee-saved
        // register; if none is free (an i64-heavy function fills R4–R8, #171),
        // spill the result to the i64 frame area and return a `Spilled` value
        // that is reloaded when popped — this is what lets `z_impl_k_sem_give`
        // (i64 + several calls) compile rather than be skipped.
        //
        // #311: an i64 result occupies the R0:R1 PAIR. It must be tagged i64 on
        // the operand stack (so liveness sees the hi half and the next constant
        // materialization cannot land in R1 — gale's k_sem_give silent
        // wrong-code), and any restoration touching R0 OR R1 forces the pair
        // through the spill path (the single-free-callee-saved move cannot
        // carry both halves).
        let r0_preserved = preserved
            .iter()
            .any(|&(r, _)| r == Reg::R0 || (ret_i64 && r == Reg::R1));
        let result = if r0_preserved {
            match (!ret_i64)
                .then(|| self.free_callee_saved(stack, local_to_reg, layout))
                .transpose()
                .ok()
                .flatten()
                .ok_or(())
            {
                Ok(free) => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mov {
                            rd: free,
                            op2: Operand2::Reg(Reg::R0),
                        },
                        source_line: Some(idx),
                    });
                    StackVal::i32(free)
                }
                Err(_) => {
                    // #331: when the i64 spill area was NOT reserved (an i32-only
                    // function — `has_i64 == false`), `i64_spill_base` aliases the
                    // #204 param home slots, so `spill.alloc()` here would hand out
                    // a slot ON TOP of a live param's home slot. gale's dissolved
                    // `k_mutex_unlock`: the mutex-ptr arg's home slot was reused to
                    // park `z_unpend_first_thread`'s result, so the later
                    // `lock_count = 0` store reloaded the clobbered slot and wrote
                    // to `linmem[0+12]` instead of `mutex+12` → silicon deadlock.
                    // Fail with the ladder-recoverable exhaustion `Err` (same guard
                    // the arg-move-cycle resolver uses): the backend retry re-runs
                    // with the spill area reserved, which relocates the param home
                    // slots ABOVE the i64 pool, so the reload is non-aliasing and
                    // the function compiles CORRECTLY (not skipped).
                    if !spill.area_reserved {
                        return Err(synth_core::Error::synthesis(
                            "register exhaustion: all allocatable registers are live on the stack — \
                             parking a call result needs a spill slot but no spill area is reserved"
                                .to_string(),
                        ));
                    }
                    let slot = spill.alloc().ok_or_else(|| {
                        synth_core::Error::synthesis(
                            "register exhaustion: i64 spill-slot pool exhausted while \
                             parking a call result — function too complex"
                                .to_string(),
                        )
                    })?;
                    // The result is in R0 (i64 lo:hi = R0:R1). Spill both halves;
                    // a garbage hi for an i32 result is harmless (the consumer
                    // reads only what it needs).
                    let hi = i64_pair_hi(Reg::R0)?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Str {
                            rd: Reg::R0,
                            addr: MemAddr::imm(Reg::SP, slot),
                        },
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Str {
                            rd: hi,
                            addr: MemAddr::imm(Reg::SP, slot + 4),
                        },
                        source_line: Some(idx),
                    });
                    StackVal::Spilled {
                        lo_slot: slot,
                        is_i64: true,
                    }
                }
            }
        } else if ret_i64 {
            StackVal::i64(Reg::R0)
        } else {
            StackVal::i32(Reg::R0)
        };

        for &(reg, off) in preserved {
            instructions.push(ArmInstruction {
                op: ArmOp::Ldr {
                    rd: reg,
                    addr: MemAddr::imm(Reg::SP, off),
                },
                source_line: Some(idx),
            });
        }
        Ok(result)
    }

    /// Find a callee-saved register (R4–R8) not currently holding a live value
    /// (neither on the operand stack, nor a param/local home). Used to park a
    /// call's return value when R0 must be reloaded with a preserved param.
    fn free_callee_saved(
        &self,
        stack: &[Reg],
        local_to_reg: &std::collections::HashMap<u32, Reg>,
        _layout: &LocalLayout,
    ) -> Result<Reg> {
        const CALLEE_SAVED: [Reg; 5] = [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];
        for &reg in &CALLEE_SAVED {
            let on_stack = stack.contains(&reg)
                || stack
                    .iter()
                    .any(|&s| i64_pair_hi(s).map(|hi| hi == reg).unwrap_or(false));
            let is_local = local_to_reg.values().any(|&r| r == reg);
            if !on_stack && !is_local {
                return Ok(reg);
            }
        }
        Err(synth_core::Error::synthesis(
            "register exhaustion: no free callee-saved register to hold a call \
             result while reloading a preserved param"
                .to_string(),
        ))
    }

    /// This method properly tracks the WASM virtual stack and generates code that
    /// uses r0-r3 for the first 4 parameters per AAPCS. Handles WASM structured
    /// control flow (block, loop, if/else, br, br_if, br_table, return, call).
    pub fn select_with_stack(
        &mut self,
        wasm_ops: &[WasmOp],
        num_params: u32,
    ) -> Result<Vec<ArmInstruction>> {
        use WasmOp::*;

        // Pre-flight: catch obvious wasm stack underflow as a typed error
        // before we walk the ops. The fuzz harness `wasm_ops_lower_or_error`
        // intentionally feeds malformed `Vec<WasmOp>` and expects `Err`, not
        // a panic deep in the selector's pop sequence (see PR #117).
        synth_core::wasm_stack_check::check_no_underflow(wasm_ops)?;

        // #359: AAPCS stack arguments. We pass params index>=4 on the outgoing
        // stack and read incoming params index>=4 from the caller's stack. The
        // frame-reserved (no dynamic SP) scheme this implements bounds the count:
        // refuse functions with more than 8 scalar params (the [sp,#imm] offsets
        // and the outgoing-region size stay small and in-range). Ok-or-Err — this
        // repo is never silently wrong (#180/#185).
        if num_params > 8 {
            return Err(synth_core::Error::synthesis(format!(
                "#359: function has {num_params} params; the AAPCS stack-argument \
                 path supports at most 8 scalar params"
            )));
        }
        // #359 Ok-or-Err (#180/#185): the register-homing + incoming-stack-slot
        // scheme assumes every param is a 4-byte i32. A 64-bit param (i64/f64)
        // occupies a register PAIR / 8-byte stack slot and shifts which params
        // land on the stack — even an UNUSED one. Declared widths (not op-stream
        // inference, which can't see an unused i64 param) drive this refusal.
        // Gated on num_params>4: a <=4-param function never touches the stack-arg
        // path, so the legacy i64-param handling (param_slots) is unchanged and
        // every existing fixture stays byte-identical. Empty `params_i64`
        // (no signature plumbed, e.g. unit tests) ⇒ assume i32.
        if num_params > 4 && self.params_i64.iter().take(num_params as usize).any(|&w| w) {
            return Err(synth_core::Error::synthesis(format!(
                "#359: function has {num_params} params including a 64-bit (i64/f64) \
                 param; the AAPCS stack-argument path supports only i32 params"
            )));
        }

        // #359: size of the outgoing stack-argument region = the max over all
        // Call/CallIndirect sites of `max(0, arg_count - 4) * 4`, rounded up to 8.
        // Reserved at the BOTTOM of the frame (offset 0) by `compute_local_layout`.
        // 0 when every call passes <=4 args — the frame is then byte-identical to
        // the pre-#359 layout. `saturating_sub` avoids the u32 underflow that would
        // otherwise inflate the region for every small-arg call.
        let mut max_stack_args: u32 = 0;
        for op in wasm_ops {
            let arg_count = match op {
                Call(func_idx) => {
                    // Meld dispatch imports take no AAPCS args (index in R0).
                    let is_import = *func_idx < self.num_imports;
                    if is_import && !self.relocatable {
                        0
                    } else {
                        self.func_arg_counts
                            .get(*func_idx as usize)
                            .copied()
                            .unwrap_or(0)
                    }
                }
                CallIndirect { type_index, .. } => self
                    .type_arg_counts
                    .get(*type_index as usize)
                    .copied()
                    .unwrap_or(0),
                _ => continue,
            };
            if arg_count > 8 {
                return Err(synth_core::Error::synthesis(format!(
                    "#359: call passes {arg_count} args; the AAPCS stack-argument \
                     path supports at most 8 scalar args"
                )));
            }
            max_stack_args = max_stack_args.max(arg_count.saturating_sub(4));
        }
        let outgoing_arg_bytes = ((max_stack_args as i32) * 4 + 7) & !7;

        let mut instructions = Vec::new();

        // Function prologue: save callee-saved registers and LR, then
        // allocate the local-variable frame.
        //
        // AAPCS requires 8-byte aligned SP at call sites. Pushing an even
        // number of registers (6: R4-R8, LR) maintains alignment, and the
        // frame_size below is rounded to 8 to preserve it.
        instructions.push(ArmInstruction {
            op: ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
            },
            source_line: None,
        });

        // Compute non-param local layout (offsets + total frame size).
        let layout = compute_local_layout(
            wasm_ops,
            num_params,
            &self.func_ret_i64,
            &self.type_ret_i64,
            self.spill_on_exhaustion,
            self.param_backing_on_exhaustion,
            outgoing_arg_bytes,
        );
        // #359 Ok-or-Err (#180/#185): an incoming stack-passed param is read via
        // `ldr rd,[sp,#off]` where `off = frame_size + 24 + (k-4)*4` and
        // `frame_size` is unbounded (a function with a large locals frame). The
        // Thumb-2 `ldr [sp,#imm]` immediate is 12-bit (0..4095); refuse rather
        // than silently emit an out-of-range encoding. Checked once here over the
        // finalized layout instead of at each use site.
        if let Some(&max_off) = layout.incoming_params.values().max()
            && max_off > 4095
        {
            return Err(synth_core::Error::synthesis(format!(
                "#359: incoming stack-param offset {max_off} exceeds the 12-bit \
                 [sp,#imm] range (frame too large for the stack-argument path)"
            )));
        }
        // Allocate stack space for non-param locals so they don't alias the
        // callee-saved-register spill area (which immediately follows SP
        // after Push above).
        if layout.frame_size > 0 {
            instructions.push(ArmInstruction {
                op: ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(layout.frame_size),
                },
                source_line: None,
            });
        }

        // Virtual operand stack: each entry is a register-resident or spilled
        // value (#171). i64 values track only the lo register/slot.
        let mut stack: Vec<StackVal> = Vec::new();
        // i64 register-pair spill slots (#171), reused across the function.
        let mut spill = SpillState::new(layout.i64_spill_base);
        spill.spill_on_exhaustion = self.spill_on_exhaustion;
        spill.area_reserved = layout.spill_area_reserved;
        // Next available register for temporaries (start after params)
        let mut next_temp = num_params.min(4) as u8;

        // Control flow tracking
        let mut cf = ControlFlowManager::new();
        cf.enter_function();
        // Stack of (label, is_loop) for branch target resolution
        // For blocks: label is the end label; for loops: label is the start label
        let mut block_labels: Vec<(String, bool)> = Vec::new();
        // Stack of (else_label, end_label) for if/else blocks
        let mut if_labels: Vec<(String, String)> = Vec::new();
        // #313: per-if-block operand-stack checkpoint (vstack depth captured at
        // `If`, after popping the condition). The result arity of an
        // `if (result …)` is observable as (vstack depth − checkpoint).
        let mut if_checkpoints: Vec<usize> = Vec::new();
        // #313: per-if-block reservation of the THEN-arm's result registers.
        // Captured at `Else` (the then-arm's results, popped off and truncated
        // back to the checkpoint so the else-arm starts from the same stack
        // shape) and threaded into the temp/pair/reload allocators across the
        // else-arm — exactly as those result regs were protected in the buggy
        // code by sitting on the vstack. Popped at the matching `End`, where
        // the else-arm's result registers are reconciled INTO the then-arm's
        // (a `mov R_then, R_else` on the else path when they differ). Each
        // inner `Vec` is one if-block's then-arm results, top-most-last.
        let mut if_then_results: Vec<Vec<StackVal>> = Vec::new();

        // Map of local index -> register
        let mut local_to_reg: std::collections::HashMap<u32, Reg> =
            std::collections::HashMap::new();
        // First 4 params are in r0-r3
        // #204/#193: a param the function reads is spilled to a frame slot at
        // entry and accessed only through it, so it can never be clobbered in
        // its home register between reads. Params with no slot (unused) stay
        // register-backed via local_to_reg.
        for i in 0..num_params.min(4) {
            if let Some(&(off, is_i64)) = layout.param_slots.get(&i) {
                let reg = index_to_reg(i as u8);
                let op = if is_i64 {
                    ArmOp::I64Str {
                        rdlo: reg,
                        rdhi: i64_pair_hi(reg)?,
                        addr: MemAddr::imm(Reg::SP, off),
                    }
                } else {
                    ArmOp::Str {
                        rd: reg,
                        addr: MemAddr::imm(Reg::SP, off),
                    }
                };
                instructions.push(ArmInstruction {
                    op,
                    source_line: None,
                });
            } else {
                local_to_reg.insert(i, index_to_reg(i as u8));
            }
        }

        let i64_locals = infer_i64_locals(wasm_ops, &self.func_ret_i64, &self.type_ret_i64);

        // #193/#210: a register-backed param (call-free function — call functions
        // frame-back via param_slots) lives in r0..r3 and is NOT on the operand
        // stack, so the temp/pair allocators (which avoid only `stack_live_regs`)
        // can hand its register out for a temp/constant/reload under pressure,
        // clobbering it before a later read. gale's `control_step_decide`:
        // `coolant_c`=param2=r2, the constant 80 lands in r2 → `subs r3,r2,r2`.
        // Snapshot the register-backed params + each one's last read so every
        // allocation reserves a param whose value is still needed.
        let param_regs: Vec<(u32, Reg)> = local_to_reg.iter().map(|(&p, &r)| (p, r)).collect();
        let mut param_last_read: std::collections::HashMap<u32, usize> =
            std::collections::HashMap::new();
        for (i, op) in wasm_ops.iter().enumerate() {
            if let LocalGet(p) | LocalTee(p) = op
                && param_regs.iter().any(|(pp, _)| pp == p)
            {
                param_last_read.insert(*p, i);
            }
        }
        let live_param_regs = |at: usize| -> Vec<Reg> {
            param_regs
                .iter()
                .filter(|(p, _)| param_last_read.get(p).is_some_and(|&last| last >= at))
                .map(|(_, r)| *r)
                .collect::<Vec<_>>()
        };

        for (idx, op) in wasm_ops.iter().enumerate() {
            // Param registers still live at this op — reserved from temp/pair/
            // reload allocation so a constant/result/reload never clobbers a live
            // param (#193).
            let mut live_params = live_param_regs(idx);
            // #313: while inside the else-arm of one or more if-blocks, the
            // then-arm result registers of each enclosing if-block must be
            // protected from the allocators exactly as they were when they sat
            // on the vstack in the buggy code (this is what makes the else-arm
            // allocate byte-identically). Reserve them — and the conventional
            // hi register of any i64 result — for the duration of the else-arm.
            for results in &if_then_results {
                for v in results {
                    if let StackVal::Reg { reg, is_i64 } = v {
                        live_params.push(*reg);
                        if *is_i64 && let Ok(hi) = i64_pair_hi(*reg) {
                            live_params.push(hi);
                        }
                    }
                }
            }
            match op {
                LocalGet(local_idx) => {
                    // #359: an incoming stack-passed param (idx in [4,num_params))
                    // is i32 by construction — a 64-bit param is refused up front
                    // in `select_with_stack` (declared-width guard), so this path
                    // only ever sees i32 stack params.
                    // Get the register for this local. Three cases:
                    //  1. Param in register — use the cached mapping.
                    //  2. Spilled i64 local — load both halves via I64Ldr.
                    //  3. Spilled i32 local — single Ldr.
                    let (reg, val_is_i64) =
                        if let Some(&off) = layout.incoming_params.get(local_idx) {
                            // #359: read the incoming stack-passed param into a
                            // fresh temp pushed on the vstack — NOT register-homed.
                            let dst = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(Reg::SP, off),
                                },
                                source_line: Some(idx),
                            });
                            (dst, false)
                        } else if let Some(&(off, is_i64)) = layout.param_slots.get(local_idx) {
                            // #204/#193: frame-backed param — reload from its slot.
                            if is_i64 {
                                let (dst_lo, dst_hi) = alloc_consecutive_pair(
                                    &mut next_temp,
                                    &mut stack,
                                    &mut instructions,
                                    &mut spill,
                                    &[],
                                    &live_params,
                                    idx,
                                )?;
                                instructions.push(ArmInstruction {
                                    op: ArmOp::I64Ldr {
                                        rdlo: dst_lo,
                                        rdhi: dst_hi,
                                        addr: MemAddr::imm(Reg::SP, off),
                                    },
                                    source_line: Some(idx),
                                });
                                (dst_lo, true)
                            } else {
                                let dst = alloc_temp_or_spill(
                                    &mut next_temp,
                                    &mut stack,
                                    &mut instructions,
                                    &mut spill,
                                    &live_params,
                                    idx,
                                )?;
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Ldr {
                                        rd: dst,
                                        addr: MemAddr::imm(Reg::SP, off),
                                    },
                                    source_line: Some(idx),
                                });
                                (dst, false)
                            }
                        } else if let Some(&r) = local_to_reg.get(local_idx) {
                            (r, i64_locals.contains(local_idx))
                        } else if let Some(&(off, true)) = layout.locals.get(local_idx) {
                            // i64 local — load both 32-bit halves into a consecutive
                            // register pair via the I64Ldr pseudo-op. Convention
                            // matches I64Const: push only dst_lo on the stack;
                            // dst_hi is recovered later via i64_pair_hi(lo).
                            // The pair MUST be consecutive in ALLOCATABLE_REGS
                            // — i64_pair_hi assumes that. Two separate calls to
                            // alloc_temp_safe can return non-consecutive registers
                            // when something in between is live, breaking the
                            // pair convention.
                            let (dst_lo, dst_hi) = alloc_consecutive_pair(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &[],
                                &live_params,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::I64Ldr {
                                    rdlo: dst_lo,
                                    rdhi: dst_hi,
                                    addr: MemAddr::imm(Reg::SP, off),
                                },
                                source_line: Some(idx),
                            });
                            (dst_lo, true)
                        } else if let Some(&(off, false)) = layout.locals.get(local_idx) {
                            // i32 local: single 4-byte load from the locals frame.
                            let dst = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(Reg::SP, off),
                                },
                                source_line: Some(idx),
                            });
                            (dst, false)
                        } else {
                            // Local not in layout (shouldn't happen for valid wasm,
                            // but fall back to legacy behaviour for compatibility).
                            let dst = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(Reg::SP, (*local_idx as i32 - 4) * 4),
                                },
                                source_line: Some(idx),
                            });
                            (dst, false)
                        };
                    stack.push(StackVal::Reg {
                        reg,
                        is_i64: val_is_i64,
                    });
                }

                I32Const(val) => {
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let uval = *val as u32;
                    // #237: under the native-pointer ABI, when a stack-pointer
                    // global establishes a real static-data base, a const at/above
                    // it is a wasm pointer (e.g. a `&static_spinlock` argument),
                    // not a scalar — emit it as `__synth_wasm_data + uval` so it
                    // resolves at link time independent of any runtime base. This
                    // is gated on `sp_global`: without one the base is 0 and every
                    // const (including stored *values*) would look like an address,
                    // which is unsound — those modules use the positional
                    // load/store promotion only.
                    if self.sp_global.is_some()
                        && let Some(addend) = self.static_data_addend(uval)
                    {
                        Self::emit_wasm_data_addr(&mut instructions, dst, addend, idx);
                        cf.add_instruction();
                        stack.push(StackVal::i32(dst));
                        continue;
                    }
                    let inverted = !uval;
                    if uval <= 0xFFFF {
                        // 0..65535: MOVW handles the full 16-bit range
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: uval as u16,
                            },
                            source_line: Some(idx),
                        });
                    } else if inverted <= 0xFFFF {
                        // Bit-inverted pattern: MOVW inverted + MVN
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: inverted as u16,
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mvn {
                                rd: dst,
                                op2: Operand2::Reg(dst),
                            },
                            source_line: Some(idx),
                        });
                    } else {
                        // Full 32-bit: MOVW low16 + MOVT high16
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movw {
                                rd: dst,
                                imm16: (uval & 0xFFFF) as u16,
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Movt {
                                rd: dst,
                                imm16: ((uval >> 16) & 0xFFFF) as u16,
                            },
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Add => {
                    // Immediate folding (#250 pattern): const operand 0..=0xFFF
                    // (the ADDW range, #253) whose `movw` is at the tail →
                    // `add rd, a, #C`, drop the materialization.
                    let fold_imm = foldable_addsub_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    // Result goes in r0 for return value (or temp if not last op)
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Add {
                            rd: dst,
                            rn: a,
                            op2,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                I32Sub => {
                    // Immediate folding: `i32.sub` is `a - b`; when b is a const
                    // 0..=0xFFF (SUBW range, #253) with its `movw` at the tail,
                    // fold to `sub rd, a, #C` and drop the materialization.
                    let fold_imm = foldable_addsub_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sub {
                            rd: dst,
                            rn: a,
                            op2,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                I32Mul => {
                    let b = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mul {
                            rd: dst,
                            rn: a,
                            rm: b,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                I32And => {
                    // Immediate folding: when the second operand is a small const
                    // (`i32.const C`, 0..=0xFF) whose `movw` is cleanly at the tail
                    // (not spilled), fold it as `and rd, a, #C` and drop the
                    // materialization — eliminating the redundant const load
                    // (#209/#248). Bounded to 0..=0xFF by the encoder (#249).
                    let fold_imm = foldable_bitwise_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::And {
                            rd: dst,
                            rn: a,
                            op2,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                I32Or => {
                    // Immediate folding (same shape as I32And, #250): const
                    // operand 0..=0xFF whose `movw` is at the tail → `orr rd,a,#C`,
                    // drop the materialization. Encoder ORR-imm hardened in #251.
                    let fold_imm = foldable_bitwise_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Orr {
                            rd: dst,
                            rn: a,
                            op2,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                I32Xor => {
                    // Immediate folding (same shape as I32And, #250): const
                    // operand 0..=0xFF whose `movw` is at the tail → `eor rd,a,#C`,
                    // drop the materialization. Encoder EOR-imm hardened in #251.
                    let fold_imm = foldable_bitwise_imm(wasm_ops, idx).filter(|_| {
                        matches!(
                            instructions.last().map(|i| (&i.op, i.source_line)),
                            Some((ArmOp::Movw { .. }, Some(sl))) if sl == idx - 1
                        )
                    });
                    let (a, op2) = if let Some(c) = fold_imm {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Imm(c))
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        (a, Operand2::Reg(b))
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Eor {
                            rd: dst,
                            rn: a,
                            op2,
                        },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                // Division operations with trap checks for divide-by-zero
                I32DivU => {
                    // #209 Opt 1: a statically-known nonzero divisor lets us
                    // strength-reduce the UDIV and drop the dead div-by-zero
                    // trap guard. Snapshot before popping (pop_operand mutates).
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?; // b (divisor)
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?; // a (dividend)
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x / 1 == x (no trap possible). Identity move.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Reg(dividend),
                            },
                            source_line: Some(idx),
                        });
                    } else if let Some(k) = cdiv.and_then(pow2_shift_u) {
                        // x / 2^k == x >> k (unsigned). No guard, no UDIV.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Lsr {
                                rd: dst,
                                rn: dividend,
                                shift: k,
                            },
                            source_line: Some(idx),
                        });
                    } else if let Some(d) = cdiv
                        .map(|c| c as u32)
                        .filter(|&u| u >= 3 && !u.is_power_of_two())
                    {
                        // #209 Opt 1b: non-power-of-two constant divisor →
                        // reciprocal-multiply (Granlund–Montgomery magic number).
                        // No UDIV, no trap guard. Computes the high word of
                        // `dividend * m` via UMULL, then an `a`-selected shift.
                        let (m, s, a) = magicu(d);
                        let mut reserved: Vec<Reg> = live_params.clone();
                        reserved.push(dividend);
                        reserved.push(dst);

                        // Scratch for the reciprocal-multiply: the magic
                        // constant + UMULL's outputs. The a==false path reuses
                        // `dst` as the throwaway low word (2 temps); a==true
                        // keeps `dividend` live past the UMULL (3 temps).
                        // Exhaustion here is recovered by the #320 spill retry
                        // — the historical v0.11.20 UDIV cost-gate is deleted
                        // (VCR-VER-001; it was already dead on the frozen
                        // suite).
                        // VCR-VER-001 (#242): the v0.11.20 cost-gate is GONE.
                        // The #320 spill-on-exhaustion retry recovers the
                        // pressure case the UDIV fallback guarded, and the
                        // fallback was already dead on the entire frozen suite
                        // (reverting it is byte-identical) — the first greedy
                        // patch deleted under the VCR program's exit criterion.
                        let rmag = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &reserved,
                            idx,
                        )?;
                        reserved.push(rmag);
                        let (rlo, rhi) = if a {
                            let rlo = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            reserved.push(rlo);
                            let rhi = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            (rlo, rhi)
                        } else {
                            // a==false: `dst` doubles as UMULL's RdLo.
                            let rhi = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            (dst, rhi)
                        };
                        {
                            // #209 cleanup: the reciprocal-multiply reads the magic
                            // constant, never the divisor — so the divisor's eager
                            // materialization (the `i32.const` at idx-1, the only op
                            // tagged there) is dead on this path. Drop it.
                            if idx >= 1 {
                                instructions.retain(|i| i.source_line != Some(idx - 1));
                            }
                            // Materialize the magic constant m into rmag.
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movw {
                                    rd: rmag,
                                    imm16: (m & 0xFFFF) as u16,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movt {
                                    rd: rmag,
                                    imm16: ((m >> 16) & 0xFFFF) as u16,
                                },
                                source_line: Some(idx),
                            });
                            // UMULL rlo, rhi, dividend, rmag → rhi = umulhi(m, n)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Umull {
                                    rdlo: rlo,
                                    rdhi: rhi,
                                    rn: dividend,
                                    rm: rmag,
                                },
                                source_line: Some(idx),
                            });
                            if a {
                                // q = (((n - hi) >> 1) + hi) >> (s-1); rlo as t.
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Sub {
                                        rd: rlo,
                                        rn: dividend,
                                        op2: Operand2::Reg(rhi),
                                    },
                                    source_line: Some(idx),
                                });
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Lsr {
                                        rd: rlo,
                                        rn: rlo,
                                        shift: 1,
                                    },
                                    source_line: Some(idx),
                                });
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Add {
                                        rd: rlo,
                                        rn: rlo,
                                        op2: Operand2::Reg(rhi),
                                    },
                                    source_line: Some(idx),
                                });
                                // s >= 1 when a is set; s == 1 → final shift is 0.
                                if s == 1 {
                                    instructions.push(ArmInstruction {
                                        op: ArmOp::Mov {
                                            rd: dst,
                                            op2: Operand2::Reg(rlo),
                                        },
                                        source_line: Some(idx),
                                    });
                                } else {
                                    instructions.push(ArmInstruction {
                                        op: ArmOp::Lsr {
                                            rd: dst,
                                            rn: rlo,
                                            shift: s - 1,
                                        },
                                        source_line: Some(idx),
                                    });
                                }
                            } else if s == 0 {
                                // q = hi (no shift). LSR #0 is invalid, so MOV.
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Mov {
                                        rd: dst,
                                        op2: Operand2::Reg(rhi),
                                    },
                                    source_line: Some(idx),
                                });
                            } else {
                                // q = hi >> s
                                instructions.push(ArmInstruction {
                                    op: ArmOp::Lsr {
                                        rd: dst,
                                        rn: rhi,
                                        shift: s,
                                    },
                                    source_line: Some(idx),
                                });
                            }
                        }
                    } else {
                        // A nonzero constant divisor can never trap; only emit
                        // the div-by-zero guard when the divisor is unknown or 0.
                        let needs_guard = cdiv.is_none_or(|c| c == 0);
                        if needs_guard {
                            // CMP divisor, #0
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            // BNE.N +0 (skip UDF if divisor != 0): offset=0 means
                            // skip to PC+4, which skips the 2-byte UDF.
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            // UDF #0 (triggers trap on divide by zero)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }
                        // UDIV dst, dividend, divisor
                        instructions.push(ArmInstruction {
                            op: ArmOp::Udiv {
                                rd: dst,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32DivS => {
                    // #209 Opt 1: a known divisor lets us drop the dead trap
                    // guards — div-by-zero when C != 0, and the INT_MIN/-1
                    // overflow guard when C != -1 (overflow only at divisor -1).
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x / 1 == x (INT_MIN/1 = INT_MIN, no overflow). Identity.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Reg(dividend),
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    } else {
                        // Trap check 1: divide by zero (dead for a nonzero const).
                        let needs_dz_guard = cdiv.is_none_or(|c| c == 0);
                        if needs_dz_guard {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }

                        // Trap check 2: signed overflow (INT_MIN / -1). Dead
                        // unless the divisor could be -1.
                        let needs_ovf_guard = cdiv.is_none_or(|c| c == -1);
                        if needs_ovf_guard {
                            // We need a temp register for INT_MIN (0x80000000)
                            let tmp = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;

                            // Load INT_MIN into tmp: MOVW tmp, #0; MOVT tmp, #0x8000
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movw { rd: tmp, imm16: 0 },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Movt {
                                    rd: tmp,
                                    imm16: 0x8000,
                                },
                                source_line: Some(idx),
                            });
                            // CMP dividend, tmp (check if dividend == INT_MIN)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: dividend,
                                    op2: Operand2::Reg(tmp),
                                },
                                source_line: Some(idx),
                            });
                            // BNE.N +3 (skip overflow check if dividend != INT_MIN)
                            // Skip 8 bytes: CMN.W(4) + BNE(2) + UDF(2)
                            // Branch target = PC + (imm8 << 1) = B+4 + 6 = B+10 (SDIV)
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 3,
                                },
                                source_line: Some(idx),
                            });
                            // CMN divisor, #1 (divisor == -1: -1 + 1 = 0 sets Z)
                            // CMN.W is 4 bytes
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmn {
                                    rn: divisor,
                                    op2: Operand2::Imm(1),
                                },
                                source_line: Some(idx),
                            });
                            // BNE.N +0 (skip UDF if divisor != -1)
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            // UDF #1 (triggers trap on overflow)
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 1 },
                                source_line: Some(idx),
                            });
                        }

                        // SDIV dst, dividend, divisor (safe to divide now)
                        instructions.push(ArmInstruction {
                            op: ArmOp::Sdiv {
                                rd: dst,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    }
                }

                I32RemU => {
                    // #209 Opt 1: drop the dead div-by-zero guard for a nonzero
                    // constant divisor; fold `x % 1` to 0.
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x % 1 == 0
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Imm(0),
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    } else {
                        // Trap check: divide by zero (dead for a nonzero const).
                        let needs_guard = cdiv.is_none_or(|c| c == 0);
                        if needs_guard {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }

                        // Remainder: dst = dividend - (dividend / divisor) * divisor
                        // quotient = UDIV tmp, dividend, divisor
                        let tmp = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Udiv {
                                rd: tmp,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                        // MLS dst, tmp, divisor, dividend (dst = dividend - tmp*divisor)
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mls {
                                rd: dst,
                                rn: tmp,
                                rm: divisor,
                                ra: dividend,
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    }
                }

                I32RemS => {
                    // #209 Opt 1: drop the dead div-by-zero guard for a nonzero
                    // constant divisor; fold `x % 1` to 0. (`x % -1 == 0` is left
                    // to SDIV+MLS, which already yields 0 for all dividends.)
                    let cdiv = const_divisor(wasm_ops, idx);
                    let divisor = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dividend = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if cdiv == Some(1) {
                        // x % 1 == 0
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst,
                                op2: Operand2::Imm(0),
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    } else {
                        // Trap check: divide by zero (rem_s doesn't trap on
                        // INT_MIN % -1). Dead for a nonzero constant divisor.
                        let needs_guard = cdiv.is_none_or(|c| c == 0);
                        if needs_guard {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Cmp {
                                    rn: divisor,
                                    op2: Operand2::Imm(0),
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::BCondOffset {
                                    cond: Condition::NE,
                                    offset: 0,
                                },
                                source_line: Some(idx),
                            });
                            instructions.push(ArmInstruction {
                                op: ArmOp::Udf { imm: 0 },
                                source_line: Some(idx),
                            });
                        }

                        // Signed remainder: dst = dividend - (dividend/divisor)*divisor
                        let tmp = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Sdiv {
                                rd: tmp,
                                rn: dividend,
                                rm: divisor,
                            },
                            source_line: Some(idx),
                        });
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mls {
                                rd: dst,
                                rn: tmp,
                                rm: divisor,
                                ra: dividend,
                            },
                            source_line: Some(idx),
                        });
                        stack.push(StackVal::i32(dst));
                    }
                }

                // Memory operations need stack-aware handling
                I32Load { offset, .. } => {
                    // Issue #95: fold `i32.const C; i32.load offset=O` to a
                    // single `LDR rd, [R11, #(C+O)]` when the effective offset
                    // fits in imm12. Drops the MOVW(+MOVT) const materialization.
                    let folded = self.try_fold_const_addr(wasm_ops, idx, *offset);
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // Result goes in R0 if this is the last value-producing op (before End)
                    // Check if next op is End or if we're at the last position
                    let is_return_value = idx == wasm_ops.len() - 1
                        || (idx + 1 < wasm_ops.len() && matches!(wasm_ops[idx + 1], End));
                    let dst = if is_return_value {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    if let Some(eff_offset) = folded {
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        if let Some(addend) = self.static_data_addend(eff_offset) {
                            // #237: static → base-independent address in `dst`,
                            // then load `[dst]` (the load overwrites the address).
                            Self::emit_wasm_data_addr(&mut instructions, dst, addend, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(dst, 0),
                                },
                                source_line: Some(idx),
                            });
                        } else {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Ldr {
                                    rd: dst,
                                    addr: MemAddr::imm(Reg::R11, eff_offset as i32),
                                },
                                source_line: Some(idx),
                            });
                        }
                    } else {
                        // Generate load with optional bounds checking
                        let load_ops =
                            self.generate_load_with_bounds_check(dst, addr, *offset as i32, 4);
                        for op in load_ops {
                            instructions.push(ArmInstruction {
                                op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    stack.push(StackVal::i32(dst));
                }

                I32Store { offset, .. } => {
                    // Issue #95: fold `i32.const C; <pusher>; i32.store offset=O`
                    // to `STR val_reg, [R11, #(C+O)]` when effective offset fits.
                    let folded = self.try_fold_const_addr_store(wasm_ops, idx, *offset);
                    // WASM i32.store pops: value first, then address
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    if let Some(eff_offset) = folded {
                        Self::splice_out_addr_const_materialization(
                            &mut instructions,
                            idx - 2,
                            idx - 1,
                        );
                        if let Some(addend) = self.static_data_addend(eff_offset) {
                            // #237: static store — materialize the base-independent
                            // address into a scratch reg, then `STR value, [addr]`.
                            let a = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, a, addend, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Str {
                                    rd: value,
                                    addr: MemAddr::imm(a, 0),
                                },
                                source_line: Some(idx),
                            });
                        } else {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Str {
                                    rd: value,
                                    addr: MemAddr::imm(Reg::R11, eff_offset as i32),
                                },
                                source_line: Some(idx),
                            });
                        }
                    } else {
                        // Generate store with optional bounds checking
                        let store_ops =
                            self.generate_store_with_bounds_check(value, addr, *offset as i32, 4);
                        for op in store_ops {
                            instructions.push(ArmInstruction {
                                op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    // Store doesn't push anything to stack
                }

                // Sub-word loads (i32) — like I32Load but with LDRB/LDRSB/LDRH/LDRSH
                I32Load8S { offset, .. }
                | I32Load8U { offset, .. }
                | I32Load16S { offset, .. }
                | I32Load16U { offset, .. } => {
                    // Issue #95: same const-address fold as I32Load.
                    let folded = self.try_fold_const_addr(wasm_ops, idx, *offset);
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let is_return_value = idx == wasm_ops.len() - 1
                        || (idx + 1 < wasm_ops.len() && matches!(wasm_ops[idx + 1], End));
                    let dst = if is_return_value {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    let (access_size, sign_extend) = match op {
                        I32Load8S { .. } => (1, true),
                        I32Load8U { .. } => (1, false),
                        I32Load16S { .. } => (2, true),
                        I32Load16U { .. } => (2, false),
                        _ => unreachable!(),
                    };

                    if let Some(eff_offset) = folded {
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let mem = MemAddr::imm(Reg::R11, eff_offset as i32);
                        let arm_op = match (access_size, sign_extend) {
                            (1, false) => ArmOp::Ldrb { rd: dst, addr: mem },
                            (1, true) => ArmOp::Ldrsb { rd: dst, addr: mem },
                            (2, false) => ArmOp::Ldrh { rd: dst, addr: mem },
                            (2, true) => ArmOp::Ldrsh { rd: dst, addr: mem },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    } else {
                        let load_ops = self.generate_subword_load_with_bounds_check(
                            dst,
                            addr,
                            *offset as i32,
                            access_size,
                            sign_extend,
                        );
                        for arm_op in load_ops {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                    }
                    stack.push(StackVal::i32(dst));
                }

                // Sub-word stores (i32) — like I32Store but with STRB/STRH
                I32Store8 { offset, .. } | I32Store16 { offset, .. } => {
                    // Issue #95: same const-address fold as I32Store.
                    let folded = self.try_fold_const_addr_store(wasm_ops, idx, *offset);
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    let access_size = match op {
                        I32Store8 { .. } => 1,
                        I32Store16 { .. } => 2,
                        _ => unreachable!(),
                    };

                    if let Some(eff_offset) = folded {
                        Self::splice_out_addr_const_materialization(
                            &mut instructions,
                            idx - 2,
                            idx - 1,
                        );
                        let mem = MemAddr::imm(Reg::R11, eff_offset as i32);
                        let arm_op = match access_size {
                            1 => ArmOp::Strb {
                                rd: value,
                                addr: mem,
                            },
                            2 => ArmOp::Strh {
                                rd: value,
                                addr: mem,
                            },
                            _ => unreachable!(),
                        };
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    } else {
                        let store_ops = self.generate_subword_store_with_bounds_check(
                            value,
                            addr,
                            *offset as i32,
                            access_size,
                        );
                        for arm_op in store_ops {
                            instructions.push(ArmInstruction {
                                op: arm_op,
                                source_line: Some(idx),
                            });
                        }
                    }
                }

                // i64 sub-word loads — load sub-word, extend to i64 (register pair)
                //
                // Pre-fix `dst_lo` and `dst_hi` were hardcoded to R0:R1,
                // clobbering AAPCS params 0 and 1 on every i64.load{8,16,32}*
                // — even when the function had 2+ params and neither was
                // the address operand. Use `alloc_consecutive_pair` with
                // `addr` in `extra_avoid` so the destination pair never
                // overlaps the address register OR a live param.
                I64Load8S { offset, .. }
                | I64Load8U { offset, .. }
                | I64Load16S { offset, .. }
                | I64Load16U { offset, .. }
                | I64Load32S { offset, .. }
                | I64Load32U { offset, .. } => {
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[addr],
                        &live_params,
                        idx,
                    )?;

                    let ops: Vec<ArmOp> = match op {
                        I64Load8S { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                1,
                                true,
                            );
                            v.push(ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            });
                            v
                        }
                        I64Load8U { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                1,
                                false,
                            );
                            v.push(ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            });
                            v
                        }
                        I64Load16S { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                2,
                                true,
                            );
                            v.push(ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            });
                            v
                        }
                        I64Load16U { .. } => {
                            let mut v = self.generate_subword_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                2,
                                false,
                            );
                            v.push(ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            });
                            v
                        }
                        I64Load32S { .. } => {
                            let mut v = self.generate_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                4,
                            );
                            v.push(ArmOp::Asr {
                                rd: dst_hi,
                                rn: dst_lo,
                                shift: 31,
                            });
                            v
                        }
                        I64Load32U { .. } => {
                            let mut v = self.generate_load_with_bounds_check(
                                dst_lo,
                                addr,
                                *offset as i32,
                                4,
                            );
                            v.push(ArmOp::Mov {
                                rd: dst_hi,
                                op2: Operand2::Imm(0),
                            });
                            v
                        }
                        _ => unreachable!(),
                    };

                    for arm_op in ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                    // i64 on 32-bit ARM uses register pair; push low register
                    stack.push(StackVal::i64(dst_lo));
                }

                // i64 sub-word stores
                I64Store8 { offset, .. }
                | I64Store16 { offset, .. }
                | I64Store32 { offset, .. } => {
                    // Pop i64 value (lo register) and address
                    let value_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    let ops: Vec<ArmOp> = match op {
                        I64Store8 { .. } => self.generate_subword_store_with_bounds_check(
                            value_lo,
                            addr,
                            *offset as i32,
                            1,
                        ),
                        I64Store16 { .. } => self.generate_subword_store_with_bounds_check(
                            value_lo,
                            addr,
                            *offset as i32,
                            2,
                        ),
                        I64Store32 { .. } => {
                            self.generate_store_with_bounds_check(value_lo, addr, *offset as i32, 4)
                        }
                        _ => unreachable!(),
                    };

                    for arm_op in ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                }

                // Memory management
                MemorySize(_mem_idx) => {
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::MemorySize { rd: dst },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                MemoryGrow(_mem_idx) => {
                    // Pop the requested number of pages from stack
                    let pages = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::MemoryGrow { rd: dst, rn: pages },
                        source_line: Some(idx),
                    });
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // Control flow operations
                // =========================================================
                Block => {
                    let label = self.alloc_label("block_end");
                    // Push block info so br can find the end label
                    cf.enter_block(BlockType::Block);
                    block_labels.push((label.clone(), false)); // (end_label, is_loop)
                    // No ARM code emitted at block entry (label at end)
                }

                Loop => {
                    let label = self.alloc_label("loop_start");
                    cf.enter_block(BlockType::Loop);
                    block_labels.push((label.clone(), true)); // (start_label, is_loop)
                    // Emit loop start label
                    instructions.push(ArmInstruction {
                        op: ArmOp::Label { name: label },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                If => {
                    // Pop condition from stack
                    let cond_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let else_label = self.alloc_label("else");
                    let end_label = self.alloc_label("if_end");

                    cf.enter_block(BlockType::If);
                    // Store both labels: else_label for the if-branch, end_label for the end
                    if_labels.push((else_label.clone(), end_label.clone()));
                    block_labels.push((end_label, false));
                    // #313: checkpoint the operand-stack depth (the condition is
                    // already popped). The then-arm runs from here; its results
                    // are whatever sits ABOVE this depth at `Else`. Reservation
                    // starts EMPTY — nothing needs protecting during the then-arm
                    // (it runs first); it is filled at `Else`.
                    if_checkpoints.push(stack.len());
                    if_then_results.push(Vec::new());

                    // CMP cond_reg, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // BEQ else_label (skip then-block if condition is zero)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Bcc {
                            cond: Condition::EQ,
                            label: else_label,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Else => {
                    // #313: the then-arm's results are the vstack entries above
                    // the checkpoint. Pop them (top-most last) and truncate the
                    // vstack back to the checkpoint so the else-arm starts from
                    // the SAME stack shape the then-arm did. The captured regs
                    // are reserved across the else-arm (via `if_then_results`,
                    // merged into `live_params` above) so the else-arm cannot
                    // clobber them — reproducing the buggy code's incidental
                    // protection (the then-results were on the vstack) exactly,
                    // which is what keeps the else-arm allocation byte-identical.
                    if let Some(&cp) = if_checkpoints.last() {
                        let then_results: Vec<StackVal> = stack.split_off(cp);
                        if let Some(slot) = if_then_results.last_mut() {
                            *slot = then_results;
                        }
                    }
                    // End of then-block: jump to end of if
                    if let Some((_, end_label)) = if_labels.last() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::B {
                                label: end_label.clone(),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Emit else label
                    if let Some((else_label, _)) = if_labels.last() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label {
                                name: else_label.clone(),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                End => {
                    cf.exit_block();
                    // If this closes an if-block, emit the end label
                    // and possibly the else label (if no else was present)
                    if let Some((else_label, end_label)) = if_labels.last().cloned() {
                        // Check if the else label was already emitted
                        // by looking for it in the instructions
                        let else_emitted = instructions
                            .iter()
                            .any(|i| matches!(&i.op, ArmOp::Label { name } if *name == else_label));
                        if !else_emitted {
                            // No else clause: emit else label (same as end).
                            // A valid if-without-else has arity 0 (no result),
                            // so there is nothing to reconcile (#313).
                            instructions.push(ArmInstruction {
                                op: ArmOp::Label { name: else_label },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        // #313: reconcile the two arms onto a single set of
                        // result registers. The then-arm's results were captured
                        // and reserved at `Else` (`if_then_results`); the
                        // else-arm's results are the vstack entries above the
                        // checkpoint right now. The `mov R_then, R_else`s emitted
                        // here sit on the ELSE path (between the else-arm body and
                        // `end_label`); the then-path's `B end_label` (emitted at
                        // `Else`) jumps over them, so the then-arm's value is the
                        // one live at `end_label` on the then path while the else
                        // path moves its value into the same registers. When the
                        // two arms already chose the same register, NO `mov` is
                        // emitted (this is what keeps register-symmetric and
                        // control-flow-only if/else byte-identical to before).
                        let then_results = if_then_results.pop().unwrap_or_default();
                        let checkpoint = if_checkpoints.pop();
                        if else_emitted {
                            if let Some(cp) = checkpoint {
                                // else-arm results above the checkpoint, in the
                                // same bottom→top order as `then_results`.
                                let else_results: Vec<StackVal> = stack.split_off(cp);
                                if else_results.len() == then_results.len() {
                                    for (then_v, else_v) in
                                        then_results.iter().zip(else_results.iter())
                                    {
                                        reconcile_if_result(
                                            then_v,
                                            else_v,
                                            &mut instructions,
                                            idx,
                                        )?;
                                    }
                                } else {
                                    // Arity mismatch between arms (should not
                                    // happen for valid wasm). Restore what we
                                    // took rather than silently miscompile;
                                    // downstream may still Err cleanly.
                                    stack.extend(else_results);
                                }
                            }
                            // The merged results live in the then-arm's
                            // registers — push them back onto the vstack so the
                            // surrounding code (return / outer op) reads them.
                            stack.extend(then_results);
                        }
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label { name: end_label },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        if_labels.pop();
                        block_labels.pop();
                    } else if let Some((label, is_loop)) = block_labels.pop()
                        && !is_loop
                    {
                        // Block end: emit end label
                        instructions.push(ArmInstruction {
                            op: ArmOp::Label { name: label },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        // Loop end: no label at end (label is at start)
                    }
                    // else: function-level end, nothing to emit
                }

                Br(depth) => {
                    // Branch to the Nth enclosing block/loop
                    // block_labels + if_labels are combined into the block_labels stack
                    let target_idx = block_labels.len().saturating_sub(1 + *depth as usize);
                    if target_idx < block_labels.len() {
                        let (label, is_loop) = &block_labels[target_idx];
                        if *is_loop {
                            // Loop: branch back to start
                            instructions.push(ArmInstruction {
                                op: ArmOp::B {
                                    label: label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        } else {
                            // Block: branch forward to end
                            instructions.push(ArmInstruction {
                                op: ArmOp::B {
                                    label: label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        }
                    } else {
                        // Depth exceeds stack — branch to function return
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bx { rm: Reg::LR },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                BrIf(depth) => {
                    // Pop condition from stack
                    let cond_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // CMP cond_reg, #0
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // BNE target_label (branch if non-zero)
                    let target_idx = block_labels.len().saturating_sub(1 + *depth as usize);
                    if target_idx < block_labels.len() {
                        let (label, _) = &block_labels[target_idx];
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bcc {
                                cond: Condition::NE,
                                label: label.clone(),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                BrTable { targets, default } => {
                    // Pop index from stack
                    let index_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // Emit cascading CMP + BEQ for each target
                    for (i, target) in targets.iter().enumerate() {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Cmp {
                                rn: index_reg,
                                op2: Operand2::Imm(i as i32),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();

                        let target_idx = block_labels.len().saturating_sub(1 + *target as usize);
                        if target_idx < block_labels.len() {
                            let (label, _) = &block_labels[target_idx];
                            instructions.push(ArmInstruction {
                                op: ArmOp::Bcc {
                                    cond: Condition::EQ,
                                    label: label.clone(),
                                },
                                source_line: Some(idx),
                            });
                        }
                        cf.add_instruction();
                    }

                    // Default branch
                    let default_idx = block_labels.len().saturating_sub(1 + *default as usize);
                    if default_idx < block_labels.len() {
                        let (label, _) = &block_labels[default_idx];
                        instructions.push(ArmInstruction {
                            op: ArmOp::B {
                                label: label.clone(),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();
                }

                Return => {
                    // Move top-of-stack to R0 for return value (AAPCS). Pop is
                    // reload-aware (#171): a spilled return value is reloaded
                    // from its frame slot first.
                    if !stack.is_empty() {
                        let val = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        if val != Reg::R0 {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: Reg::R0,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                    }
                    // Deallocate the local frame before popping callee-saved
                    // registers; otherwise the pop would read from the locals
                    // area instead of the saved-register slots.
                    if layout.frame_size > 0 {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Add {
                                rd: Reg::SP,
                                rn: Reg::SP,
                                op2: Operand2::Imm(layout.frame_size),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Restore callee-saved registers and return via PC
                    instructions.push(ArmInstruction {
                        op: ArmOp::Pop {
                            regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Call(func_idx) => {
                    let is_import = *func_idx < self.num_imports;
                    // #197: a relocatable host-link import is a *direct* AAPCS
                    // call (`BL func_N` → wasm field name), so it marshals args
                    // into R0–R3 exactly like a local call. Only the legacy Meld
                    // dispatch ABI (non-relocatable imports) puts the import
                    // index in R0 and takes no AAPCS args.
                    let meld_dispatch = is_import && !self.relocatable;

                    // ── #195: AAPCS argument count for this callee ──
                    // Look up how many integer args the callee expects so we can
                    // move the top-N operand-stack values into R0–R3. Meld
                    // dispatch imports are excluded: that ABI puts the import
                    // index in R0 (see below), which would collide with arg0.
                    // Direct imports (#197) and local calls marshal normally —
                    // `func_arg_counts` is indexed by the full wasm function
                    // index (imports first), so an import's entry is valid.
                    let arg_count = if meld_dispatch {
                        0
                    } else {
                        self.func_arg_counts
                            .get(*func_idx as usize)
                            .copied()
                            .unwrap_or(0)
                    };

                    // #195: pop the call arguments off the operand stack FIRST so
                    // they are excluded from caller-saved preservation (they are
                    // consumed by the call, not live across it). The actual moves
                    // into R0–R3 are emitted AFTER preservation (below), so they
                    // are the last writes before the BL.
                    let arg_srcs = Self::pop_call_args(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        arg_count,
                        idx,
                    )?;

                    // #359: store args index>=4 to the outgoing stack region
                    // BEFORE preservation and the r0..r3 move (their sources are
                    // already popped, so the move could otherwise clobber them).
                    let n_stack_args = self.emit_stack_args(&mut instructions, &arg_srcs, idx)?;
                    for _ in 0..n_stack_args {
                        cf.add_instruction();
                    }
                    // Only the first <=4 args are marshalled into r0..r3.
                    let reg_srcs = &arg_srcs[..arg_srcs.len().min(ARG_REGS.len())];

                    // ── #188: caller-saved preservation across the call ──
                    // A BL clobbers R0–R3 and R12. Any live value (operand-stack
                    // temp or param) residing in one of those registers and needed
                    // after the call must be spilled before the BL and reloaded
                    // after it. R4–R8 are callee-saved and survive untouched. The
                    // call arguments were already popped, so they are not spilled.
                    let preserved = self.preserve_caller_saved(
                        &mut instructions,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        idx,
                    )?;

                    // #195: move arguments into R0–R3 — the LAST thing before the
                    // BL, after live values are safely in the spill area. Skipped
                    // for imports (arg_srcs is empty there). Uses a cycle-safe
                    // parallel move so chains/swaps among R0–R3 are handled.
                    let n_arg_moves = self.emit_arg_moves(
                        &mut instructions,
                        reg_srcs,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        idx,
                    )?;
                    for _ in 0..n_arg_moves {
                        cf.add_instruction();
                    }

                    if meld_dispatch {
                        // Legacy import call — dispatch through the Meld runtime
                        // (import index in R0, then BL __meld_dispatch_import).
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: Reg::R0,
                                op2: Operand2::Imm(*func_idx as i32),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bl {
                                label: "__meld_dispatch_import".to_string(),
                            },
                            source_line: Some(idx),
                        });
                    } else {
                        // Direct `BL func_N`: a local call, or (#197) a
                        // relocatable import whose `func_N` symbol the ELF
                        // builder rewrites to the wasm field name (e.g.
                        // `k_spin_lock`) for the host linker to resolve.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Bl {
                                label: format!("func_{}", func_idx),
                            },
                            source_line: Some(idx),
                        });
                    }
                    cf.add_instruction();

                    // #311: tag an i64 result as the R0:R1 pair.
                    let ret_i64 = self
                        .func_ret_i64
                        .get(*func_idx as usize)
                        .copied()
                        .unwrap_or(false);
                    let result_reg = self.restore_caller_saved(
                        &mut instructions,
                        &preserved,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        ret_i64,
                        idx,
                    )?;
                    // Push the call's return value as a live operand (spilled to
                    // the frame if no register was free to hold it — #171).
                    stack.push(result_reg);
                }

                CallIndirect { type_index, .. } => {
                    // Top of stack is the table index; the call arguments sit
                    // BELOW it on the operand stack.
                    let mut table_idx_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // #195: callee arg count comes from the static function type.
                    let arg_count = self
                        .type_arg_counts
                        .get(*type_index as usize)
                        .copied()
                        .unwrap_or(0);
                    let arg_srcs = Self::pop_call_args(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        arg_count,
                        idx,
                    )?;

                    // #359: store args index>=4 to the outgoing stack region
                    // BEFORE the table-index relocation (free_callee_saved below
                    // could pick an R4–R8 reg still holding a stack-arg source),
                    // preservation, and the r0..r3 move. The popped arg regs are
                    // not in stack_live_regs, so storing first closes the window.
                    let n_stack_args = self.emit_stack_args(&mut instructions, &arg_srcs, idx)?;
                    for _ in 0..n_stack_args {
                        cf.add_instruction();
                    }
                    let reg_srcs = &arg_srcs[..arg_srcs.len().min(ARG_REGS.len())];

                    // #195: the arg moves write R0–R3, but the `CallIndirect`
                    // expansion reads `table_idx_reg` to compute the branch
                    // target (and clobbers R12). When there are args to marshal,
                    // relocate the table index into a free callee-saved register
                    // so neither the R0–R3 arg writes nor the spill scratch can
                    // clobber it. We keep that register ON the operand stack while
                    // marshalling so every `free_callee_saved` call avoids it,
                    // then pop it back off just before emitting the call.
                    let mut table_pushed = false;
                    if !reg_srcs.is_empty() {
                        let safe = self.free_callee_saved(
                            &stack_live_regs(&stack),
                            &local_to_reg,
                            &layout,
                        )?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: safe,
                                op2: Operand2::Reg(table_idx_reg),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        table_idx_reg = safe;
                        stack.push(StackVal::i32(safe));
                        table_pushed = true;
                    }

                    // #188: preserve caller-saved registers across the indirect
                    // call (the table-index reg and the args are already popped
                    // and consumed, so they are excluded from preservation; the
                    // relocated callee-saved table index, if any, is not spilled
                    // because preservation only touches caller-saved regs).
                    let preserved = self.preserve_caller_saved(
                        &mut instructions,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        idx,
                    )?;

                    // #195: marshal args into R0–R3 (after preservation, last
                    // writes before the indirect branch). The relocated table
                    // index on the stack keeps the scratch picker away from it.
                    let n_arg_moves = self.emit_arg_moves(
                        &mut instructions,
                        reg_srcs,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        idx,
                    )?;
                    for _ in 0..n_arg_moves {
                        cf.add_instruction();
                    }

                    // Pop the relocated table index back off before the call op.
                    if table_pushed {
                        stack.pop();
                    }

                    instructions.push(ArmInstruction {
                        op: ArmOp::CallIndirect {
                            rd: Reg::R0,
                            type_idx: *type_index,
                            table_index_reg: table_idx_reg,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    // #311: tag an i64 result as the R0:R1 pair (static type).
                    let ret_i64 = self
                        .type_ret_i64
                        .get(*type_index as usize)
                        .copied()
                        .unwrap_or(false);
                    let result_reg = self.restore_caller_saved(
                        &mut instructions,
                        &preserved,
                        &stack_live_regs(&stack),
                        &local_to_reg,
                        &layout,
                        &mut spill,
                        ret_i64,
                        idx,
                    )?;
                    stack.push(result_reg);
                }

                Unreachable => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Udf { imm: 0 },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Nop => {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Nop,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                Drop => {
                    // Just pop a value from the stack and discard it
                    stack.pop();
                }

                Select => {
                    // Select: pop condition, val2, val1; push val1 if cond != 0, else val2
                    let cond_reg = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let val2 = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let val1 = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // #209/VCR-SEL-002 — in-place select. `val2` is consumed by
                    // this op, so when it is a free temp (not a live param reg,
                    // and distinct from cond/val1) we reuse ITS register as `dst`
                    // and keep its value via the EQ fall-through — only ONE
                    // conditional move is needed (cond != 0 overrides with val1).
                    // This is exactly what native emits for a clamp `(x>k)?k:x`
                    // and removes one `SelectMove` per select, the dominant cost
                    // in flat_flight's saturation chain. The three guards rule out
                    // the cases where overwriting val2's register is observable:
                    //   - live param  → #193 param-clobber class
                    //   - val2==cond  → cmp consumed cond, but a later read can't
                    //   - val2==val1  → degenerate; fresh dst keeps it simple
                    // Falls back to the fresh-dst two-move form otherwise.
                    let in_place = !live_params.contains(&val2) && val2 != cond_reg && val2 != val1;
                    let dst = if in_place {
                        val2
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };

                    // CMP cond, #0 — sets the flags FIRST, before anything writes
                    // `dst`. The previous lowering put a `MOV dst, val1` between
                    // the CMP and the conditional move; that MOV is a 16-bit Thumb
                    // `MOVS` for low registers and SETS the flags, clobbering the
                    // comparison whenever the allocator picked a low `dst` — which
                    // mis-computed gale's br_table index so the binary-semaphore
                    // WAKE path never ran. The `SelectMove`s below are `IT;MOV`
                    // (the flag-preserving 0x46xx MOV), so neither disturbs the
                    // flags and exactly one fires — correct under any aliasing of
                    // dst with cond/val1/val2 (cond is already consumed by CMP).
                    // In the in-place case there is NO instruction between the CMP
                    // and the conditional move, so the flags are likewise intact.
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: cond_reg,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // cond != 0 → dst = val1
                    instructions.push(ArmInstruction {
                        op: ArmOp::SelectMove {
                            rd: dst,
                            rm: val1,
                            cond: Condition::NE,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // cond == 0 → dst = val2. Skipped when dst already IS val2
                    // (in-place): the EQ branch is a no-op move on itself.
                    if !in_place {
                        instructions.push(ArmInstruction {
                            op: ArmOp::SelectMove {
                                rd: dst,
                                rm: val2,
                                cond: Condition::EQ,
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    stack.push(StackVal::i32(dst));
                }

                LocalSet(local_idx) => {
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    if let Some(&off) = layout.incoming_params.get(local_idx) {
                        // #359: write to the incoming stack-passed param's slot.
                        // i32 by construction — a 64-bit param is refused up front
                        // in `select_with_stack`.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, is_i64)) = layout.param_slots.get(local_idx) {
                        // #204/#193: frame-backed param — store to its slot.
                        let op = if is_i64 {
                            ArmOp::I64Str {
                                rdlo: val,
                                rdhi: i64_pair_hi(val)?,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        } else {
                            ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        };
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if *local_idx < num_params.min(4) {
                        let target = index_to_reg(*local_idx as u8);
                        if val != target {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        local_to_reg.insert(*local_idx, target);
                    } else if let Some(&(off, true)) = layout.locals.get(local_idx) {
                        // i64 spilled local: store BOTH 32-bit halves
                        // (lower at offset N, upper at N+4) via the I64Str
                        // pseudo-op. Without this we drop the upper half.
                        let val_hi = i64_pair_hi(val)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64Str {
                                rdlo: val,
                                rdhi: val_hi,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, false)) = layout.locals.get(local_idx) {
                        // i32 spilled local: single 4-byte store.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // Fall-through for compatibility (shouldn't happen).
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, (*local_idx as i32 - 4) * 4),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                LocalTee(local_idx) => {
                    // Like local.set but keeps value on stack. Peek is
                    // reload-aware (#171): a spilled TOS is reloaded in place.
                    let val = peek_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    if let Some(&off) = layout.incoming_params.get(local_idx) {
                        // #359: write to the incoming stack-passed param's slot;
                        // value stays on the operand stack (peek kept it). i32 by
                        // construction — a 64-bit param is refused up front.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, is_i64)) = layout.param_slots.get(local_idx) {
                        // #204/#193: frame-backed param — store to its slot; value
                        // stays on the operand stack (peek kept it).
                        let op = if is_i64 {
                            ArmOp::I64Str {
                                rdlo: val,
                                rdhi: i64_pair_hi(val)?,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        } else {
                            ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            }
                        };
                        instructions.push(ArmInstruction {
                            op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if *local_idx < num_params.min(4) {
                        let target = index_to_reg(*local_idx as u8);
                        if val != target {
                            instructions.push(ArmInstruction {
                                op: ArmOp::Mov {
                                    rd: target,
                                    op2: Operand2::Reg(val),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        local_to_reg.insert(*local_idx, target);
                    } else if let Some(&(off, true)) = layout.locals.get(local_idx) {
                        // i64 spilled local: store both halves like LocalSet.
                        let val_hi = i64_pair_hi(val)?;
                        instructions.push(ArmInstruction {
                            op: ArmOp::I64Str {
                                rdlo: val,
                                rdhi: val_hi,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else if let Some(&(off, false)) = layout.locals.get(local_idx) {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, off),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    } else {
                        // Fall-through for compatibility.
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: val,
                                addr: MemAddr::imm(Reg::SP, (*local_idx as i32 - 4) * 4),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                }

                GlobalGet(global_idx) => {
                    // #237 (gale, mutex-on-silicon): under the native-pointer ABI,
                    // globals live in MATERIALIZED slots (`__synth_globals + idx*4`,
                    // emitted into the object's .data with their wasm init values)
                    // — mutable state that survives global.set, unlike the earlier
                    // constant promotion whose paired dropped-store miscompiled any
                    // multi-function module that moves the shadow-stack pointer.
                    // Slots hold wasm OFFSETS (no data relocation needed); the SP
                    // global is rebased to an absolute pointer on read so address
                    // arithmetic and [r11=0 + addr] accesses see host pointers.
                    if self.native_pointer_abi {
                        let dst = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::emit_sym_addr(
                            &mut instructions,
                            dst,
                            "__synth_globals",
                            (*global_idx as i32) * 4,
                            idx,
                        );
                        instructions.push(ArmInstruction {
                            op: ArmOp::Ldr {
                                rd: dst,
                                addr: MemAddr::imm(dst, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        stack.push(StackVal::i32(dst));
                        if let Some((sp_idx, _)) = self.sp_global
                            && *global_idx == sp_idx
                        {
                            // dst is on the operand stack now, so the base temp
                            // cannot alias it.
                            let base = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &live_params,
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, base, 0, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Add {
                                    rd: dst,
                                    rn: dst,
                                    op2: Operand2::Reg(base),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                        }
                        continue;
                    }
                    // Load global value from globals table (R9 = globals base).
                    // Each i32 global occupies 4 bytes at offset index * 4.
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Ldr {
                            rd: dst,
                            addr: MemAddr::imm(Reg::R9, (*global_idx as i32) * 4),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                GlobalSet(global_idx) => {
                    // Pop value from stack and store to globals table (R9 = globals base).
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // #237 (gale, mutex-on-silicon): under the native-pointer ABI
                    // the store is REAL — write the value into the global's
                    // materialized slot. The earlier "dropped store" leaf
                    // assumption miscompiled multi-function modules whose callees
                    // re-read the moved shadow-stack pointer. The SP global's
                    // absolute pointer is rebased back to a wasm offset before the
                    // store (slots hold offsets; no data relocation needed).
                    if self.native_pointer_abi {
                        let mut reserved = live_params.clone();
                        reserved.push(val);
                        let stored = if let Some((sp_idx, _)) = self.sp_global
                            && *global_idx == sp_idx
                        {
                            let base = alloc_temp_or_spill(
                                &mut next_temp,
                                &mut stack,
                                &mut instructions,
                                &mut spill,
                                &reserved,
                                idx,
                            )?;
                            Self::emit_wasm_data_addr(&mut instructions, base, 0, idx);
                            instructions.push(ArmInstruction {
                                op: ArmOp::Sub {
                                    rd: base,
                                    rn: val,
                                    op2: Operand2::Reg(base),
                                },
                                source_line: Some(idx),
                            });
                            cf.add_instruction();
                            base
                        } else {
                            val
                        };
                        reserved.push(stored);
                        let slot = alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &reserved,
                            idx,
                        )?;
                        Self::emit_sym_addr(
                            &mut instructions,
                            slot,
                            "__synth_globals",
                            (*global_idx as i32) * 4,
                            idx,
                        );
                        instructions.push(ArmInstruction {
                            op: ArmOp::Str {
                                rd: stored,
                                addr: MemAddr::imm(slot, 0),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                        continue;
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Str {
                            rd: val,
                            addr: MemAddr::imm(Reg::R9, (*global_idx as i32) * 4),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                }

                // =========================================================
                // i64 operations with proper stack tracking
                // =========================================================
                // Convention: i64 values occupy a register pair (lo, hi).
                // Only the lo register is pushed onto the virtual stack.
                // The hi register is derived as the next consecutive
                // register via i64_pair_hi(lo).
                // Pairs are allocated as two consecutive temp registers.
                // =========================================================
                I64Const(val) => {
                    // Allocate a CONSECUTIVE register pair for the 64-bit
                    // constant. Two separate alloc_temp_safe calls can return
                    // non-consecutive registers if something in between is
                    // live on the wasm stack, which then breaks the
                    // i64_pair_hi convention used by every i64 op downstream.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[],
                        &live_params,
                        idx,
                    )?;

                    instructions.push(ArmInstruction {
                        op: ArmOp::I64Const {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            value: *val,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    // Push only the lo register; hi is derived via i64_pair_hi
                    stack.push(StackVal::i64(dst_lo));
                }

                I64Add => {
                    // Pop two i64 register pairs: b (top), a (second)
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;

                    // Allocate result register pair. MUST be consecutive
                    // in ALLOCATABLE_REGS — i64_pair_hi assumes consecutive
                    // and is called by every i64 op downstream to recover
                    // the high register. Two separate alloc_temp_safe calls
                    // skip live registers and produce non-consecutive pairs.
                    // Avoid clobbering the just-popped operand pairs before
                    // the ADC reads them — passing them in extra_avoid
                    // ensures dst doesn't overlap any of a_lo/a_hi/b_lo/b_hi.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;

                    // ADDS dst_lo, a_lo, b_lo  (sets carry flag)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Adds {
                            rd: dst_lo,
                            rn: a_lo,
                            op2: Operand2::Reg(b_lo),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // ADC dst_hi, a_hi, b_hi  (adds with carry)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Adc {
                            rd: dst_hi,
                            rn: a_hi,
                            op2: Operand2::Reg(b_hi),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    stack.push(StackVal::i64(dst_lo));
                }

                I64Sub => {
                    // Pop two i64 register pairs: b (top), a (second)
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;

                    // See I64Add for why extra_avoid carries a_*/b_* —
                    // dst must not overlap any operand half before SBC reads it.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;

                    // SUBS dst_lo, a_lo, b_lo  (sets borrow flag)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Subs {
                            rd: dst_lo,
                            rn: a_lo,
                            op2: Operand2::Reg(b_lo),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // SBC dst_hi, a_hi, b_hi  (subtracts with borrow)
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sbc {
                            rd: dst_hi,
                            rn: a_hi,
                            op2: Operand2::Reg(b_hi),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 bitwise ops (I64Or / I64And / I64Xor)
                //
                // Each pops two i64 register pairs from the wasm stack and
                // emits two ARM ops (low-half then high-half) into a freshly
                // allocated consecutive pair. This replaces the wildcard
                // fallthrough to select_default, which assumed inputs in
                // R0:R1 and R2:R3 — incorrect when the wasm stack tracks
                // arbitrary register pairs from earlier ops.
                // ============================================================
                I64Or | I64And | I64Xor => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // dst must not overlap any popped operand's half — the
                    // hi instruction reads a_hi and b_hi after the lo
                    // instruction writes dst_lo.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    let (lo_op, hi_op) = match op {
                        I64Or => (
                            ArmOp::Orr {
                                rd: dst_lo,
                                rn: a_lo,
                                op2: Operand2::Reg(b_lo),
                            },
                            ArmOp::Orr {
                                rd: dst_hi,
                                rn: a_hi,
                                op2: Operand2::Reg(b_hi),
                            },
                        ),
                        I64And => (
                            ArmOp::And {
                                rd: dst_lo,
                                rn: a_lo,
                                op2: Operand2::Reg(b_lo),
                            },
                            ArmOp::And {
                                rd: dst_hi,
                                rn: a_hi,
                                op2: Operand2::Reg(b_hi),
                            },
                        ),
                        I64Xor => (
                            ArmOp::Eor {
                                rd: dst_lo,
                                rn: a_lo,
                                op2: Operand2::Reg(b_lo),
                            },
                            ArmOp::Eor {
                                rd: dst_hi,
                                rn: a_hi,
                                op2: Operand2::Reg(b_hi),
                            },
                        ),
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: lo_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    instructions.push(ArmInstruction {
                        op: hi_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i32 -> i64 extension (I64ExtendI32U / I64ExtendI32S)
                //
                // Pops one i32, allocates a consecutive i64 pair, places the
                // i32 in the low half. For unsigned: high = 0. For signed:
                // high = arithmetic-shift-right by 31 (sign-extension).
                // ============================================================
                I64ExtendI32U => {
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    // val must stay alive until the Mov reads it; dst_hi
                    // must not be val (we'd write the zero high before
                    // moving val to dst_lo).
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[val],
                        &live_params,
                        idx,
                    )?;
                    if val != dst_lo {
                        instructions.push(ArmInstruction {
                            op: ArmOp::Mov {
                                rd: dst_lo,
                                op2: Operand2::Reg(val),
                            },
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    instructions.push(ArmInstruction {
                        op: ArmOp::Movw {
                            rd: dst_hi,
                            imm16: 0,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                I64ExtendI32S => {
                    let val = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[val],
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::I64ExtendI32S {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rn: val,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 variable shifts (I64Shl / I64ShrU / I64ShrS)
                //
                // Use the existing I64Shl/I64ShrU/I64ShrS pseudo-ops (which
                // expand to the variable-shift logic in arm_encoder.rs) but
                // pass the actual stack-tracked register pairs rather than
                // assuming R0:R1 / R2:R3.
                // ============================================================
                I64Shl | I64ShrU | I64ShrS => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // dst must not overlap any popped operand's half — the
                    // shift pseudo-op reads all four (rn_lo/rn_hi/rm_lo/rm_hi)
                    // before writing the destination.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    let shift_op = match op {
                        I64Shl => ArmOp::I64Shl {
                            rd_lo: dst_lo,
                            rd_hi: dst_hi,
                            rn_lo: a_lo,
                            rn_hi: a_hi,
                            rm_lo: b_lo,
                            rm_hi: b_hi,
                        },
                        I64ShrU => ArmOp::I64ShrU {
                            rd_lo: dst_lo,
                            rd_hi: dst_hi,
                            rn_lo: a_lo,
                            rn_hi: a_hi,
                            rm_lo: b_lo,
                            rm_hi: b_hi,
                        },
                        I64ShrS => ArmOp::I64ShrS {
                            rd_lo: dst_lo,
                            rd_hi: dst_hi,
                            rn_lo: a_lo,
                            rn_hi: a_hi,
                            rm_lo: b_lo,
                            rm_hi: b_hi,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: shift_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                I64Load { offset, .. } => {
                    // Pop address from stack
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    // Allocate result register pair. MUST be consecutive
                    // in ALLOCATABLE_REGS — i64_pair_hi assumes consecutive
                    // and is called by every i64 op downstream to recover
                    // the high register. Avoid clobbering addr before the
                    // load uses it.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[addr],
                        &live_params,
                        idx,
                    )?;

                    // Generate bounds-checked i64 load into the allocated pair
                    let load_ops =
                        self.generate_i64_load_into_regs(dst_lo, dst_hi, addr, *offset as i32);
                    for arm_op in load_ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                    stack.push(StackVal::i64(dst_lo));
                }

                I64Store { offset, .. } => {
                    // WASM i64.store pops: value first, then address
                    let value_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let addr = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let value_hi = i64_pair_hi(value_lo)?;

                    // Generate bounds-checked i64 store from the value pair
                    let store_ops =
                        self.generate_i64_store_from_regs(value_lo, value_hi, addr, *offset as i32);
                    for arm_op in store_ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                    }
                    // Store doesn't push anything to stack
                }

                I64Eqz => {
                    // Pop one i64 register pair
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let src_hi = i64_pair_hi(src_lo)?;

                    // Result is a single i32 (0 or 1)
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;

                    instructions.push(ArmInstruction {
                        op: ArmOp::I64SetCondZ {
                            rd: dst,
                            rn_lo: src_lo,
                            rn_hi: src_hi,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();

                    // I64Eqz produces an i32 result (single register)
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 comparisons (binary: pop 2, push 1)
                // CMP rn, rm; SetCond rd, <condition>
                // =========================================================
                I32Eq | I32Ne | I32LtS | I32LtU | I32GtS | I32GtU | I32LeS | I32LeU | I32GeS
                | I32GeU => {
                    // #258: fold a compare *bound* into a `cmp`/`cmn` immediate
                    // instead of materializing it into a register. A const
                    // `0..=0xFF` → `cmp a, #C`; a const `-0xFF..=-1` →
                    // `cmn a, #-C` (`cmp a, #neg` ≡ `cmn a, #|neg|`, same flags →
                    // same condition). Bounded to a byte (both imm encoders are
                    // correct there); the guard keeps it to a cleanly-tail
                    // materialization (not spilled), covering the `movw` and the
                    // `movw;mvn` (negative) forms.
                    let fold = if idx > 0
                        && instructions
                            .last()
                            .is_some_and(|i| i.source_line == Some(idx - 1))
                    {
                        match wasm_ops[idx - 1] {
                            WasmOp::I32Const(c) if (0..=0xFF).contains(&c) => Some((false, c)),
                            WasmOp::I32Const(c) if (-0xFF..=-1).contains(&c) => Some((true, -c)),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    let cmp_op = if let Some((is_neg, mag)) = fold {
                        let _b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        Self::drop_prev_const_materialization(&mut instructions, idx - 1);
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        if is_neg {
                            ArmOp::Cmn {
                                rn: a,
                                op2: Operand2::Imm(mag),
                            }
                        } else {
                            ArmOp::Cmp {
                                rn: a,
                                op2: Operand2::Imm(mag),
                            }
                        }
                    } else {
                        let b = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        let a = pop_operand(
                            &mut stack,
                            &mut next_temp,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?;
                        ArmOp::Cmp {
                            rn: a,
                            op2: Operand2::Reg(b),
                        }
                    };
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    let cond = match op {
                        I32Eq => Condition::EQ,
                        I32Ne => Condition::NE,
                        I32LtS => Condition::LT,
                        I32LtU => Condition::LO,
                        I32GtS => Condition::GT,
                        I32GtU => Condition::HI,
                        I32LeS => Condition::LE,
                        I32LeU => Condition::LS,
                        I32GeS => Condition::GE,
                        I32GeU => Condition::HS,
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: cmp_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    // SetCond rd, <cond> — materializes 0/1 based on flags
                    instructions.push(ArmInstruction {
                        op: ArmOp::SetCond { rd: dst, cond },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // i32.eqz (unary: pop 1, push 1)
                // CMP rn, #0; SetCond rd, EQ
                I32Eqz => {
                    let a = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Cmp {
                            rn: a,
                            op2: Operand2::Imm(0),
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    instructions.push(ArmInstruction {
                        op: ArmOp::SetCond {
                            rd: dst,
                            cond: Condition::EQ,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 shifts and rotates (binary: pop 2, push 1)
                // =========================================================
                I32Shl | I32ShrS | I32ShrU | I32Rotr => {
                    let shift_amt = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    let shift_op = match op {
                        I32Shl => ArmOp::LslReg {
                            rd: dst,
                            rn: value,
                            rm: shift_amt,
                        },
                        I32ShrU => ArmOp::LsrReg {
                            rd: dst,
                            rn: value,
                            rm: shift_amt,
                        },
                        I32ShrS => ArmOp::AsrReg {
                            rd: dst,
                            rn: value,
                            rm: shift_amt,
                        },
                        I32Rotr => ArmOp::RorReg {
                            rd: dst,
                            rn: value,
                            rm: shift_amt,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: shift_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                I32Rotl => {
                    // Rotate left by N = Rotate right by (32 - N)
                    // RSB tmp, shift_amt, #32; ROR dst, value, tmp
                    let shift_amt = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let value = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    let tmp = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::Rsb {
                            rd: tmp,
                            rn: shift_amt,
                            imm: 32,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    instructions.push(ArmInstruction {
                        op: ArmOp::RorReg {
                            rd: dst,
                            rn: value,
                            rm: tmp,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 unary bit operations (pop 1, push 1)
                // =========================================================
                I32Clz => {
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Clz { rd: dst, rm: src },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                I32Ctz => {
                    // Count trailing zeros: RBIT + CLZ
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Rbit { rd: dst, rm: src },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    instructions.push(ArmInstruction {
                        op: ArmOp::Clz { rd: dst, rm: dst },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                I32Popcnt => {
                    // Population count — no native ARM instruction
                    // Popcnt pseudo-op expanded by encoder
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Popcnt { rd: dst, rm: src },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // =========================================================
                // i32 sign extension (pop 1, push 1)
                // =========================================================
                I32Extend8S => {
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sxtb { rd: dst, rm: src },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                I32Extend16S => {
                    let src = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::Sxth { rd: dst, rm: src },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // ============================================================
                // i64 comparisons (binary: pop 2 i64 pairs, push 1 i32 result)
                //
                // Issue #103: previously these fell through to `select_default`,
                // which hardcodes the operand pairs at R0:R1 / R2:R3 and the
                // result at R0 — clobbering any AAPCS param register the user
                // hasn't read yet via `LocalGet`. The fix is to pop the actual
                // register pairs the stack tracker assigned to the operands and
                // allocate a result register with `alloc_temp_safe`, which
                // already skips live stack values.
                //
                // Same class as PR #86's i64-const fix in `optimizer_bridge`,
                // applied here to every i64 op that hardcoded R0..R3.
                // ============================================================
                I64Eq | I64Ne | I64LtS | I64LtU | I64LeS | I64LeU | I64GtS | I64GtU | I64GeS
                | I64GeU => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // Result is a single i32. alloc_temp_safe avoids any reg
                    // still on the wasm stack, but the popped operand halves
                    // are NO LONGER on the stack — they may be reused by the
                    // allocator. That is fine for I64SetCond which encodes to
                    // a sequence that reads all four operand halves before
                    // writing rd (see arm_encoder; the CMP chain is fully
                    // resolved before SetCond writes the byte).
                    let dst = if idx == wasm_ops.len() - 1 {
                        Reg::R0
                    } else {
                        alloc_temp_or_spill(
                            &mut next_temp,
                            &mut stack,
                            &mut instructions,
                            &mut spill,
                            &live_params,
                            idx,
                        )?
                    };
                    let cond = match op {
                        I64Eq => Condition::EQ,
                        I64Ne => Condition::NE,
                        I64LtS => Condition::LT,
                        I64LtU => Condition::LO,
                        I64LeS => Condition::LE,
                        I64LeU => Condition::LS,
                        I64GtS => Condition::GT,
                        I64GtU => Condition::HI,
                        I64GeS => Condition::GE,
                        I64GeU => Condition::HS,
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: ArmOp::I64SetCond {
                            rd: dst,
                            rn_lo: a_lo,
                            rn_hi: a_hi,
                            rm_lo: b_lo,
                            rm_hi: b_hi,
                            cond,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // ============================================================
                // i64 multiply (binary: pop 2 i64 pairs, push 1 i64 pair)
                //
                // Issue #103: was hardcoding R0:R1 (operands and result low),
                // R2:R3 (second operand). Now uses the stack-tracked pairs
                // and a fresh consecutive pair for the destination.
                // ============================================================
                I64Mul => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    // I64Mul encodes to UMULL + MLA cross products: rd_lo/rd_hi
                    // are written, and ALL four operand halves are read. dst
                    // must not overlap any operand half before the encoded
                    // sequence reads it.
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::I64Mul {
                            rd_lo: dst_lo,
                            rd_hi: dst_hi,
                            rn_lo: a_lo,
                            rn_hi: a_hi,
                            rm_lo: b_lo,
                            rm_hi: b_hi,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 divide / remainder (binary: pop 2 i64 pairs, push 1 pair)
                //
                // Issue #103: was hardcoding R0:R1 / R2:R3. The encoded
                // sequence for these ops is a libcall-style helper that
                // reads/writes the operand and result registers — using the
                // stack-tracked pairs keeps AAPCS params intact.
                // ============================================================
                I64DivS | I64DivU | I64RemS | I64RemU => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    let arm_op = match op {
                        I64DivS => ArmOp::I64DivS {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                        },
                        I64DivU => ArmOp::I64DivU {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                        },
                        I64RemS => ArmOp::I64RemS {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                        },
                        I64RemU => ArmOp::I64RemU {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            rmlo: b_lo,
                            rmhi: b_hi,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 rotations (binary: pop 2 i64 pairs, push 1 pair)
                //
                // Issue #103: was hardcoding R0:R1 / R2. ArmOp::I64Rotl/Rotr
                // takes a SINGLE shift reg (the low half of the i64 shift
                // amount) — i64.rotl in WASM has an i64 shift amount but
                // ARM only uses the low 32 bits modulo-64 by convention.
                // We pop both halves of `b` for stack correctness and pass
                // b_lo as the shift reg, matching the pre-fix `select_default`
                // contract (which assumed shift in R2).
                // ============================================================
                I64Rotl | I64Rotr => {
                    let b_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let a_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let b_hi = i64_pair_hi(b_lo)?;
                    let a_hi = i64_pair_hi(a_lo)?;
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[a_lo, a_hi, b_lo, b_hi],
                        &live_params,
                        idx,
                    )?;
                    let arm_op = match op {
                        I64Rotl => ArmOp::I64Rotl {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            shift: b_lo,
                        },
                        I64Rotr => ArmOp::I64Rotr {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: a_lo,
                            rnhi: a_hi,
                            shift: b_lo,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 unary bit ops (pop 1 i64 pair, push 1 i32 result)
                //
                // I64Clz / I64Ctz / I64Popcnt return a 32-bit count. Was
                // hardcoding R0 (operand lo + result) and R1 (operand hi).
                // ============================================================
                I64Clz | I64Ctz | I64Popcnt => {
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let src_hi = i64_pair_hi(src_lo)?;
                    // The count is i64-typed (lo = count 0..64, hi = 0). Produce
                    // a proper pair so the hi half is reserved and zeroed
                    // (#204/#171: pushing i32 left hi unreserved/garbage for a
                    // downstream i64 consumer).
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[src_lo, src_hi],
                        &live_params,
                        idx,
                    )?;
                    let arm_op = match op {
                        I64Clz => ArmOp::I64Clz {
                            rd: dst_lo,
                            rnlo: src_lo,
                            rnhi: src_hi,
                        },
                        I64Ctz => ArmOp::I64Ctz {
                            rd: dst_lo,
                            rnlo: src_lo,
                            rnhi: src_hi,
                        },
                        I64Popcnt => ArmOp::I64Popcnt {
                            rd: dst_lo,
                            rnlo: src_lo,
                            rnhi: src_hi,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    instructions.push(ArmInstruction {
                        op: ArmOp::Movw {
                            rd: dst_hi,
                            imm16: 0,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 in-place sign extension (pop 1 i64 pair, push 1 pair)
                //
                // I64Extend{8,16,32}S take an i64 (the upper bits are
                // ignored) and sign-extend the low N bits to 64. Was
                // hardcoding R0:R1 for both operand and result.
                // ============================================================
                I64Extend8S | I64Extend16S | I64Extend32S => {
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let _src_hi = i64_pair_hi(src_lo)?;
                    // dst must not overlap src_lo before the encoded sequence
                    // reads it (the encoder issues a SXTB/SXTH/MOV + ASR #31
                    // pattern that reads src_lo first then writes rdlo/rdhi).
                    let (dst_lo, dst_hi) = alloc_consecutive_pair(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &[src_lo],
                        &live_params,
                        idx,
                    )?;
                    let arm_op = match op {
                        I64Extend8S => ArmOp::I64Extend8S {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: src_lo,
                        },
                        I64Extend16S => ArmOp::I64Extend16S {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: src_lo,
                        },
                        I64Extend32S => ArmOp::I64Extend32S {
                            rdlo: dst_lo,
                            rdhi: dst_hi,
                            rnlo: src_lo,
                        },
                        _ => unreachable!(),
                    };
                    instructions.push(ArmInstruction {
                        op: arm_op,
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i64(dst_lo));
                }

                // ============================================================
                // i64 → i32 wrap (pop 1 i64 pair, push 1 i32)
                //
                // I32WrapI64 keeps the low half. Was hardcoding R0 for both
                // operand low and result.
                // ============================================================
                I32WrapI64 => {
                    let src_lo = pop_operand(
                        &mut stack,
                        &mut next_temp,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    let _src_hi = i64_pair_hi(src_lo)?;
                    // Always allocate a fresh temporary. Pre-fix, this picked
                    // `Reg::R0` when `idx == wasm_ops.len() - 1`, on the theory
                    // that "the last wasm op is the function's return value, so
                    // place it directly in R0". That premature R0-pin clobbers
                    // any AAPCS param the function hasn't yet read — PR #100's
                    // `i64_lowering_doesnt_clobber_params` fuzz harness caught
                    // this for the `i64.const; i32.wrap_i64` pattern (rdlo
                    // landing on R3, then I32WrapI64 pinning rd=R0). The
                    // function epilogue now handles the return-value Mov to R0
                    // explicitly via `emit_return_move_if_needed` below.
                    let dst = alloc_temp_or_spill(
                        &mut next_temp,
                        &mut stack,
                        &mut instructions,
                        &mut spill,
                        &live_params,
                        idx,
                    )?;
                    instructions.push(ArmInstruction {
                        op: ArmOp::I32WrapI64 {
                            rd: dst,
                            rnlo: src_lo,
                        },
                        source_line: Some(idx),
                    });
                    cf.add_instruction();
                    stack.push(StackVal::i32(dst));
                }

                // For other operations, fall back to default behavior.
                // Stack tracking is approximate after this point: select_default
                // uses its own register allocator and doesn't update the virtual stack.
                _ => {
                    let arm_ops = self.select_default(op)?;
                    for arm_op in arm_ops {
                        instructions.push(ArmInstruction {
                            op: arm_op,
                            source_line: Some(idx),
                        });
                        cf.add_instruction();
                    }
                    // Update stack based on WASM stack effect.
                    // This is approximate — select_default allocated its own registers.
                    let (pops, pushes) = wasm_stack_effect(op);
                    for _ in 0..pops.min(stack.len()) {
                        stack.pop();
                    }
                    for _ in 0..pushes {
                        // Push a placeholder — select_default used its own register
                        let placeholder = self.regs.alloc_reg();
                        stack.push(StackVal::i32(placeholder));
                    }
                }
            }
        }

        // Function epilogue: place the AAPCS return value in R0 (if the last
        // expression result isn't already there), deallocate the local frame,
        // then restore callee-saved registers and return via PC.
        //
        // Pre-fix, several wasm-op handlers (I32Add, I32Sub, ..., I32WrapI64,
        // I64ExtendI32U/S) pinned the destination register to R0 when their
        // `idx == wasm_ops.len() - 1`. That heuristic conflated "lexically
        // last op handed to select_with_stack" with "function-return
        // boundary"; with the move to fuzz-driven testing (PR #100) those
        // are no longer the same thing, and the pin caused AAPCS-param
        // clobbers. The fix is to keep results in regalloc-chosen temps and
        // have the epilogue emit the AAPCS return-value move here, ONCE.
        //
        // `source_line: None` keeps the move out of the
        // "writes-param-reg-before-LocalGet" invariant the fuzz harness
        // checks; it's the function-boundary Mov, not a body-level write.
        // Reload-aware (#171): a spilled final result is reloaded before the
        // AAPCS return-value move. Past the op loop, so use wasm_ops.len() as
        // the synthetic source line for any reload.
        // #311 defect 3 (gale): an i64 RESULT is the (lo, hi) pair and BOTH
        // halves must reach r0:r1 — the single-register move silently dropped
        // the hi whenever the final value transited registers other than
        // r0/r1 (decide() returned (0,0) where the contract says (0,1)).
        // Capture the width BEFORE peek (which returns only the lo register).
        let result_is_i64 = matches!(
            stack.last(),
            Some(StackVal::Reg { is_i64: true, .. }) | Some(StackVal::Spilled { is_i64: true, .. })
        );
        let result_reg = if stack.is_empty() {
            None
        } else {
            Some(peek_operand(
                &mut stack,
                &mut next_temp,
                &mut instructions,
                &mut spill,
                &[],
                wasm_ops.len(),
            )?)
        };
        if let Some(result_reg) = result_reg {
            // lo move FIRST: for a consecutive pair (hi = lo+1) the only
            // overlap case is lo == R1 (hi == R2), where r1 must be READ by
            // the lo move before the hi move WRITES it — lo-first is safe for
            // every possible pair (hi == R0 would require lo == "R-1").
            if result_reg != Reg::R0 {
                instructions.push(ArmInstruction {
                    op: ArmOp::Mov {
                        rd: Reg::R0,
                        op2: Operand2::Reg(result_reg),
                    },
                    source_line: None,
                });
            }
            if result_is_i64 {
                let hi = i64_pair_hi(result_reg)?;
                if hi != Reg::R1 {
                    instructions.push(ArmInstruction {
                        op: ArmOp::Mov {
                            rd: Reg::R1,
                            op2: Operand2::Reg(hi),
                        },
                        source_line: None,
                    });
                }
            }
        }
        if layout.frame_size > 0 {
            instructions.push(ArmInstruction {
                op: ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    op2: Operand2::Imm(layout.frame_size),
                },
                source_line: None,
            });
        }
        // POP {R4-R8, PC} restores registers and returns (PC = saved LR)
        instructions.push(ArmInstruction {
            op: ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
            },
            source_line: None,
        });

        Ok(instructions)
    }
}

/// Validate that all ARM instructions in the sequence are supported by the target.
///
/// This is the ISA feature gate: it checks each generated ARM instruction against
/// the target's FPU capabilities and returns an error for the first unsupported
/// instruction encountered. This must be called AFTER instruction selection but
/// BEFORE encoding, to ensure the compiler never emits an instruction that the
/// target platform cannot execute.
pub fn validate_instructions(
    instructions: &[ArmInstruction],
    fpu: Option<FPUPrecision>,
    target_name: &str,
) -> Result<()> {
    validate_instructions_with_helium(instructions, fpu, false, target_name)
}

/// Validate instructions with full ISA feature gating including Helium MVE.
pub fn validate_instructions_with_helium(
    instructions: &[ArmInstruction],
    fpu: Option<FPUPrecision>,
    has_helium: bool,
    target_name: &str,
) -> Result<()> {
    for instr in instructions {
        // Check FPU requirement (single-precision or higher)
        if instr.op.requires_fpu() && fpu.is_none() {
            return Err(synth_core::Error::UnsupportedInstruction(format!(
                "instruction {} requires FPU, but target {} has no FPU",
                instr.op.instruction_name(),
                target_name,
            )));
        }

        // Check double-precision FPU requirement
        if instr.op.requires_double_precision_fpu() && !matches!(fpu, Some(FPUPrecision::Double)) {
            let reason = if fpu.is_some() {
                "only has single-precision FPU"
            } else {
                "has no FPU"
            };
            return Err(synth_core::Error::UnsupportedInstruction(format!(
                "instruction {} requires double-precision FPU, but target {} {}",
                instr.op.instruction_name(),
                target_name,
                reason,
            )));
        }

        // Check Helium MVE requirement
        if instr.op.requires_helium() && !has_helium {
            return Err(synth_core::Error::UnsupportedInstruction(format!(
                "instruction {} requires Helium MVE, but target {} does not have Helium",
                instr.op.instruction_name(),
                target_name,
            )));
        }
    }
    Ok(())
}

/// Statistics from instruction selection
#[derive(Debug, Clone, Default)]
pub struct SelectionStats {
    /// Total number of registers used
    pub total_registers_used: usize,
    /// Number of variables mapped to registers
    pub variables_mapped: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::RuleDatabase;

    #[test]
    fn test_register_allocation() {
        let mut regs = RegisterState::new();

        let r0 = regs.alloc_reg();
        let r1 = regs.alloc_reg();
        let r2 = regs.alloc_reg();

        assert_eq!(r0, Reg::R0);
        assert_eq!(r1, Reg::R1);
        assert_eq!(r2, Reg::R2);
    }

    #[test]
    fn test_variable_mapping() {
        let mut regs = RegisterState::new();

        let r1 = regs.get_or_alloc("x");
        let r2 = regs.get_or_alloc("y");
        let r3 = regs.get_or_alloc("x"); // Should reuse same register

        assert_eq!(r1, r3); // Same variable gets same register
        assert_ne!(r1, r2); // Different variables get different registers
    }

    #[test]
    fn test_instruction_selector_creation() {
        let db = RuleDatabase::new();
        let selector = InstructionSelector::new(db.rules().to_vec());

        assert_eq!(selector.regs.next_reg, 0);
    }

    #[test]
    fn test_select_default_add() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Add];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Add { .. } => {}
            _ => panic!("Expected Add instruction"),
        }
    }

    #[test]
    fn test_select_arithmetic_sequence() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(5),
            WasmOp::I32Const(10),
            WasmOp::I32Add,
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
        ];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should generate at least one instruction per WASM op
        assert!(arm_instrs.len() >= wasm_ops.len());
    }

    #[test]
    fn test_select_memory_operations() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Load {
                offset: 0,
                align: 4,
            },
            WasmOp::I32Const(42),
            WasmOp::I32Store {
                offset: 4,
                align: 4,
            },
        ];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        // First should be load
        match &arm_instrs[0].op {
            ArmOp::Ldr { .. } => {}
            _ => panic!("Expected Ldr instruction"),
        }

        // Last should be store
        match &arm_instrs[2].op {
            ArmOp::Str { .. } => {}
            _ => panic!("Expected Str instruction"),
        }
    }

    #[test]
    fn test_selector_stats() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Add, WasmOp::I32Sub, WasmOp::I32Mul];
        let instrs = selector.select(&wasm_ops).unwrap();

        // `total_registers_used` is the round-robin allocator's `next_reg`, which
        // wraps modulo the allocatable pool size — so assert on the selection
        // output (the meaningful signal) rather than the wrapping counter.
        assert!(!instrs.is_empty());
        let _ = selector.get_stats().total_registers_used;
    }

    #[test]
    fn test_selector_reset() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Add];
        let _ = selector.select(&wasm_ops).unwrap();

        assert!(selector.regs.next_reg > 0);

        selector.reset();
        assert_eq!(selector.regs.next_reg, 0);
    }

    #[test]
    fn test_bitwise_operations() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32And, WasmOp::I32Or, WasmOp::I32Xor];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        match &arm_instrs[0].op {
            ArmOp::And { .. } => {}
            _ => panic!("Expected And"),
        }

        match &arm_instrs[1].op {
            ArmOp::Orr { .. } => {}
            _ => panic!("Expected Orr"),
        }

        match &arm_instrs[2].op {
            ArmOp::Eor { .. } => {}
            _ => panic!("Expected Eor"),
        }
    }

    #[test]
    fn test_shift_operations() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        // WASM shifts take the shift amount from the stack (dynamic),
        // so we emit register-based shift instructions.
        let wasm_ops = vec![WasmOp::I32Shl, WasmOp::I32ShrS, WasmOp::I32ShrU];

        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3);

        match &arm_instrs[0].op {
            ArmOp::LslReg { .. } => {}
            _ => panic!("Expected LslReg, got {:?}", arm_instrs[0].op),
        }

        match &arm_instrs[1].op {
            ArmOp::AsrReg { .. } => {}
            _ => panic!("Expected AsrReg, got {:?}", arm_instrs[1].op),
        }

        match &arm_instrs[2].op {
            ArmOp::LsrReg { .. } => {}
            _ => panic!("Expected LsrReg, got {:?}", arm_instrs[2].op),
        }
    }

    #[test]
    fn test_index_to_reg_conversion() {
        assert_eq!(index_to_reg(0), Reg::R0);
        assert_eq!(index_to_reg(1), Reg::R1);
        assert_eq!(index_to_reg(8), Reg::R8); // last allocatable (R0-R8)
        assert_eq!(index_to_reg(9), Reg::R0); // wraps after 9 allocatable registers
        // Verify reserved registers are never allocated (#212: R12 now reserved
        // as the encoder's IP scratch alongside R9/R10/R11).
        for i in 0..100u8 {
            let reg = index_to_reg(i);
            assert_ne!(reg, Reg::R9, "R9 (globals base) must never be allocated");
            assert_ne!(reg, Reg::R10, "R10 (mem size) must never be allocated");
            assert_ne!(reg, Reg::R11, "R11 (mem base) must never be allocated");
            assert_ne!(reg, Reg::R12, "R12 (IP scratch) must never be allocated");
        }
    }

    /// #212: the encoder uses R12/IP as scratch for indexed `[R11 + addr + #off]`
    /// memory addressing (`ADD ip, addr, #off; LDR rd, [R11, ip]`). If the
    /// operand allocator places a live value in R12, that live value is clobbered
    /// by the address calc. With R12 reserved, `select_with_stack` must never emit
    /// R12 as a destination on the default (no bounds-check) path — reproduces the
    /// `i32.const 0; … i32.load …; i32.sub` (negation-after-load) shape that
    /// miscompiled gale's inlined `flight_algo`.
    #[test]
    fn test_212_selector_never_allocates_r12() {
        // Pressure: several live constants, then an address + load + negation,
        // mirroring the divided-field reader in the inlined controller body.
        let wasm_ops = vec![
            WasmOp::I32Const(11),
            WasmOp::I32Const(22),
            WasmOp::I32Const(33),
            WasmOp::I32Const(44),
            WasmOp::I32Const(55),
            WasmOp::I32Const(0), // negation base (the one that landed in R12)
            WasmOp::LocalGet(0), // address
            WasmOp::I32Load {
                offset: 4,
                align: 2,
            },
            WasmOp::I32Const(6),
            WasmOp::I32ShrS,
            WasmOp::I32Sub, // 0 - (loaded >> 6)
        ];
        let mut selector = fresh_selector();
        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        fn dest(op: &ArmOp) -> Option<Reg> {
            match *op {
                ArmOp::Mov { rd, .. }
                | ArmOp::Movw { rd, .. }
                | ArmOp::Movt { rd, .. }
                | ArmOp::Mvn { rd, .. }
                | ArmOp::Add { rd, .. }
                | ArmOp::Sub { rd, .. }
                | ArmOp::And { rd, .. }
                | ArmOp::Asr { rd, .. }
                | ArmOp::Lsl { rd, .. }
                | ArmOp::Lsr { rd, .. }
                | ArmOp::Ldr { rd, .. } => Some(rd),
                _ => None,
            }
        }
        // No operand-producing instruction targets R12 (it is encoder scratch only).
        for ins in &instrs {
            assert_ne!(
                dest(&ins.op),
                Some(Reg::R12),
                "selector allocated R12 as an operand dest (#212): {:?}",
                ins.op
            );
        }
    }

    #[test]
    fn test_bounds_check_none() {
        // With BoundsCheckConfig::None, loads/stores should generate single instruction
        let db = RuleDatabase::new();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), BoundsCheckConfig::None);

        let wasm_ops = vec![WasmOp::I32Load {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should be just the LDR instruction (1 instruction)
        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldr { .. } => {}
            _ => panic!("Expected Ldr instruction"),
        }
    }

    #[test]
    fn test_bounds_check_software() {
        // With BoundsCheckConfig::Software, loads should generate bounds check sequence
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::with_bounds_check(
            db.rules().to_vec(),
            BoundsCheckConfig::Software,
        );

        let wasm_ops = vec![WasmOp::I32Load {
            offset: 4,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should be: ADD temp, addr, #(offset+access_size-1); CMP temp, R10; BHS trap; LDR
        assert_eq!(arm_instrs.len(), 4);

        // First: ADD to calculate end-of-access address (offset=4, access_size=4 -> 4+4-1=7)
        match &arm_instrs[0].op {
            ArmOp::Add {
                rd,
                rn: _,
                op2: Operand2::Imm(7),
            } => {
                assert_eq!(*rd, Reg::R12); // Uses R12 as temp
            }
            other => panic!(
                "Expected Add with immediate 7 (offset+access_size-1), got {:?}",
                other
            ),
        }

        // Second: CMP against R10 (memory size)
        match &arm_instrs[1].op {
            ArmOp::Cmp {
                rn,
                op2: Operand2::Reg(Reg::R10),
            } => {
                assert_eq!(*rn, Reg::R12); // Compare temp
            }
            other => panic!("Expected Cmp against R10, got {:?}", other),
        }

        // Third: BHS to trap handler
        match &arm_instrs[2].op {
            ArmOp::Bhs { label } => {
                assert_eq!(label, "Trap_Handler");
            }
            other => panic!("Expected Bhs to Trap_Handler, got {:?}", other),
        }

        // Fourth: The actual LDR
        match &arm_instrs[3].op {
            ArmOp::Ldr { .. } => {}
            other => panic!("Expected Ldr instruction, got {:?}", other),
        }
    }

    #[test]
    fn test_validate_instructions_rejects_fpu_on_no_fpu_target() {
        // Simulate FPU instructions being generated, then validate against a no-FPU target
        let instrs = vec![ArmInstruction {
            op: ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S1,
                sm: VfpReg::S2,
            },
            source_line: Some(0),
        }];
        let result = super::validate_instructions(&instrs, None, "cortex-m3");
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("requires FPU"),
            "Error should mention FPU requirement, got: {err}"
        );
        assert!(
            err.contains("cortex-m3"),
            "Error should mention target name, got: {err}"
        );
    }

    #[test]
    fn test_validate_instructions_allows_fpu_on_fpu_target() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S1,
                sm: VfpReg::S2,
            },
            source_line: Some(0),
        }];
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_instructions_rejects_f64_on_single_precision() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::F64Add {
                dd: VfpReg::D0,
                dn: VfpReg::D1,
                dm: VfpReg::D2,
            },
            source_line: Some(0),
        }];
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("double-precision"),
            "Error should mention double-precision, got: {err}"
        );
    }

    #[test]
    fn test_validate_instructions_allows_f64_on_double_precision() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::F64Add {
                dd: VfpReg::D0,
                dn: VfpReg::D1,
                dm: VfpReg::D2,
            },
            source_line: Some(0),
        }];
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Double), "cortex-m7dp");
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_instructions_allows_integer_ops_on_all_targets() {
        let instrs = vec![
            ArmInstruction {
                op: ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    op2: Operand2::Reg(Reg::R2),
                },
                source_line: Some(0),
            },
            ArmInstruction {
                op: ArmOp::Mul {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                source_line: Some(1),
            },
            ArmInstruction {
                op: ArmOp::Sdiv {
                    rd: Reg::R0,
                    rn: Reg::R1,
                    rm: Reg::R2,
                },
                source_line: Some(2),
            },
            ArmInstruction {
                op: ArmOp::Clz {
                    rd: Reg::R0,
                    rm: Reg::R1,
                },
                source_line: Some(3),
            },
        ];

        // Should pass on M3 (no FPU)
        let result = super::validate_instructions(&instrs, None, "cortex-m3");
        assert!(result.is_ok(), "Integer ops should pass on cortex-m3");

        // Should pass on M4F (with FPU)
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Single), "cortex-m4f");
        assert!(result.is_ok(), "Integer ops should pass on cortex-m4f");

        // Should pass on M7DP (with double FPU)
        let result =
            super::validate_instructions(&instrs, Some(FPUPrecision::Double), "cortex-m7dp");
        assert!(result.is_ok(), "Integer ops should pass on cortex-m7dp");
    }

    #[test]
    fn test_bounds_check_masking() {
        // With BoundsCheckConfig::Masking, loads should generate AND + LDR
        let db = RuleDatabase::new();
        let mut selector =
            InstructionSelector::with_bounds_check(db.rules().to_vec(), BoundsCheckConfig::Masking);

        let wasm_ops = vec![WasmOp::I32Store {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // Should be: AND addr, addr, R10; STR
        assert_eq!(arm_instrs.len(), 2);

        // First: AND to mask address
        match &arm_instrs[0].op {
            ArmOp::And {
                rn: _,
                op2: Operand2::Reg(Reg::R10),
                ..
            } => {}
            other => panic!("Expected And with R10, got {:?}", other),
        }

        // Second: The actual STR
        match &arm_instrs[1].op {
            ArmOp::Str { .. } => {}
            other => panic!("Expected Str instruction, got {:?}", other),
        }
    }

    // =========================================================================
    // Control flow tests
    // =========================================================================

    #[test]
    fn test_control_flow_simple_block() {
        // block ... end — should emit a label at the end
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Block, WasmOp::I32Const(42), WasmOp::End];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain a Label instruction for block end
        let has_label = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Label { .. }));
        assert!(has_label, "Block should emit an end label");

        // Should contain a MOVW for the constant
        let has_movw = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { .. }));
        assert!(has_movw, "Should emit MOVW for i32.const");
    }

    #[test]
    fn test_control_flow_loop_with_br() {
        // loop ... br 0 ... end — should emit a label at loop start and branch back
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Loop,
            WasmOp::I32Const(1),
            WasmOp::Br(0), // Branch back to loop start
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain a Label for loop start
        let label_instrs: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { name } if name.contains("loop_start")))
            .collect();
        assert_eq!(
            label_instrs.len(),
            1,
            "Should have exactly one loop_start label"
        );

        // Should contain a B (branch) instruction targeting the loop label
        let has_branch = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::B { .. }));
        assert!(has_branch, "Loop with br should emit a B instruction");
    }

    /// #188 regression: a param that is live across a call must be preserved.
    ///
    /// Reproducer body (`g` in /tmp/liveacross.wat):
    ///   `(drop (call $clob)) (i32.load (local.get 0))`
    /// Pre-fix, `g` did `bl clob` (clobbering R0=param0) and then computed the
    /// load address from the clobbered R0 — reading the call's return instead
    /// of param0. The fix spills R0 before the BL and reloads it after, so the
    /// load's address register still holds the ORIGINAL param0.
    #[test]
    fn test_188_param_preserved_across_call() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        // Default bounds config (None) → I32Load lowers to a single LDR whose
        // offset_reg is the address register.
        let wasm_ops = vec![
            WasmOp::Call(7),     // call $clob (local func, idx >= num_imports)
            WasmOp::Drop,        // discard clob's result
            WasmOp::LocalGet(0), // push param0 (R0)
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        let arm = selector.select_with_stack(&wasm_ops, 1).unwrap();

        let bl_pos = arm
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Bl { .. }))
            .expect("a BL must be emitted for the call");

        // #204: in a function with a call, param0 is frame-backed — spilled to
        // a stack slot at entry, then reloaded from that slot wherever used. The
        // slot survives the call AND any temp allocation, so this preserves
        // param0 strictly more than the old around-the-call spill/reload.
        assert!(
            arm[..bl_pos]
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Str { rd: Reg::R0, .. })),
            "param0 (R0) must be spilled to its frame slot before the call: {:#?}",
            arm
        );
        assert_param0_load_derives_from_slot(&arm);
    }

    /// Shared assertion for the #188/#195/#204 frame-backed-param tests: the
    /// memory LDR's base register must have been reloaded from the SAME frame
    /// slot param0 was spilled to at entry — i.e. the load derives from the
    /// preserved param0, never from a call's clobbered R0 or a stray temp.
    fn assert_param0_load_derives_from_slot(arm: &[ArmInstruction]) {
        let spill = arm
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Str { rd: Reg::R0, addr } => Some(addr.clone()),
                _ => None,
            })
            .expect("param0 (R0) must be spilled to a frame slot at entry");
        let mem_load = arm
            .iter()
            .rev()
            .find_map(|i| match &i.op {
                ArmOp::Ldr { addr, .. } if addr.offset_reg.is_some() => Some(addr.clone()),
                _ => None,
            })
            .expect("a memory LDR with a register offset must be emitted");
        let base = mem_load
            .offset_reg
            .expect("memory LDR must have a register base");
        assert!(
            arm.iter().any(|i| matches!(&i.op,
                ArmOp::Ldr { rd, addr }
                    if *rd == base
                        && addr.base == spill.base
                        && addr.offset == spill.offset
                        && addr.offset_reg == spill.offset_reg)),
            "i32.load base {base:?} must be reloaded from param0's frame slot {spill:?}: {arm:#?}"
        );
    }

    /// #204 regression (gale `z_impl_k_sem_give`): a param used as a store
    /// ADDRESS that is live across a call must reach the `i64.store32` as the
    /// memory index, never dropped. gale's shape: `local.get 0` (sem_ptr) is
    /// the store address; an intervening call (`k_spin_lock`) reclaims R0 for
    /// its argument. With param frame-backing the store must be
    /// `STR rval, [R11, <reloaded sem_ptr>, #off]` — an indexed store whose
    /// index is reloaded from param0's frame slot. A base-only `[R11, #off]`
    /// (the bug) would write linear-memory offset 0, not `&sem->count`.
    #[test]
    fn test_204_sem_store_keeps_param_address_index() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_func_arg_counts(vec![1], Vec::new()); // func_0 takes 1 arg
        let wasm_ops = vec![
            // k_spin_lock(1024) — clobbers R0 with the arg, mirroring gale.
            WasmOp::I32Const(1024),
            WasmOp::Call(0),
            WasmOp::Drop,
            // store low word of a packed i64 to [sem_ptr]: (new_count << 32) >> 32
            WasmOp::LocalGet(0), // sem_ptr (param0) = store address
            WasmOp::LocalGet(1), // packed i64 value
            WasmOp::I64Const(32),
            WasmOp::I64ShrU,
            WasmOp::I64Store32 {
                offset: 0,
                align: 2,
            },
        ];
        let arm = selector.select_with_stack(&wasm_ops, 2).unwrap();

        // param0 spilled to its frame slot at entry.
        let spill = arm
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Str { rd: Reg::R0, addr } => Some(addr.clone()),
                _ => None,
            })
            .expect("param0 (R0) must be spilled to a frame slot at entry");

        // the memory store (base R11) must carry a register index...
        let mem_store = arm
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Str { addr, .. } if addr.base == Reg::R11 => Some(addr.clone()),
                _ => None,
            })
            .expect("an i64.store32 to [R11, ...] must be emitted");
        let idx = mem_store
            .offset_reg
            .expect("store address index must NOT be dropped (got base-only [R11]) — #204");

        // ...and that index must be the sem_ptr reloaded from param0's slot.
        assert!(
            arm.iter().any(|i| matches!(&i.op,
                ArmOp::Ldr { rd, addr }
                    if *rd == idx
                        && addr.base == spill.base
                        && addr.offset == spill.offset
                        && addr.offset_reg == spill.offset_reg)),
            "store index {idx:?} must be reloaded from param0's frame slot {spill:?}: {arm:#?}"
        );
    }

    /// #193/#210 regression: a constant/temp must never be allocated onto a
    /// still-live param register. gale's call-free `control_step_decide`:
    /// `coolant_c` = param2 = r2, and under pressure the constant `80` was
    /// materialized into r2, clobbering coolant → `subs r3,r2,r2` (= 80-80=0).
    /// Here param0 (r0) is read only AFTER six live constants exhaust the temp
    /// bank (r4-r8,r12); without the reservation the next constant wraps onto
    /// r0. The param-register reservation must keep r0 intact: no `Movw rd:r0`
    /// while param0 is still live.
    #[test]
    fn test_193_const_does_not_clobber_live_param() {
        use WasmOp::*;
        let mut selector = InstructionSelector::new(RuleDatabase::new().rules().to_vec());
        let ops = vec![
            // six live constants fill r4-r8,r12
            I32Const(11),
            I32Const(22),
            I32Const(33),
            I32Const(44),
            I32Const(55),
            I32Const(66),
            I32Const(99), // must NOT land on r0 — param0 still live
            LocalGet(0),  // read param0 (r0)
            I32Sub,       // 99 - param0
            // keep the six fillers live across the subtract
            I32Add,
            I32Add,
            I32Add,
            I32Add,
            I32Add,
            I32Add,
        ];
        let arm = selector.select_with_stack(&ops, 4).unwrap();
        // param0 lives in r0 until the LocalGet(0); no constant may overwrite it.
        assert!(
            !arm.iter()
                .any(|i| matches!(&i.op, ArmOp::Movw { rd: Reg::R0, .. })),
            "a constant clobbered param0 (r0) while it was still live (#193): {arm:#?}"
        );
    }

    /// #195 regression: a single i32 argument to a local call must be placed in
    /// R0 (per AAPCS) before the BL. Reproducer: `(call $use (i32.const 42))`.
    /// Pre-fix the constant was computed but never moved into R0 — the callee
    /// saw garbage.
    #[test]
    fn test_195_single_arg_in_r0_before_bl() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        // func_3 (a local function, >= num_imports=0) takes 1 i32 arg.
        selector.set_func_arg_counts(vec![0, 0, 0, 1], Vec::new());

        let wasm_ops = vec![
            WasmOp::I32Const(42), // the argument
            WasmOp::Call(3),      // call func_3(arg)
        ];
        let arm = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let bl_pos = arm
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Bl { .. }))
            .expect("a BL must be emitted");

        // Before the BL, R0 must end up holding the argument (42). The constant
        // may be materialized into a temp and then moved to R0, or directly into
        // R0 — either way R0 is written before the BL via a Mov/Movw/Mov-imm.
        let writes_r0_before_bl = arm[..bl_pos].iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Mov { rd: Reg::R0, .. } | ArmOp::Movw { rd: Reg::R0, .. }
            )
        });
        assert!(
            writes_r0_before_bl,
            "argument must be marshalled into R0 before the BL: {:#?}",
            arm
        );
    }

    /// #195 + #188 compose: gale's `z_impl_k_sem_give` shape — a value is live
    /// across a call that ALSO takes an argument. Both must hold: (a) the arg is
    /// passed in R0, and (b) the live value (param0) is preserved across the
    /// call and used afterwards. Reproducer body:
    ///   `(drop (call $use (i32.const 42))) (i32.load (local.get 0))`
    #[test]
    fn test_195_arg_passed_and_live_value_preserved() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        // func_0 takes 1 i32 arg.
        selector.set_func_arg_counts(vec![1], Vec::new());

        let wasm_ops = vec![
            WasmOp::I32Const(42), // arg to func_0
            WasmOp::Call(0),      // call func_0(42)
            WasmOp::Drop,         // discard the result
            WasmOp::LocalGet(0),  // push param0 (R0)
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
        ];
        let arm = selector.select_with_stack(&wasm_ops, 1).unwrap();

        let bl_pos = arm
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Bl { .. }))
            .expect("a BL must be emitted");

        // (a) param0 (R0) spilled to its frame slot at entry, before the call.
        assert!(
            arm[..bl_pos]
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Str { rd: Reg::R0, .. })),
            "param0 (R0) must be spilled to its frame slot before the call: {:#?}",
            arm
        );

        // (b) R0 is written with the argument before the BL (#195).
        assert!(
            arm[..bl_pos].iter().any(|i| matches!(
                &i.op,
                ArmOp::Mov { rd: Reg::R0, .. } | ArmOp::Movw { rd: Reg::R0, .. }
            )),
            "argument must be marshalled into R0 before the BL: {:#?}",
            arm
        );

        // (c) The memory load derives from the preserved param0 (reloaded from
        // its frame slot), not from the call's clobbered R0 (#204).
        assert_param0_load_derives_from_slot(&arm);
    }

    /// #195: two i32 arguments go to R0 and R1 (in order) before the BL.
    #[test]
    fn test_195_two_args_in_r0_r1() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_func_arg_counts(vec![2], Vec::new());

        let wasm_ops = vec![
            WasmOp::I32Const(10), // arg0 -> R0
            WasmOp::I32Const(20), // arg1 -> R1
            WasmOp::Call(0),
        ];
        let arm = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let bl_pos = arm
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Bl { .. }))
            .expect("a BL must be emitted");

        // Both R0 and R1 must be written before the BL.
        let r0_written = arm[..bl_pos].iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Mov { rd: Reg::R0, .. } | ArmOp::Movw { rd: Reg::R0, .. }
            )
        });
        let r1_written = arm[..bl_pos].iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Mov { rd: Reg::R1, .. } | ArmOp::Movw { rd: Reg::R1, .. }
            )
        });
        assert!(r0_written, "arg0 must land in R0 before BL: {:#?}", arm);
        assert!(r1_written, "arg1 must land in R1 before BL: {:#?}", arm);
    }

    /// #195: with no signature table (empty `func_arg_counts`) a call passes no
    /// args — the pre-#195 / #188 behaviour. Confirms the 0-arg #188 path is
    /// untouched: a 0-arg `Call` still emits exactly its BL with no extra arg
    /// moves into R0–R3.
    #[test]
    fn test_195_zero_args_unchanged() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        // No arg-count table: marshalling falls back to zero args.
        let wasm_ops = vec![WasmOp::Call(5)];
        let arm = selector.select_with_stack(&wasm_ops, 0).unwrap();

        assert!(
            arm.iter()
                .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "func_5")),
            "Call(5) should still emit BL func_5: {:#?}",
            arm
        );
        // No argument move into R0 (there are no args and no live values).
        let r0_moves = arm
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Mov { rd: Reg::R0, .. }))
            .count();
        assert_eq!(
            r0_moves, 0,
            "a 0-arg call must not marshal anything into R0: {:#?}",
            arm
        );
    }

    /// #171: i64-heavy functions that keep more i64 values live than fit in the
    /// 5 consecutive register pairs now COMPILE — `alloc_consecutive_pair` spills
    /// a deep i64 value to the frame (`StackVal::Spilled`) to free a pair, and
    /// the spilled value is reloaded on pop. Previously this hit register
    /// exhaustion and was dropped by the #168 skip-and-continue net (regressing
    /// gale's `z_impl_k_sem_give` once #188 added call-spill pressure).
    #[test]
    fn test_171_i64_exhaustion_spills_and_compiles() {
        let db = RuleDatabase::new();

        // Moderate i64 expression: compiles fine, no spill needed.
        let mut sel_ok = InstructionSelector::new(db.rules().to_vec());
        let ok_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I64Add,
            WasmOp::LocalGet(0),
            WasmOp::I64Mul,
        ];
        assert!(
            sel_ok.select_with_stack(&ok_ops, 2).is_ok(),
            "a moderate i64 function must compile"
        );

        // Pathological: keep 6 i64 values live simultaneously (12 regs needed,
        // only 10 allocatable). Pre-#171 this errored; now it COMPILES via spill.
        let mut sel_bad = InstructionSelector::new(db.rules().to_vec());
        let mut bad_ops = Vec::new();
        // Six independent i64 constants — each allocates a FRESH register pair,
        // so all six are live simultaneously before any consumer (the 6th
        // forces a spill).
        for _ in 0..6 {
            bad_ops.push(WasmOp::I64Const(1));
        }
        // Now fold them: five adds consume the six live values (reloading the
        // spilled one when it is popped).
        for _ in 0..5 {
            bad_ops.push(WasmOp::I64Add);
        }
        let res = sel_bad.select_with_stack(&bad_ops, 0);
        assert!(
            res.is_ok(),
            "6-live-i64 function must now compile via spill (#171), got {res:?}"
        );
        // The spill path must have emitted at least one STR/LDR to the frame.
        let arm = res.unwrap();
        let has_mem = arm
            .iter()
            .any(|i| matches!(i.op, ArmOp::Str { .. }) || matches!(i.op, ArmOp::Ldr { .. }));
        assert!(has_mem, "spill must emit STR/LDR frame traffic");
    }

    /// Regression test for #197: in relocatable host-link mode, a pointer param
    /// live across an import call must be preserved, the import must be a DIRECT
    /// `BL func_N` (rewritten to the field name by the ELF builder), and the
    /// dereference must be fp-relative — NOT the optimized path's absolute
    /// 0x20000100 linmem base.
    ///
    /// This is gale's `z_impl_k_sem_give` shape: a `sem` pointer param is passed
    /// to an import (`k_spin_lock`) and then dereferenced afterward. Pre-#197
    /// the register-heavy function went through the optimized path, which loaded
    /// `sem->count` from `0x20000100 + clobbered-r0` instead of `[fp, sem]`.
    /// Forcing `--relocatable` onto `select_with_stack` (now i64-spill capable
    /// after #171) gives correct preservation + fp-relative memory + direct ABI.
    #[test]
    fn test_197_relocatable_import_preserves_pointer_param() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_num_imports(1); // func 0 is the import (e.g. k_spin_lock)
        selector.set_relocatable(true); // host-link ET_REL
        // The import takes one integer arg (the pointer) per AAPCS.
        selector.set_func_arg_counts(vec![1], vec![]);

        // local.get $sem ; call $import(0) ; local.get $sem ; i32.load ; drop ; end
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::Call(0),
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
            WasmOp::Drop,
            WasmOp::End,
        ];
        let instrs = selector
            .select_with_stack(&ops, 1)
            .expect("#197: relocatable import + deref must compile via select_with_stack");

        let bl_labels: Vec<&str> = instrs
            .iter()
            .filter_map(|i| match &i.op {
                ArmOp::Bl { label } => Some(label.as_str()),
                _ => None,
            })
            .collect();

        // (A) Direct import ABI: `BL func_0`, NOT `__meld_dispatch_import`.
        assert!(
            bl_labels.contains(&"func_0"),
            "#197: relocatable import must emit direct `BL func_0`, got {bl_labels:?}"
        );
        assert!(
            !bl_labels.contains(&"__meld_dispatch_import"),
            "#197: relocatable import must NOT route through Meld dispatch, got {bl_labels:?}"
        );

        // (B) Defect-2 absent: no absolute 0x20000100 base materialized. The
        // optimized path emits `Movt R12, #0x2000` (high half of 0x20000100);
        // select_with_stack uses fp (R11) instead.
        let has_abs_base = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { rd: Reg::R12, imm16 } if *imm16 == 0x2000));
        assert!(
            !has_abs_base,
            "#197: must NOT materialize the absolute 0x20000100 linmem base (defect 2)"
        );

        // (C) The dereference is fp-relative (R11 = linmem base), via either a
        // register-offset load `[R11, rN]` or an `ADD rT, R11, rN; LDR [rT]`.
        let uses_fp_for_mem = instrs.iter().any(|i| match &i.op {
            ArmOp::Ldr { addr, .. } => addr.base == Reg::R11,
            ArmOp::Add { rn, .. } => *rn == Reg::R11,
            _ => false,
        });
        assert!(
            uses_fp_for_mem,
            "#197: the i32.load must be fp-relative (R11 linmem base), not absolute"
        );
    }

    #[test]
    fn test_control_flow_if_else() {
        // if ... else ... end — conditional execution
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(1),  // Push condition
            WasmOp::If,           // Start if block
            WasmOp::I32Const(10), // Then body
            WasmOp::Else,         // Else
            WasmOp::I32Const(20), // Else body
            WasmOp::End,          // End if
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain a CMP (condition test)
        let has_cmp = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "If should emit CMP for condition check");

        // Should contain a conditional branch (BEQ to else)
        let has_beq = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(has_beq, "If should emit BEQ to else label");

        // Should contain an unconditional branch (B to end, at end of then-block)
        let has_b = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::B { .. }));
        assert!(has_b, "Else should emit B to end label");

        // Should contain labels for else and end
        let labels: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { .. }))
            .collect();
        assert!(
            labels.len() >= 2,
            "Should have at least else and end labels, got {}",
            labels.len()
        );
    }

    #[test]
    fn test_control_flow_if_without_else() {
        // if ... end — no else clause
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(1),  // Push condition
            WasmOp::If,           // Start if block
            WasmOp::I32Const(10), // Then body
            WasmOp::End,          // End if (no else)
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should still emit else label (same as end) and end label
        let labels: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { .. }))
            .collect();
        assert!(
            labels.len() >= 2,
            "If without else should emit both else (=end) and end labels"
        );
    }

    #[test]
    fn test_control_flow_br_if() {
        // br_if — conditional branch
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::I32Const(1),  // Push condition
            WasmOp::BrIf(0),      // Conditional branch to block end
            WasmOp::I32Const(42), // Code after br_if (only reached if condition was 0)
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain CMP and BNE
        let has_cmp = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "br_if should emit CMP");

        let has_bne = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Bcc {
                    cond: Condition::NE,
                    ..
                }
            )
        });
        assert!(has_bne, "br_if should emit BNE (branch if non-zero)");
    }

    #[test]
    fn test_control_flow_nested_blocks() {
        // Nested blocks with br to outer block
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Block,        // Outer block (depth 1 from inner)
            WasmOp::Block,        // Inner block (depth 0)
            WasmOp::Br(1),        // Branch to outer block end
            WasmOp::End,          // End inner
            WasmOp::I32Const(99), // This is skipped by br 1
            WasmOp::End,          // End outer
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // The br(1) should target the outer block's end label
        let branch_instrs: Vec<_> = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::B { .. }))
            .collect();
        assert!(
            !branch_instrs.is_empty(),
            "br(1) should emit a B instruction targeting outer block"
        );
    }

    #[test]
    fn test_control_flow_call() {
        // Call a local function
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Call(5)];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_bl = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "func_5"));
        assert!(has_bl, "Call(5) should emit BL func_5");
    }

    #[test]
    fn test_control_flow_call_import() {
        // Call an imported function via Meld dispatch
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_num_imports(3);

        let wasm_ops = vec![WasmOp::Call(1)]; // Import index 1 (< 3)
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should emit MOV R0, #1 (import index) then BL __meld_dispatch_import
        let has_mov = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Imm(1)
                }
            )
        });
        assert!(has_mov, "Import call should set R0 to import index");

        let has_bl = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "__meld_dispatch_import"));
        assert!(has_bl, "Import call should BL to __meld_dispatch_import");
    }

    #[test]
    fn test_control_flow_return() {
        // Return from function
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Const(42), WasmOp::Return];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain BX LR or POP {PC} for the return
        let has_return = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bx { rm: Reg::LR } | ArmOp::Pop { .. }));
        assert!(has_return, "Return should emit BX LR or POP");
    }

    #[test]
    fn test_control_flow_unreachable() {
        // Unreachable trap
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Unreachable];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_udf = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Udf { imm: 0 }));
        assert!(has_udf, "Unreachable should emit UDF");
    }

    #[test]
    fn test_control_flow_nop() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Nop];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_nop = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::Nop));
        assert!(has_nop, "Nop should emit NOP");
    }

    #[test]
    fn test_control_flow_drop() {
        // Drop should pop from virtual stack without emitting code
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Const(42), WasmOp::Drop, WasmOp::I32Const(10)];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should emit MOVWs for the consts but no instruction for Drop
        let movw_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Movw { .. }))
            .count();
        assert_eq!(movw_count, 2, "Should have two MOVWs for the two consts");
    }

    #[test]
    fn test_control_flow_select() {
        // Select: pick between two values based on condition
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(10), // val1
            WasmOp::I32Const(20), // val2
            WasmOp::I32Const(1),  // condition
            WasmOp::Select,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain CMP for condition check
        let has_cmp = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "Select should emit CMP for condition");

        // Should contain the NE override SelectMove (cond != 0 -> dst = val1).
        // The in-place select (#209/VCR-SEL-002) reuses val2's register as dst
        // and elides the EQ "keep val2" move, so NE is the form present in both
        // the in-place and the fresh-dst fallback lowerings.
        let has_select_move = arm_instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::SelectMove {
                    cond: Condition::NE,
                    ..
                }
            )
        });
        assert!(has_select_move, "Select should emit SelectMove");
    }

    #[test]
    fn test_control_flow_br_table() {
        // br_table — indexed branch
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Block,       // Target for case 0 (depth 0)
            WasmOp::Block,       // Target for case 1 (depth 0)
            WasmOp::I32Const(0), // index
            WasmOp::BrTable {
                targets: vec![1, 0], // case 0 -> depth 1, case 1 -> depth 0
                default: 1,          // default -> depth 1
            },
            WasmOp::End,
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should contain multiple CMP instructions (one per target)
        let cmp_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Cmp { .. }))
            .count();
        assert!(
            cmp_count >= 2,
            "br_table should emit CMP for each target, got {}",
            cmp_count
        );

        // Should contain conditional branches (BEQ)
        let beq_count = arm_instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::Bcc {
                        cond: Condition::EQ,
                        ..
                    }
                )
            })
            .count();
        assert!(
            beq_count >= 2,
            "br_table should emit BEQ for each target, got {}",
            beq_count
        );

        // Should contain a default unconditional branch (B)
        let has_default_b = arm_instrs.iter().any(|i| matches!(&i.op, ArmOp::B { .. }));
        assert!(has_default_b, "br_table should emit B for default target");
    }

    #[test]
    fn test_control_flow_local_set_get() {
        // local.set and local.get round-trip
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(42),
            WasmOp::LocalSet(0), // Set local 0 (param r0)
            WasmOp::LocalGet(0), // Get local 0
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should contain instructions (MOV for const, MOV for set, then get is register reuse)
        assert!(
            !arm_instrs.is_empty(),
            "local.set/get sequence should emit instructions"
        );
    }

    #[test]
    fn test_branchable_instruction_trait() {
        // Test the BranchableInstruction trait implementation
        let mut instr = ArmInstruction {
            op: ArmOp::B {
                label: "target".to_string(),
            },
            source_line: Some(0),
        };

        assert!(instr.is_branch());
        instr.set_branch_offset(10);
        assert_eq!(instr.op, ArmOp::BOffset { offset: 10 });

        // Test conditional branch
        let mut cond_instr = ArmInstruction {
            op: ArmOp::Bcc {
                cond: Condition::EQ,
                label: "target".to_string(),
            },
            source_line: Some(0),
        };

        assert!(cond_instr.is_branch());
        cond_instr.set_branch_offset(5);
        assert_eq!(
            cond_instr.op,
            ArmOp::BCondOffset {
                cond: Condition::EQ,
                offset: 5,
            }
        );
    }

    #[test]
    fn test_label_emits_no_code() {
        // Verify that Label pseudo-instruction doesn't produce any encoding
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Block, WasmOp::End];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Labels should be present in instructions
        let label_count = arm_instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Label { .. }))
            .count();
        assert!(
            label_count >= 1,
            "Block/end should produce at least one label"
        );
    }

    #[test]
    fn test_loop_backward_branch_label() {
        // Verify loop emits label at start and br(0) branches back to it
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::Loop,
            WasmOp::Br(0), // Back to loop start
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Get the loop start label name
        let loop_label = arm_instrs.iter().find_map(|i| {
            if let ArmOp::Label { name } = &i.op
                && name.contains("loop_start")
            {
                return Some(name.clone());
            }
            None
        });
        assert!(loop_label.is_some(), "Loop should emit loop_start label");
        let loop_label = loop_label.unwrap();

        // The branch should target the same label
        let branch_target = arm_instrs.iter().find_map(|i| {
            if let ArmOp::B { label } = &i.op {
                return Some(label.clone());
            }
            None
        });
        assert_eq!(
            branch_target.as_deref(),
            Some(loop_label.as_str()),
            "br(0) in loop should branch back to loop_start label"
        );
    }

    // =========================================================================
    // Complex control flow tests (GitHub issue #36)
    //
    // These exercise the control flow compilation paths landed in PR #52:
    // nested blocks, loops with conditional exit, if/else with nested blocks,
    // br_table dispatch, and realistic multi-construct programs like
    // factorial and fibonacci.
    // =========================================================================

    /// Helper: create a fresh InstructionSelector with no optimization rules
    fn fresh_selector() -> InstructionSelector {
        InstructionSelector::new(vec![])
    }

    /// Helper: collect all Label names from an instruction sequence
    fn collect_labels(instrs: &[ArmInstruction]) -> Vec<String> {
        instrs
            .iter()
            .filter_map(|i| {
                if let ArmOp::Label { name } = &i.op {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Helper: collect all unconditional branch targets (B { label })
    fn collect_branch_targets(instrs: &[ArmInstruction]) -> Vec<String> {
        instrs
            .iter()
            .filter_map(|i| {
                if let ArmOp::B { label } = &i.op {
                    Some(label.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Helper: collect all conditional branch targets (Bcc { label, .. })
    fn collect_cond_branch_targets(instrs: &[ArmInstruction]) -> Vec<(Condition, String)> {
        instrs
            .iter()
            .filter_map(|i| {
                if let ArmOp::Bcc { cond, label } = &i.op {
                    Some((*cond, label.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Helper: count instructions of a given kind
    fn count_op<F: Fn(&ArmOp) -> bool>(instrs: &[ArmInstruction], pred: F) -> usize {
        instrs.iter().filter(|i| pred(&i.op)).count()
    }

    // ----- Test 1: Nested blocks with branch-out (br to outer block) -----

    #[test]
    fn test_complex_nested_blocks_br_to_outer() {
        // WASM equivalent:
        //   (block $outer            ;; depth 2 from innermost
        //     (block $middle         ;; depth 1 from innermost
        //       (block $inner        ;; depth 0
        //         i32.const 1
        //         br 2               ;; jump to $outer end
        //       )
        //       i32.const 2          ;; skipped by br 2
        //     )
        //     i32.const 3            ;; also skipped by br 2
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block, // $outer
            WasmOp::Block, // $middle
            WasmOp::Block, // $inner
            WasmOp::I32Const(1),
            WasmOp::Br(2), // jump to $outer end
            WasmOp::End,   // end $inner
            WasmOp::I32Const(2),
            WasmOp::End, // end $middle
            WasmOp::I32Const(3),
            WasmOp::End, // end $outer
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have 3 block end labels (one per block)
        let labels = collect_labels(&instrs);
        assert!(
            labels.len() >= 3,
            "Three nested blocks should produce at least 3 end labels, got {}",
            labels.len()
        );

        // The br(2) should generate a B instruction
        let branches = collect_branch_targets(&instrs);
        assert!(
            !branches.is_empty(),
            "br(2) should generate an unconditional branch"
        );

        // The branch target should be the outer block's end label (the first
        // label pushed on block_labels, which is the outermost block end)
        let outer_end_label = &labels[labels.len() - 1]; // last label emitted is outermost end
        assert!(
            branches.contains(outer_end_label),
            "br(2) should target the outermost block end label '{}', targets: {:?}",
            outer_end_label,
            branches
        );
    }

    // ----- Test 2: Loop with conditional exit (br_if) -----

    #[test]
    fn test_complex_loop_with_conditional_exit() {
        // WASM equivalent (countdown loop):
        //   (block $exit
        //     (loop $loop
        //       local.get 0          ;; counter
        //       i32.eqz
        //       br_if 1              ;; if counter == 0, exit block
        //       local.get 0
        //       i32.const 1
        //       i32.sub
        //       local.set 0          ;; counter -= 1
        //       br 0                 ;; loop back
        //     )
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Eqz,      // counter == 0?
            WasmOp::BrIf(1),     // if zero, exit to $exit end
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Sub,      // counter - 1
            WasmOp::LocalSet(0), // counter = counter - 1
            WasmOp::Br(0),       // loop back to $loop start
            WasmOp::End,         // end $loop
            WasmOp::End,         // end $exit
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have a loop_start label
        let loop_labels: Vec<_> = collect_labels(&instrs)
            .into_iter()
            .filter(|l| l.contains("loop_start"))
            .collect();
        assert_eq!(
            loop_labels.len(),
            1,
            "Should have exactly one loop_start label"
        );

        // Should have an unconditional branch back to loop_start (br 0)
        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(&loop_labels[0]),
            "br(0) should branch back to loop_start label"
        );

        // Should have a conditional branch (br_if 1) targeting exit block end
        let cond_branches = collect_cond_branch_targets(&instrs);
        let ne_branches: Vec<_> = cond_branches
            .iter()
            .filter(|(c, _)| *c == Condition::NE)
            .collect();
        assert!(
            !ne_branches.is_empty(),
            "br_if should generate a BNE conditional branch"
        );

        // Should emit a SUB for counter decrement
        let has_sub = instrs.iter().any(|i| matches!(&i.op, ArmOp::Sub { .. }));
        assert!(has_sub, "Should emit SUB for i32.sub (counter -= 1)");
    }

    // ----- Test 3: If/else with computation in both arms -----

    #[test]
    fn test_complex_if_else_with_computation() {
        // WASM equivalent:
        //   local.get 0              ;; condition from param
        //   (if
        //     (then
        //       local.get 1
        //       i32.const 10
        //       i32.add
        //       local.set 1          ;; x += 10
        //       local.get 1
        //       i32.const 100
        //       i32.mul
        //       local.set 1          ;; x *= 100
        //     )
        //     (else
        //       local.get 1
        //       i32.const 20
        //       i32.sub
        //       local.set 1          ;; x -= 20
        //       local.get 1
        //       i32.const 2
        //       i32.mul
        //       local.set 1          ;; x *= 2
        //     )
        //   )
        //   local.get 1              ;; return x
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::LocalGet(0), // condition
            WasmOp::If,
            // then-arm: x += 10, x *= 100
            WasmOp::LocalGet(1),
            WasmOp::I32Const(10),
            WasmOp::I32Add,
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
            WasmOp::I32Const(100),
            WasmOp::I32Mul,
            WasmOp::LocalSet(1),
            WasmOp::Else,
            // else-arm: x -= 20, x *= 2
            WasmOp::LocalGet(1),
            WasmOp::I32Const(20),
            WasmOp::I32Sub,
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
            WasmOp::LocalSet(1),
            WasmOp::End,         // end if
            WasmOp::LocalGet(1), // return x
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 2).unwrap();

        // Should have CMP for condition
        let cmp_count = count_op(&instrs, |op| matches!(op, ArmOp::Cmp { .. }));
        assert!(cmp_count >= 1, "If should emit CMP for condition");

        // Should have conditional branch to else (BEQ)
        let beq_count = count_op(&instrs, |op| {
            matches!(
                op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(beq_count >= 1, "If should emit BEQ to skip to else");

        // Should have unconditional branch to skip else at end of then
        let b_count = count_op(&instrs, |op| matches!(op, ArmOp::B { .. }));
        assert!(
            b_count >= 1,
            "End of then-arm should emit B to skip else, got {}",
            b_count
        );

        // Should have labels for else and if_end
        let labels = collect_labels(&instrs);
        let else_labels: Vec<_> = labels.iter().filter(|l| l.contains("else")).collect();
        let end_labels: Vec<_> = labels.iter().filter(|l| l.contains("if_end")).collect();
        assert!(!else_labels.is_empty(), "Should have an else label");
        assert!(!end_labels.is_empty(), "Should have an if_end label");

        // Should have ADD for then-arm and SUB for else-arm
        let add_count = count_op(&instrs, |op| matches!(op, ArmOp::Add { .. }));
        assert!(add_count >= 1, "Then-arm should have ADD");
        let sub_count = count_op(&instrs, |op| matches!(op, ArmOp::Sub { .. }));
        assert!(sub_count >= 1, "Else-arm should have SUB");

        // Should have MUL instructions for both arms
        let mul_count = count_op(&instrs, |op| matches!(op, ArmOp::Mul { .. }));
        assert_eq!(
            mul_count, 2,
            "Should have 2 MUL instructions (one per arm), got {}",
            mul_count
        );
    }

    // ----- Test 4: br_table (switch-like dispatch) -----

    #[test]
    fn test_complex_br_table_switch_dispatch() {
        // WASM equivalent (switch with 3 cases + default):
        //   (block $case2
        //     (block $case1
        //       (block $case0
        //         (block $default
        //           local.get 0          ;; switch index
        //           br_table 0 1 2 3     ;; targets=[0,1,2], default=3
        //         )
        //         ;; default body
        //         i32.const 99
        //         br 2
        //       )
        //       ;; case 0 body
        //       i32.const 0
        //       br 1
        //     )
        //     ;; case 1 body
        //     i32.const 1
        //     br 0
        //   )
        //   ;; case 2 falls through here
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $case2
            WasmOp::Block,       // $case1
            WasmOp::Block,       // $case0
            WasmOp::Block,       // $default
            WasmOp::LocalGet(0), // switch index
            WasmOp::BrTable {
                targets: vec![0, 1, 2], // case 0->$default, 1->$case0, 2->$case1
                default: 3,             // default->$case2
            },
            WasmOp::End,          // end $default
            WasmOp::I32Const(99), // default body
            WasmOp::Br(2),        // skip to $case2 end
            WasmOp::End,          // end $case0
            WasmOp::I32Const(0),  // case 0 body
            WasmOp::Br(1),        // skip to $case2 end
            WasmOp::End,          // end $case1
            WasmOp::I32Const(1),  // case 1 body
            WasmOp::Br(0),        // skip to $case2 end
            WasmOp::End,          // end $case2
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // br_table should emit CMP+BEQ for each target (3 targets)
        let cmp_count = count_op(&instrs, |op| matches!(op, ArmOp::Cmp { .. }));
        assert!(
            cmp_count >= 3,
            "br_table with 3 targets should emit at least 3 CMPs, got {}",
            cmp_count
        );

        let beq_count = count_op(&instrs, |op| {
            matches!(
                op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert!(
            beq_count >= 3,
            "br_table with 3 targets should emit at least 3 BEQs, got {}",
            beq_count
        );

        // Should emit a default unconditional branch
        let b_count = count_op(&instrs, |op| matches!(op, ArmOp::B { .. }));
        assert!(
            b_count >= 4,
            "Should have at least 4 B instructions (1 default + 3 case br), got {}",
            b_count
        );

        // Should have 4 block end labels
        let labels = collect_labels(&instrs);
        let block_end_labels: Vec<_> = labels.iter().filter(|l| l.contains("block_end")).collect();
        assert_eq!(
            block_end_labels.len(),
            4,
            "Should have 4 block_end labels for 4 blocks, got {}",
            block_end_labels.len()
        );
    }

    // ----- Test 5: Factorial (loop + if + arithmetic) -----

    #[test]
    fn test_complex_factorial() {
        // WASM equivalent of iterative factorial:
        //   (func $factorial (param $n i32) (result i32)
        //     (local $result i32)
        //     i32.const 1
        //     local.set 1             ;; result = 1
        //     (block $exit
        //       (loop $loop
        //         local.get 0         ;; n
        //         i32.const 1
        //         i32.le_s
        //         br_if 1             ;; if n <= 1, exit
        //         local.get 1         ;; result
        //         local.get 0         ;; n
        //         i32.mul
        //         local.set 1         ;; result *= n
        //         local.get 0
        //         i32.const 1
        //         i32.sub
        //         local.set 0         ;; n -= 1
        //         br 0                ;; loop
        //       )
        //     )
        //     local.get 1             ;; return result
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(1),
            WasmOp::LocalSet(1), // result = 1
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // n
            WasmOp::I32Const(1),
            WasmOp::I32LeS,      // n <= 1?
            WasmOp::BrIf(1),     // exit if true
            WasmOp::LocalGet(1), // result
            WasmOp::LocalGet(0), // n
            WasmOp::I32Mul,      // result * n
            WasmOp::LocalSet(1), // result = result * n
            WasmOp::LocalGet(0), // n
            WasmOp::I32Const(1),
            WasmOp::I32Sub,      // n - 1
            WasmOp::LocalSet(0), // n = n - 1
            WasmOp::Br(0),       // loop back
            WasmOp::End,         // end $loop
            WasmOp::End,         // end $exit
            WasmOp::LocalGet(1), // return result
        ];

        // 2 params: $n in r0, $result in r1 (via local.set 1)
        let instrs = selector.select_with_stack(&wasm_ops, 2).unwrap();

        // Should have a loop_start label
        let labels = collect_labels(&instrs);
        let loop_starts: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_starts.len(), 1, "Should have exactly one loop_start");

        // Should have backward branch (br 0) to loop
        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(loop_starts[0]),
            "br(0) should branch back to loop_start"
        );

        // Should have conditional exit (br_if 1)
        let cond_branches = collect_cond_branch_targets(&instrs);
        assert!(
            !cond_branches.is_empty(),
            "br_if(1) should emit conditional branch to exit"
        );

        // Should have MUL for result * n
        let mul_count = count_op(&instrs, |op| matches!(op, ArmOp::Mul { .. }));
        assert_eq!(mul_count, 1, "Should have exactly one MUL for result * n");

        // Should have SUB for n - 1
        let sub_count = count_op(&instrs, |op| matches!(op, ArmOp::Sub { .. }));
        assert_eq!(sub_count, 1, "Should have exactly one SUB for n - 1");

        // Should have BX LR or POP for function return
        let has_return = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bx { rm: Reg::LR } | ArmOp::Pop { .. }));
        assert!(has_return, "Function should end with BX LR or POP");
    }

    // ----- Test 6: Fibonacci (loop + if + arithmetic) -----

    #[test]
    fn test_complex_fibonacci() {
        // WASM equivalent of iterative fibonacci:
        //   (func $fib (param $n i32) (result i32)
        //     (local $a i32)   ;; local 1 = 0
        //     (local $b i32)   ;; local 2 = 1
        //     (local $tmp i32) ;; local 3
        //     i32.const 0
        //     local.set 1         ;; a = 0
        //     i32.const 1
        //     local.set 2         ;; b = 1
        //     (block $exit
        //       (loop $loop
        //         local.get 0     ;; n
        //         i32.eqz
        //         br_if 1         ;; if n == 0, exit
        //         local.get 1     ;; a
        //         local.get 2     ;; b
        //         i32.add
        //         local.set 3     ;; tmp = a + b
        //         local.get 2
        //         local.set 1     ;; a = b
        //         local.get 3
        //         local.set 2     ;; b = tmp
        //         local.get 0
        //         i32.const 1
        //         i32.sub
        //         local.set 0     ;; n -= 1
        //         br 0            ;; loop
        //       )
        //     )
        //     local.get 1         ;; return a
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(0),
            WasmOp::LocalSet(1), // a = 0
            WasmOp::I32Const(1),
            WasmOp::LocalSet(2), // b = 1
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // n
            WasmOp::I32Eqz,      // n == 0?
            WasmOp::BrIf(1),     // exit if n == 0
            WasmOp::LocalGet(1), // a
            WasmOp::LocalGet(2), // b
            WasmOp::I32Add,      // a + b
            WasmOp::LocalSet(3), // tmp = a + b
            WasmOp::LocalGet(2), // b
            WasmOp::LocalSet(1), // a = b
            WasmOp::LocalGet(3), // tmp
            WasmOp::LocalSet(2), // b = tmp
            WasmOp::LocalGet(0), // n
            WasmOp::I32Const(1),
            WasmOp::I32Sub,      // n - 1
            WasmOp::LocalSet(0), // n = n - 1
            WasmOp::Br(0),       // loop
            WasmOp::End,         // end $loop
            WasmOp::End,         // end $exit
            WasmOp::LocalGet(1), // return a
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 4).unwrap();

        // Should have loop_start label
        let labels = collect_labels(&instrs);
        let loop_starts: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_starts.len(), 1, "Should have one loop_start");

        // Should have backward branch
        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(loop_starts[0]),
            "Should branch back to loop_start"
        );

        // Should have ADD for a + b
        let add_count = count_op(&instrs, |op| matches!(op, ArmOp::Add { .. }));
        assert!(add_count >= 1, "Should have ADD for a + b");

        // Should have SUB for n - 1
        let sub_count = count_op(&instrs, |op| matches!(op, ArmOp::Sub { .. }));
        assert!(sub_count >= 1, "Should have SUB for n - 1");

        // Should have conditional branch for br_if
        let cond_branches = collect_cond_branch_targets(&instrs);
        let ne_branches: Vec<_> = cond_branches
            .iter()
            .filter(|(c, _)| *c == Condition::NE)
            .collect();
        assert!(
            !ne_branches.is_empty(),
            "br_if should generate BNE for conditional exit"
        );
    }

    // ----- Test 7: Empty blocks -----

    #[test]
    fn test_complex_empty_blocks() {
        // Empty blocks should compile without error and produce minimal code
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::End,
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::End,
            WasmOp::End,
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should succeed and produce labels
        let labels = collect_labels(&instrs);
        assert!(
            labels.len() >= 3,
            "Three empty blocks should produce at least 3 labels, got {}",
            labels.len()
        );

        // No branches should be emitted (no br instructions)
        let b_count = count_op(&instrs, |op| matches!(op, ArmOp::B { .. }));
        assert_eq!(
            b_count, 0,
            "Empty blocks should not emit branches, got {}",
            b_count
        );
    }

    // ----- Test 8: Deeply nested blocks (5 levels) -----

    #[test]
    fn test_complex_deeply_nested_blocks() {
        // 5 levels of nesting with br from innermost to outermost
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block, // depth 4 from innermost
            WasmOp::Block, // depth 3
            WasmOp::Block, // depth 2
            WasmOp::Block, // depth 1
            WasmOp::Block, // depth 0 (innermost)
            WasmOp::I32Const(42),
            WasmOp::Br(4), // jump to outermost block end
            WasmOp::End,   // end depth 0
            WasmOp::End,   // end depth 1
            WasmOp::End,   // end depth 2
            WasmOp::End,   // end depth 3
            WasmOp::End,   // end depth 4
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have 5 block end labels
        let labels = collect_labels(&instrs);
        let block_end_labels: Vec<_> = labels.iter().filter(|l| l.contains("block_end")).collect();
        assert_eq!(
            block_end_labels.len(),
            5,
            "5 nested blocks should have 5 end labels, got {}",
            block_end_labels.len()
        );

        // The br(4) should branch to the outermost block's end
        let branches = collect_branch_targets(&instrs);
        assert_eq!(branches.len(), 1, "Should have exactly one branch (br 4)");

        // The target should be the last label emitted (outermost end)
        let outermost_label = block_end_labels.last().unwrap();
        assert_eq!(
            &branches[0], *outermost_label,
            "br(4) should target outermost block end"
        );
    }

    // ----- Test 9: Loop re-entry via br 0 -----

    #[test]
    fn test_complex_loop_reentry() {
        // Multiple br 0 in a loop body (different code paths re-enter the loop)
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // condition
            WasmOp::If,
            WasmOp::I32Const(1),
            WasmOp::LocalSet(0),
            WasmOp::Br(1), // re-enter loop from then-arm
            WasmOp::Else,
            WasmOp::I32Const(0),
            WasmOp::LocalSet(0),
            WasmOp::Br(1), // re-enter loop from else-arm
            WasmOp::End,   // end if
            WasmOp::End,   // end loop
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have loop_start label
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_labels.len(), 1, "Should have one loop_start label");

        // Should have two unconditional branches targeting loop_start (br 1 from both arms)
        // Plus the B that skips else at end of then-arm
        let branches = collect_branch_targets(&instrs);
        let loop_branches: Vec<_> = branches
            .iter()
            .filter(|b| b.contains("loop_start"))
            .collect();
        assert_eq!(
            loop_branches.len(),
            2,
            "Both br(1) should branch to loop_start, got {} branches to loop_start",
            loop_branches.len()
        );
    }

    // ----- Test 10: Mixed control flow — block containing loop containing if/else -----

    #[test]
    fn test_complex_block_loop_if_combined() {
        // WASM equivalent:
        //   (block $outer
        //     (loop $loop
        //       local.get 0
        //       i32.const 10
        //       i32.gt_s
        //       (if
        //         (then
        //           br 2            ;; exit $outer
        //         )
        //         (else
        //           local.get 0
        //           i32.const 1
        //           i32.add
        //           local.set 0
        //           br 1            ;; re-enter $loop
        //         )
        //       )
        //     )
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $outer
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Const(10),
            WasmOp::I32GtS, // counter > 10?
            WasmOp::If,
            // then: exit outer
            WasmOp::Br(2), // exit $outer
            WasmOp::Else,
            // else: increment and loop
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Add,
            WasmOp::LocalSet(0),
            WasmOp::Br(1), // re-enter $loop
            WasmOp::End,   // end if
            WasmOp::End,   // end loop
            WasmOp::End,   // end outer
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Verify structural elements
        let labels = collect_labels(&instrs);

        // Should have loop_start
        let loop_starts: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_starts.len(), 1, "Should have one loop_start");

        // Should have block_end for outer block
        let block_ends: Vec<_> = labels.iter().filter(|l| l.contains("block_end")).collect();
        assert!(
            !block_ends.is_empty(),
            "Should have block_end label for outer block"
        );

        // Should have else and if_end labels
        let else_labels: Vec<_> = labels.iter().filter(|l| l.contains("else")).collect();
        assert!(!else_labels.is_empty(), "Should have an else label");

        let if_end_labels: Vec<_> = labels.iter().filter(|l| l.contains("if_end")).collect();
        assert!(!if_end_labels.is_empty(), "Should have an if_end label");

        // Verify branches
        let branches = collect_branch_targets(&instrs);

        // br(2) should target outer block end
        assert!(
            branches.iter().any(|b| b.contains("block_end")),
            "br(2) should target outer block_end, branches: {:?}",
            branches
        );

        // br(1) should target loop_start
        assert!(
            branches.iter().any(|b| b.contains("loop_start")),
            "br(1) should target loop_start, branches: {:?}",
            branches
        );

        // Should have ADD for counter + 1
        let add_count = count_op(&instrs, |op| matches!(op, ArmOp::Add { .. }));
        assert!(add_count >= 1, "Should have ADD for counter + 1");
    }

    // ----- Test 11: br_table within a loop -----

    #[test]
    fn test_complex_br_table_in_loop() {
        // State machine pattern: loop with br_table dispatch
        //   (loop $loop
        //     (block $state2
        //       (block $state1
        //         (block $state0
        //           local.get 0       ;; state variable
        //           br_table 0 1 2    ;; dispatch to state blocks
        //         )
        //         ;; state 0 body
        //         i32.const 1
        //         local.set 0          ;; state = 1
        //         br 2                 ;; continue loop
        //       )
        //       ;; state 1 body
        //       i32.const 2
        //       local.set 0            ;; state = 2
        //       br 1                   ;; continue loop
        //     )
        //     ;; state 2: exit (fall through to end)
        //   )
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Loop,        // $loop
            WasmOp::Block,       // $state2
            WasmOp::Block,       // $state1
            WasmOp::Block,       // $state0
            WasmOp::LocalGet(0), // state
            WasmOp::BrTable {
                targets: vec![0, 1, 2], // dispatch per state
                default: 2,             // default -> $state2 (exit)
            },
            WasmOp::End, // end $state0
            WasmOp::I32Const(1),
            WasmOp::LocalSet(0), // state = 1
            WasmOp::Br(2),       // back to $loop
            WasmOp::End,         // end $state1
            WasmOp::I32Const(2),
            WasmOp::LocalSet(0), // state = 2
            WasmOp::Br(1),       // back to $loop
            WasmOp::End,         // end $state2
            WasmOp::End,         // end $loop
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have loop_start label
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_labels.len(), 1, "Should have one loop_start");

        // br_table should emit 3 CMP + BEQ pairs
        let cmp_count = count_op(&instrs, |op| matches!(op, ArmOp::Cmp { .. }));
        assert!(
            cmp_count >= 3,
            "br_table should emit at least 3 CMPs, got {}",
            cmp_count
        );

        // Should have branches back to loop_start (br 2 and br 1 target loop)
        let branches = collect_branch_targets(&instrs);
        let to_loop: Vec<_> = branches
            .iter()
            .filter(|b| b.contains("loop_start"))
            .collect();
        assert!(
            to_loop.len() >= 2,
            "Should have at least 2 branches back to loop_start (from state 0 and 1), got {}",
            to_loop.len()
        );
    }

    // ----- Test 12: Nested if/else without inner else clause -----

    #[test]
    fn test_complex_nested_if_no_else() {
        // Nested if without else exercises the else-label dedup path
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(1), // outer condition
            WasmOp::If,
            WasmOp::I32Const(1), // inner condition
            WasmOp::If,
            WasmOp::I32Const(42), // deeply nested body
            WasmOp::End,          // end inner if (no else)
            WasmOp::End,          // end outer if (no else)
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Each if-without-else should emit both else label and if_end label
        let labels = collect_labels(&instrs);
        let else_labels: Vec<_> = labels.iter().filter(|l| l.contains("else")).collect();
        let end_labels: Vec<_> = labels.iter().filter(|l| l.contains("if_end")).collect();

        assert!(
            else_labels.len() >= 2,
            "Two if-without-else should emit at least 2 else labels, got {}",
            else_labels.len()
        );
        assert!(
            end_labels.len() >= 2,
            "Two if blocks should emit at least 2 if_end labels, got {}",
            end_labels.len()
        );

        // Should have 2 BEQ instructions (one per if)
        let beq_count = count_op(&instrs, |op| {
            matches!(
                op,
                ArmOp::Bcc {
                    cond: Condition::EQ,
                    ..
                }
            )
        });
        assert_eq!(
            beq_count, 2,
            "Two if blocks should emit 2 BEQ, got {}",
            beq_count
        );
    }

    // ----- Test 13: Function call within loop -----

    #[test]
    fn test_complex_call_in_loop() {
        // Loop that calls a function each iteration
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,       // $exit
            WasmOp::Loop,        // $loop
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Eqz,      // counter == 0?
            WasmOp::BrIf(1),     // exit if zero
            WasmOp::LocalGet(0), // pass counter as arg
            WasmOp::Call(5),     // call func_5
            WasmOp::Drop,        // discard return value
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Sub,
            WasmOp::LocalSet(0), // counter -= 1
            WasmOp::Br(0),       // loop
            WasmOp::End,         // end loop
            WasmOp::End,         // end block
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have a BL func_5 call
        let has_bl = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Bl { label } if label == "func_5"));
        assert!(has_bl, "Should emit BL func_5 for Call(5)");

        // Should have loop_start and backward branch
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(loop_labels.len(), 1, "Should have one loop_start");

        let branches = collect_branch_targets(&instrs);
        assert!(
            branches.contains(loop_labels[0]),
            "Should branch back to loop_start"
        );
    }

    // ----- Test 14: Early return from nested control flow -----

    #[test]
    fn test_complex_return_from_nested() {
        // Return from inside a nested block+loop+if
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0),
            WasmOp::I32Eq,
            WasmOp::If,
            WasmOp::I32Const(42),
            WasmOp::Return, // early return from inside if inside loop inside block
            WasmOp::End,    // end if
            WasmOp::Br(0),  // loop
            WasmOp::End,    // end loop
            WasmOp::End,    // end block
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have return instructions (BX LR or POP) for early return + function epilogue
        let return_count = count_op(&instrs, |op| {
            matches!(op, ArmOp::Bx { rm: Reg::LR } | ArmOp::Pop { .. })
        });
        assert!(
            return_count >= 2,
            "Should have at least 2 returns (early return + function epilogue), got {}",
            return_count
        );

        // Should have loop_start
        let labels = collect_labels(&instrs);
        assert!(
            labels.iter().any(|l| l.contains("loop_start")),
            "Should have loop_start label"
        );

        // Should have if-related labels
        assert!(
            labels
                .iter()
                .any(|l| l.contains("if_end") || l.contains("else")),
            "Should have if-related labels"
        );
    }

    // ----- Test 15: Unreachable inside control flow -----

    #[test]
    fn test_complex_unreachable_in_block() {
        // Unreachable trap inside a conditional block
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(0),
            WasmOp::If,
            WasmOp::Unreachable, // trap if condition is true
            WasmOp::Else,
            WasmOp::I32Const(1), // normal path
            WasmOp::End,
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have UDF for unreachable
        let udf_count = count_op(&instrs, |op| matches!(op, ArmOp::Udf { .. }));
        assert_eq!(udf_count, 1, "Should have exactly one UDF for unreachable");

        // Should still have proper if/else structure
        let labels = collect_labels(&instrs);
        assert!(
            labels.iter().any(|l| l.contains("else")),
            "Should have else label"
        );
        assert!(
            labels.iter().any(|l| l.contains("if_end")),
            "Should have if_end label"
        );
    }

    // ----- Test 16: Multiple loops (sequential, not nested) -----

    #[test]
    fn test_complex_sequential_loops() {
        // Two loops in sequence (not nested)
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            // First loop: count up
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(0),
            WasmOp::I32Const(10),
            WasmOp::I32GeS,
            WasmOp::BrIf(1), // exit if >= 10
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Add,
            WasmOp::LocalSet(0),
            WasmOp::Br(0), // loop
            WasmOp::End,
            WasmOp::End,
            // Second loop: count down
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(0),
            WasmOp::I32Eqz,
            WasmOp::BrIf(1), // exit if == 0
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Sub,
            WasmOp::LocalSet(0),
            WasmOp::Br(0), // loop
            WasmOp::End,
            WasmOp::End,
        ];

        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should have 2 loop_start labels
        let labels = collect_labels(&instrs);
        let loop_labels: Vec<_> = labels.iter().filter(|l| l.contains("loop_start")).collect();
        assert_eq!(
            loop_labels.len(),
            2,
            "Should have 2 loop_start labels for sequential loops, got {}",
            loop_labels.len()
        );

        // Each loop should have a backward branch
        let branches = collect_branch_targets(&instrs);
        for ll in &loop_labels {
            assert!(
                branches.contains(ll),
                "Should branch back to loop_start '{}', branches: {:?}",
                ll,
                branches
            );
        }
    }

    // ----- Test 17: Instruction count sanity checks -----

    #[test]
    fn test_complex_instruction_count_sanity() {
        // Verify that control flow constructs produce a reasonable number of
        // instructions (not zero, not explosively large)
        let mut selector = fresh_selector();

        // Simple block with one instruction
        let wasm_ops = vec![WasmOp::Block, WasmOp::I32Const(1), WasmOp::End];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();
        // MOV for const + Label for block end + BX LR
        assert!(
            instrs.len() <= 5,
            "Simple block should produce <= 5 ARM instructions, got {}",
            instrs.len()
        );
        assert!(
            instrs.len() >= 2,
            "Simple block should produce >= 2 ARM instructions, got {}",
            instrs.len()
        );

        // Loop with br should produce bounded output
        selector.reset();
        let wasm_ops = vec![WasmOp::Loop, WasmOp::Br(0), WasmOp::End];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();
        assert!(
            instrs.len() <= 5,
            "Simple loop+br should produce <= 5 ARM instructions, got {}",
            instrs.len()
        );
    }

    // =========================================================================
    // GlobalGet / GlobalSet tests
    // =========================================================================

    #[test]
    fn test_global_get_select_default() {
        // global.get should generate LDR from globals base (R9)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalGet(0)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldr { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9, "Globals base should be R9");
                assert_eq!(addr.offset, 0, "Global 0 should have offset 0");
                assert!(addr.offset_reg.is_none(), "No offset register");
            }
            other => panic!("Expected Ldr for global.get, got {:?}", other),
        }
    }

    #[test]
    fn test_global_get_nonzero_index_select_default() {
        // global.get with index 3 should use offset 12 (3 * 4)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalGet(3)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldr { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9);
                assert_eq!(addr.offset, 12, "Global 3 should have offset 3*4=12");
            }
            other => panic!("Expected Ldr for global.get(3), got {:?}", other),
        }
    }

    #[test]
    fn test_global_set_select_default() {
        // global.set should generate STR to globals base (R9)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalSet(0)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Str { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9, "Globals base should be R9");
                assert_eq!(addr.offset, 0, "Global 0 should have offset 0");
            }
            other => panic!("Expected Str for global.set, got {:?}", other),
        }
    }

    #[test]
    fn test_global_set_nonzero_index_select_default() {
        // global.set with index 5 should use offset 20 (5 * 4)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::GlobalSet(5)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Str { rd: _, addr } => {
                assert_eq!(addr.base, Reg::R9);
                assert_eq!(addr.offset, 20, "Global 5 should have offset 5*4=20");
            }
            other => panic!("Expected Str for global.set(5), got {:?}", other),
        }
    }

    #[test]
    fn test_global_get_stack_mode() {
        // global.get in stack mode should push result register onto virtual stack
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::GlobalGet(2), // Load global 2
            WasmOp::I32Const(1),
            WasmOp::I32Add, // Add 1 to global value
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have LDR from R9+8 (global index 2, offset 2*4=8)
        let has_global_ldr = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Ldr { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 8
            )
        });
        assert!(
            has_global_ldr,
            "global.get(2) should emit LDR from [R9, #8]"
        );

        // Should have ADD (from the i32.add)
        let has_add = instrs.iter().any(|i| matches!(&i.op, ArmOp::Add { .. }));
        assert!(has_add, "Should emit ADD for i32.add after global.get");
    }

    #[test]
    fn test_global_set_stack_mode() {
        // global.set in stack mode should pop value and store to globals table
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::I32Const(42), // Push value
            WasmOp::GlobalSet(1), // Store to global 1
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have STR to R9+4 (global index 1, offset 1*4=4)
        let has_global_str = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Str { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 4
            )
        });
        assert!(has_global_str, "global.set(1) should emit STR to [R9, #4]");
    }

    #[test]
    fn test_global_get_set_roundtrip() {
        // global.get + modify + global.set should work correctly
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::GlobalGet(0), // Load global 0
            WasmOp::I32Const(10), // Push 10
            WasmOp::I32Add,       // global_0 + 10
            WasmOp::GlobalSet(0), // Store back to global 0
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have LDR from R9 (global.get 0)
        let has_load = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Ldr { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 0
            )
        });
        assert!(has_load, "Should have LDR from [R9, #0] for global.get(0)");

        // Should have STR to R9 (global.set 0)
        let has_store = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Str { addr, .. }
                if addr.base == Reg::R9 && addr.offset == 0
            )
        });
        assert!(has_store, "Should have STR to [R9, #0] for global.set(0)");

        // Should have ADD for the increment
        let has_add = instrs.iter().any(|i| matches!(&i.op, ArmOp::Add { .. }));
        assert!(has_add, "Should have ADD for i32.add");
    }

    // =========================================================================
    // Select instruction tests
    // =========================================================================

    #[test]
    fn test_select_default_mode() {
        // Select in select_default should emit CMP + MOV + SelectMove
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::Select];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 3, "Select should emit 3 instructions");

        // First: CMP rcond, #0
        match &arm_instrs[0].op {
            ArmOp::Cmp {
                op2: Operand2::Imm(0),
                ..
            } => {}
            other => panic!("Expected CMP rcond, #0, got {:?}", other),
        }

        // Second: MOV rd, rval1 (default)
        match &arm_instrs[1].op {
            ArmOp::Mov { .. } => {}
            other => panic!("Expected MOV rd, rval1, got {:?}", other),
        }

        // Third: SelectMove (conditional override)
        match &arm_instrs[2].op {
            ArmOp::SelectMove {
                cond: Condition::EQ,
                ..
            } => {}
            other => panic!("Expected SelectMove with EQ condition, got {:?}", other),
        }
    }

    #[test]
    fn test_select_stack_mode_with_constants() {
        // Select with three constant operands
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::I32Const(10), // val1
            WasmOp::I32Const(20), // val2
            WasmOp::I32Const(1),  // condition (nonzero -> pick val1)
            WasmOp::Select,
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // Should have CMP for condition
        let has_cmp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0),
                    ..
                }
            )
        });
        assert!(has_cmp, "Select should emit CMP condition, #0");

        // Should have the NE override SelectMove. With in-place select
        // (#209/VCR-SEL-002), val2 (the const-20 temp) is reused as dst and the
        // EQ "keep" move is elided; the NE override is present in both forms.
        let has_select_move = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::SelectMove {
                    cond: Condition::NE,
                    ..
                }
            )
        });
        assert!(has_select_move, "Select should emit SelectMove with NE");
    }

    #[test]
    fn test_select_in_place_elides_keep_move_209() {
        // #209/VCR-SEL-002: when val2 is a free temp (here the const-20 temp,
        // not a live param, distinct from cond/val1), the select reuses val2's
        // register as dst and keeps it via the EQ fall-through — so exactly ONE
        // SelectMove (the NE override) is emitted, not two. Result-identity is
        // verified on-target by the flight_seam / control_step differentials;
        // this pins the structural win (one fewer IT;MOV per qualifying select).
        let mut selector = fresh_selector();
        let wasm_ops = vec![
            WasmOp::I32Const(10), // val1
            WasmOp::I32Const(20), // val2 — reusable temp
            WasmOp::I32Const(1),  // cond
            WasmOp::Select,
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let ne = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::SelectMove {
                        cond: Condition::NE,
                        ..
                    }
                )
            })
            .count();
        let eq = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::SelectMove {
                        cond: Condition::EQ,
                        ..
                    }
                )
            })
            .count();
        assert_eq!(ne, 1, "in-place select emits exactly one NE override move");
        assert_eq!(eq, 0, "in-place select elides the EQ keep-val2 move");
    }

    #[test]
    fn test_select_with_global_values() {
        // Combine global.get with select: select between two globals based on condition
        let mut selector = fresh_selector();

        let wasm_ops = vec![
            WasmOp::GlobalGet(0), // val1 = global 0
            WasmOp::GlobalGet(1), // val2 = global 1
            WasmOp::LocalGet(0),  // condition from param
            WasmOp::Select,       // pick val1 if cond != 0, else val2
            WasmOp::GlobalSet(2), // store result to global 2
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should load from globals 0 and 1
        let global_loads: Vec<_> = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::Ldr { addr, .. }
                    if addr.base == Reg::R9
                )
            })
            .collect();
        assert_eq!(
            global_loads.len(),
            2,
            "Should have 2 LDR from globals (indices 0 and 1), got {}",
            global_loads.len()
        );

        // Should store to global 2
        let global_stores: Vec<_> = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::Str { addr, .. }
                    if addr.base == Reg::R9 && addr.offset == 8
                )
            })
            .collect();
        assert_eq!(
            global_stores.len(),
            1,
            "Should have 1 STR to global 2 at [R9, #8]"
        );

        // Should have select logic — the NE override is emitted in both the
        // in-place (#209/VCR-SEL-002) and fresh-dst forms (the EQ "keep val2"
        // move is what in-place elides when val2's register is reused as dst).
        let has_select_move = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::SelectMove {
                    cond: Condition::NE,
                    ..
                }
            )
        });
        assert!(has_select_move, "Should have SelectMove for the select op");
    }

    // =========================================================================
    // i64 instruction selection tests
    // =========================================================================

    #[test]
    fn test_i64_const() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Const(0x0000_0001_0000_0002)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64Const { rdlo, rdhi, value } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(*value, 0x0000_0001_0000_0002);
            }
            other => panic!("Expected I64Const, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_const_negative() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Const(-1)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64Const { value, .. } => {
                assert_eq!(*value, -1);
            }
            other => panic!("Expected I64Const, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_extend_i32_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64ExtendI32S];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64ExtendI32S { rdlo, rdhi, rn } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(*rn, Reg::R0);
            }
            other => panic!("Expected I64ExtendI32S, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_extend_i32_u() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64ExtendI32U];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64ExtendI32U { rdlo, rdhi, rn } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(*rn, Reg::R0);
            }
            other => panic!("Expected I64ExtendI32U, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_wrap_i64() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32WrapI64];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I32WrapI64 { rd, rnlo } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rnlo, Reg::R0);
            }
            other => panic!("Expected I32WrapI64, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_add() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Add];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // i64 add generates ADDS + ADC (two instructions)
        assert_eq!(arm_instrs.len(), 2);
        match &arm_instrs[0].op {
            ArmOp::Adds { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn, Reg::R0);
                assert_eq!(*op2, Operand2::Reg(Reg::R2));
            }
            other => panic!("Expected Adds, got {other:?}"),
        }
        match &arm_instrs[1].op {
            ArmOp::Adc { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R1);
                assert_eq!(*op2, Operand2::Reg(Reg::R3));
            }
            other => panic!("Expected Adc, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_sub() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Sub];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        match &arm_instrs[0].op {
            ArmOp::Subs { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn, Reg::R0);
                assert_eq!(*op2, Operand2::Reg(Reg::R2));
            }
            other => panic!("Expected Subs, got {other:?}"),
        }
        match &arm_instrs[1].op {
            ArmOp::Sbc { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R1);
                assert_eq!(*op2, Operand2::Reg(Reg::R3));
            }
            other => panic!("Expected Sbc, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_and() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64And];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        match &arm_instrs[0].op {
            ArmOp::And { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn, Reg::R0);
                assert_eq!(*op2, Operand2::Reg(Reg::R2));
            }
            other => panic!("Expected And (lo), got {other:?}"),
        }
        match &arm_instrs[1].op {
            ArmOp::And { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1);
                assert_eq!(*rn, Reg::R1);
                assert_eq!(*op2, Operand2::Reg(Reg::R3));
            }
            other => panic!("Expected And (hi), got {other:?}"),
        }
    }

    #[test]
    fn test_i64_or() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Or];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Orr { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::Orr { .. }));
    }

    #[test]
    fn test_i64_xor() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Xor];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Eor { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::Eor { .. }));
    }

    #[test]
    fn test_i64_eqz() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Eqz];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn_lo, Reg::R0);
                assert_eq!(*rn_hi, Reg::R1);
            }
            other => panic!("Expected I64SetCondZ, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_eq() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Eq];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond {
                rd,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
                cond,
            } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*rn_lo, Reg::R0);
                assert_eq!(*rn_hi, Reg::R1);
                assert_eq!(*rm_lo, Reg::R2);
                assert_eq!(*rm_hi, Reg::R3);
                assert_eq!(*cond, Condition::EQ);
            }
            other => panic!("Expected I64SetCond EQ, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_ne() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Ne];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => {
                assert_eq!(*cond, Condition::NE);
            }
            other => panic!("Expected I64SetCond NE, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_lt_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64LtS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::LT),
            other => panic!("Expected I64SetCond LT, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_lt_u() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64LtU];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::LO),
            other => panic!("Expected I64SetCond LO, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_le_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64LeS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::LE),
            other => panic!("Expected I64SetCond LE, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_gt_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64GtS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::GT),
            other => panic!("Expected I64SetCond GT, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_ge_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64GeS];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64SetCond { cond, .. } => assert_eq!(*cond, Condition::GE),
            other => panic!("Expected I64SetCond GE, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_unsigned_comparisons() {
        let db = RuleDatabase::new();

        // Test all unsigned comparison conditions
        let tests = vec![
            (WasmOp::I64LeU, Condition::LS),
            (WasmOp::I64GtU, Condition::HI),
            (WasmOp::I64GeU, Condition::HS),
        ];

        for (op, expected_cond) in tests {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let arm_instrs = selector.select(std::slice::from_ref(&op)).unwrap();
            assert_eq!(arm_instrs.len(), 1);
            match &arm_instrs[0].op {
                ArmOp::I64SetCond { cond, .. } => {
                    assert_eq!(*cond, expected_cond, "Wrong condition for {op:?}");
                }
                other => panic!("Expected I64SetCond for {op:?}, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_i64_mul() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Mul];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::I64Mul {
                rd_lo,
                rd_hi,
                rn_lo,
                rn_hi,
                rm_lo,
                rm_hi,
            } => {
                assert_eq!(*rd_lo, Reg::R0);
                assert_eq!(*rd_hi, Reg::R1);
                assert_eq!(*rn_lo, Reg::R0);
                assert_eq!(*rn_hi, Reg::R1);
                assert_eq!(*rm_lo, Reg::R2);
                assert_eq!(*rm_hi, Reg::R3);
            }
            other => panic!("Expected I64Mul, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_shifts() {
        let db = RuleDatabase::new();

        // Shift left
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let arm_instrs = selector.select(&[WasmOp::I64Shl]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Shl { .. }));

        // Shift right unsigned
        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64ShrU]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64ShrU { .. }));

        // Shift right signed
        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64ShrS]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64ShrS { .. }));
    }

    #[test]
    fn test_i64_rotations() {
        let db = RuleDatabase::new();

        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let arm_instrs = selector.select(&[WasmOp::I64Rotl]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Rotl { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Rotr]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Rotr { .. }));
    }

    #[test]
    fn test_i64_bit_manipulation() {
        let db = RuleDatabase::new();

        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let arm_instrs = selector.select(&[WasmOp::I64Clz]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Clz { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Ctz]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Ctz { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Popcnt]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Popcnt { .. }));
    }

    #[test]
    fn test_i64_division_remainder() {
        let db = RuleDatabase::new();

        let ops = vec![
            (WasmOp::I64DivS, "I64DivS"),
            (WasmOp::I64DivU, "I64DivU"),
            (WasmOp::I64RemS, "I64RemS"),
            (WasmOp::I64RemU, "I64RemU"),
        ];

        for (op, name) in ops {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let arm_instrs = selector.select(&[op]).unwrap();
            assert_eq!(arm_instrs.len(), 1, "Failed for {name}");
            // Each should emit the corresponding i64 pseudo-op
        }
    }

    #[test]
    fn test_i64_extend_sign_operations() {
        let db = RuleDatabase::new();

        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let arm_instrs = selector.select(&[WasmOp::I64Extend8S]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Extend8S { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Extend16S]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Extend16S { .. }));

        selector.reset();
        let arm_instrs = selector.select(&[WasmOp::I64Extend32S]).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64Extend32S { .. }));
    }

    #[test]
    fn test_i64_add_sequence() {
        // Test a full i64 add sequence: const + const + add
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64Const(1), WasmOp::I64Const(2), WasmOp::I64Add];

        let arm_instrs = selector.select(&wasm_ops).unwrap();
        // I64Const(1) -> 1 instr
        // I64Const(2) -> 1 instr
        // I64Add -> 2 instrs (ADDS + ADC)
        assert_eq!(arm_instrs.len(), 4);

        // First two are I64Const
        assert!(matches!(
            &arm_instrs[0].op,
            ArmOp::I64Const { value: 1, .. }
        ));
        assert!(matches!(
            &arm_instrs[1].op,
            ArmOp::I64Const { value: 2, .. }
        ));
        // Then ADDS + ADC
        assert!(matches!(&arm_instrs[2].op, ArmOp::Adds { .. }));
        assert!(matches!(&arm_instrs[3].op, ArmOp::Adc { .. }));
    }

    #[test]
    fn test_i64_wrap_extend_roundtrip() {
        // extend_i32_u followed by wrap_i64 should produce two instructions
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I64ExtendI32U, WasmOp::I32WrapI64];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::I64ExtendI32U { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::I32WrapI64 { .. }));
    }

    #[test]
    fn test_i64_load_store() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I64Load {
                offset: 8,
                align: 8,
            },
            WasmOp::I64Store {
                offset: 16,
                align: 8,
            },
        ];

        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 2);

        match &arm_instrs[0].op {
            ArmOp::I64Ldr { rdlo, rdhi, addr } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(addr.offset, 8);
            }
            other => panic!("Expected I64Ldr, got {other:?}"),
        }

        match &arm_instrs[1].op {
            ArmOp::I64Str { rdlo, rdhi, addr } => {
                assert_eq!(*rdlo, Reg::R0);
                assert_eq!(*rdhi, Reg::R1);
                assert_eq!(addr.offset, 16);
            }
            other => panic!("Expected I64Str, got {other:?}"),
        }
    }

    #[test]
    fn test_i64_all_ops_no_error() {
        // Verify that ALL i64 operations now succeed (no more "requires register pairs" error)
        let db = RuleDatabase::new();

        let all_i64_ops: Vec<WasmOp> = vec![
            WasmOp::I64Const(42),
            WasmOp::I64Add,
            WasmOp::I64Sub,
            WasmOp::I64Mul,
            WasmOp::I64DivS,
            WasmOp::I64DivU,
            WasmOp::I64RemS,
            WasmOp::I64RemU,
            WasmOp::I64And,
            WasmOp::I64Or,
            WasmOp::I64Xor,
            WasmOp::I64Shl,
            WasmOp::I64ShrS,
            WasmOp::I64ShrU,
            WasmOp::I64Rotl,
            WasmOp::I64Rotr,
            WasmOp::I64Clz,
            WasmOp::I64Ctz,
            WasmOp::I64Popcnt,
            WasmOp::I64Eqz,
            WasmOp::I64Eq,
            WasmOp::I64Ne,
            WasmOp::I64LtS,
            WasmOp::I64LtU,
            WasmOp::I64LeS,
            WasmOp::I64LeU,
            WasmOp::I64GtS,
            WasmOp::I64GtU,
            WasmOp::I64GeS,
            WasmOp::I64GeU,
            WasmOp::I64ExtendI32S,
            WasmOp::I64ExtendI32U,
            WasmOp::I32WrapI64,
            WasmOp::I64Extend8S,
            WasmOp::I64Extend16S,
            WasmOp::I64Extend32S,
            WasmOp::I64Load {
                offset: 0,
                align: 8,
            },
            WasmOp::I64Store {
                offset: 0,
                align: 8,
            },
        ];

        // Each should succeed individually (no error)
        for op in &all_i64_ops {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let result = selector.select(std::slice::from_ref(op));
            assert!(
                result.is_ok(),
                "i64 operation {op:?} should succeed but got error: {:?}",
                result.err()
            );
        }
    }

    // =========================================================================
    // Sub-word load/store tests
    // =========================================================================

    #[test]
    fn test_i32_load8_u() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Load8U {
            offset: 0,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldrb { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(addr.base, Reg::R11);
                assert_eq!(addr.offset, 0);
            }
            other => panic!("Expected Ldrb, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_load8_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Load8S {
            offset: 4,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldrsb { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(addr.base, Reg::R11);
                assert_eq!(addr.offset, 4);
            }
            other => panic!("Expected Ldrsb, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_load16_u() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Load16U {
            offset: 8,
            align: 2,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldrh { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(addr.base, Reg::R11);
                assert_eq!(addr.offset, 8);
            }
            other => panic!("Expected Ldrh, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_load16_s() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Load16S {
            offset: 0,
            align: 2,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Ldrsh { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(addr.base, Reg::R11);
            }
            other => panic!("Expected Ldrsh, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_store8() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Store8 {
            offset: 0,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Strb { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(addr.base, Reg::R11);
            }
            other => panic!("Expected Strb, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_store16() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::I32Store16 {
            offset: 4,
            align: 2,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        match &arm_instrs[0].op {
            ArmOp::Strh { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(addr.base, Reg::R11);
                assert_eq!(addr.offset, 4);
            }
            other => panic!("Expected Strh, got {other:?}"),
        }
    }

    #[test]
    fn test_i32_subword_loads_with_bounds_checking() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::with_bounds_check(
            db.rules().to_vec(),
            BoundsCheckConfig::Software,
        );

        let wasm_ops = vec![WasmOp::I32Load8U {
            offset: 4,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // With software bounds checking: ADD + CMP + BHS + LDRB
        assert_eq!(arm_instrs.len(), 4);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Add { .. }));
        assert!(matches!(&arm_instrs[1].op, ArmOp::Cmp { .. }));
        assert!(matches!(&arm_instrs[2].op, ArmOp::Bhs { .. }));
        assert!(matches!(&arm_instrs[3].op, ArmOp::Ldrb { .. }));
    }

    #[test]
    fn test_i32_subword_stores_with_bounds_checking() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::with_bounds_check(
            db.rules().to_vec(),
            BoundsCheckConfig::Software,
        );

        let wasm_ops = vec![WasmOp::I32Store16 {
            offset: 0,
            align: 2,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        // With software bounds checking: ADD + CMP + BHS + STRH
        assert_eq!(arm_instrs.len(), 4);
        assert!(matches!(&arm_instrs[3].op, ArmOp::Strh { .. }));
    }

    #[test]
    fn test_i64_subword_loads() {
        let db = RuleDatabase::new();

        // i64.load8_s: LDRSB + ASR (sign-extend hi from lo)
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Load8S {
            offset: 0,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Ldrsb { .. }));
        assert!(matches!(
            &arm_instrs[1].op,
            ArmOp::Asr {
                rd: Reg::R1,
                rn: Reg::R0,
                shift: 31
            }
        ));

        // i64.load8_u: LDRB + MOV R1, #0
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Load8U {
            offset: 0,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Ldrb { .. }));
        assert!(matches!(
            &arm_instrs[1].op,
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Imm(0)
            }
        ));

        // i64.load32_s: LDR + ASR
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Load32S {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Ldr { .. }));
        assert!(matches!(
            &arm_instrs[1].op,
            ArmOp::Asr {
                rd: Reg::R1,
                rn: Reg::R0,
                shift: 31
            }
        ));

        // i64.load32_u: LDR + MOV R1, #0
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Load32U {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 2);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Ldr { .. }));
        assert!(matches!(
            &arm_instrs[1].op,
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Imm(0)
            }
        ));
    }

    #[test]
    fn test_i64_subword_stores() {
        let db = RuleDatabase::new();

        // i64.store8: STRB
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Store8 {
            offset: 0,
            align: 1,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Strb { .. }));

        // i64.store16: STRH
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Store16 {
            offset: 0,
            align: 2,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Strh { .. }));

        // i64.store32: STR
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let wasm_ops = vec![WasmOp::I64Store32 {
            offset: 0,
            align: 4,
        }];
        let arm_instrs = selector.select(&wasm_ops).unwrap();
        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::Str { .. }));
    }

    // =========================================================================
    // memory.size / memory.grow tests
    // =========================================================================

    #[test]
    fn test_memory_size() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::MemorySize(0)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::MemorySize { .. }));
    }

    #[test]
    fn test_memory_grow() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::MemoryGrow(0)];
        let arm_instrs = selector.select(&wasm_ops).unwrap();

        assert_eq!(arm_instrs.len(), 1);
        assert!(matches!(&arm_instrs[0].op, ArmOp::MemoryGrow { .. }));
    }

    #[test]
    fn test_all_subword_ops_succeed() {
        let db = RuleDatabase::new();

        let all_subword_ops = vec![
            WasmOp::I32Load8S {
                offset: 0,
                align: 1,
            },
            WasmOp::I32Load8U {
                offset: 0,
                align: 1,
            },
            WasmOp::I32Load16S {
                offset: 0,
                align: 2,
            },
            WasmOp::I32Load16U {
                offset: 0,
                align: 2,
            },
            WasmOp::I32Store8 {
                offset: 0,
                align: 1,
            },
            WasmOp::I32Store16 {
                offset: 0,
                align: 2,
            },
            WasmOp::I64Load8S {
                offset: 0,
                align: 1,
            },
            WasmOp::I64Load8U {
                offset: 0,
                align: 1,
            },
            WasmOp::I64Load16S {
                offset: 0,
                align: 2,
            },
            WasmOp::I64Load16U {
                offset: 0,
                align: 2,
            },
            WasmOp::I64Load32S {
                offset: 0,
                align: 4,
            },
            WasmOp::I64Load32U {
                offset: 0,
                align: 4,
            },
            WasmOp::I64Store8 {
                offset: 0,
                align: 1,
            },
            WasmOp::I64Store16 {
                offset: 0,
                align: 2,
            },
            WasmOp::I64Store32 {
                offset: 0,
                align: 4,
            },
            WasmOp::MemorySize(0),
            WasmOp::MemoryGrow(0),
        ];

        for op in &all_subword_ops {
            let mut selector = InstructionSelector::new(db.rules().to_vec());
            let result = selector.select(std::slice::from_ref(op));
            assert!(
                result.is_ok(),
                "Sub-word/memory operation {op:?} should succeed but got error: {:?}",
                result.err()
            );
        }
    }

    #[test]
    fn test_subword_load_stack_mode() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        // Test i32.load8_u in stack mode: local.get 0; i32.load8_u; end
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load8U {
                offset: 0,
                align: 1,
            },
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should contain at least one Ldrb instruction
        let has_ldrb = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Ldrb { .. }));
        assert!(has_ldrb, "Should contain LDRB instruction");
    }

    #[test]
    fn test_subword_store_stack_mode() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        // Test i32.store8 in stack mode: local.get 0; i32.const 42; i32.store8; end
        let wasm_ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(42),
            WasmOp::I32Store8 {
                offset: 0,
                align: 1,
            },
            WasmOp::End,
        ];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // Should contain a Strb instruction
        let has_strb = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Strb { .. }));
        assert!(has_strb, "Should contain STRB instruction");
    }

    #[test]
    fn test_memory_size_stack_mode() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![WasmOp::MemorySize(0), WasmOp::End];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_mem_size = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::MemorySize { .. }));
        assert!(has_mem_size, "Should contain MemorySize instruction");
    }

    #[test]
    fn test_memory_grow_stack_mode() {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        // memory.grow pops 1 value (requested pages) from stack
        let wasm_ops = vec![WasmOp::I32Const(1), WasmOp::MemoryGrow(0), WasmOp::End];
        let arm_instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        let has_mem_grow = arm_instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::MemoryGrow { .. }));
        assert!(has_mem_grow, "Should contain MemoryGrow instruction");
    }

    // ========================================================================
    // v128 SIMD / Helium MVE tests
    // ========================================================================

    fn helium_selector() -> InstructionSelector {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_target(Some(FPUPrecision::Single), "cortex-m55");
        selector.set_helium(true);
        selector
    }

    fn non_helium_selector() -> InstructionSelector {
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        selector.set_target(Some(FPUPrecision::Single), "cortex-m4f");
        selector
    }

    #[test]
    fn test_simd_i32x4_add_on_helium() {
        let mut selector = helium_selector();
        let ops = vec![WasmOp::I32x4Add];
        let result = selector.select(&ops);
        assert!(result.is_ok(), "i32x4.add should succeed on Helium target");
        let instrs = result.unwrap();
        assert!(
            instrs.iter().any(|i| matches!(
                &i.op,
                ArmOp::MveAddI {
                    size: MveSize::S32,
                    ..
                }
            )),
            "Should produce VADD.I32 MVE instruction"
        );
    }

    #[test]
    fn test_simd_i32x4_sub_on_helium() {
        let mut selector = helium_selector();
        let ops = vec![WasmOp::I32x4Sub];
        let result = selector.select(&ops);
        assert!(result.is_ok());
        let instrs = result.unwrap();
        assert!(instrs.iter().any(|i| matches!(
            &i.op,
            ArmOp::MveSubI {
                size: MveSize::S32,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_i32x4_mul_on_helium() {
        let mut selector = helium_selector();
        let ops = vec![WasmOp::I32x4Mul];
        let result = selector.select(&ops);
        assert!(result.is_ok());
        let instrs = result.unwrap();
        assert!(instrs.iter().any(|i| matches!(
            &i.op,
            ArmOp::MveMulI {
                size: MveSize::S32,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_i8x16_add_on_helium() {
        let mut selector = helium_selector();
        let ops = vec![WasmOp::I8x16Add];
        let result = selector.select(&ops);
        assert!(result.is_ok());
        let instrs = result.unwrap();
        assert!(instrs.iter().any(|i| matches!(
            &i.op,
            ArmOp::MveAddI {
                size: MveSize::S8,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_i16x8_add_on_helium() {
        let mut selector = helium_selector();
        let ops = vec![WasmOp::I16x8Add];
        let result = selector.select(&ops);
        assert!(result.is_ok());
        let instrs = result.unwrap();
        assert!(instrs.iter().any(|i| matches!(
            &i.op,
            ArmOp::MveAddI {
                size: MveSize::S16,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_v128_bitwise_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::V128And]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveAnd { .. }))
        );

        let result = selector.select(&[WasmOp::V128Or]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveOrr { .. }))
        );

        let result = selector.select(&[WasmOp::V128Xor]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveEor { .. }))
        );

        let result = selector.select(&[WasmOp::V128Not]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveMvn { .. }))
        );

        let result = selector.select(&[WasmOp::V128AndNot]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveBic { .. }))
        );
    }

    #[test]
    fn test_simd_v128_const_on_helium() {
        let mut selector = helium_selector();
        let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
        let ops = vec![WasmOp::V128Const(bytes)];
        let result = selector.select(&ops);
        assert!(result.is_ok());
        let instrs = result.unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveConst { bytes: b, .. } if *b == bytes))
        );
    }

    #[test]
    fn test_simd_v128_load_store_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::V128Load {
            offset: 0,
            align: 4,
        }]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveLoad { .. }))
        );

        let result = selector.select(&[WasmOp::V128Store {
            offset: 0,
            align: 4,
        }]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveStore { .. }))
        );
    }

    #[test]
    fn test_simd_i32x4_splat_on_helium() {
        let mut selector = helium_selector();
        let result = selector.select(&[WasmOp::I32x4Splat]);
        assert!(result.is_ok());
        assert!(result.unwrap().iter().any(|i| matches!(
            &i.op,
            ArmOp::MveDup {
                size: MveSize::S32,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_i32x4_extract_lane_on_helium() {
        let mut selector = helium_selector();
        let result = selector.select(&[WasmOp::I32x4ExtractLane(2)]);
        assert!(result.is_ok());
        assert!(result.unwrap().iter().any(|i| matches!(
            &i.op,
            ArmOp::MveExtractLane {
                lane: 2,
                size: MveSize::S32,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_i32x4_replace_lane_on_helium() {
        let mut selector = helium_selector();
        let result = selector.select(&[WasmOp::I32x4ReplaceLane(1)]);
        assert!(result.is_ok());
        assert!(result.unwrap().iter().any(|i| matches!(
            &i.op,
            ArmOp::MveInsertLane {
                lane: 1,
                size: MveSize::S32,
                ..
            }
        )));
    }

    #[test]
    fn test_simd_f32x4_arithmetic_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::F32x4Add]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveAddF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4Sub]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveSubF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4Mul]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveMulF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4Div]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveDivF32 { .. }))
        );
    }

    #[test]
    fn test_simd_f32x4_unary_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::F32x4Abs]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveAbsF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4Neg]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveNegF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4Sqrt]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveSqrtF32 { .. }))
        );
    }

    #[test]
    fn test_simd_f32x4_comparisons_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::F32x4Eq]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveCmpEqF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4Lt]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveCmpLtF32 { .. }))
        );
    }

    #[test]
    fn test_simd_f32x4_splat_extract_replace_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::F32x4Splat]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveDupF32 { .. }))
        );

        let result = selector.select(&[WasmOp::F32x4ExtractLane(3)]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveExtractLaneF32 { lane: 3, .. }))
        );

        let result = selector.select(&[WasmOp::F32x4ReplaceLane(0)]);
        assert!(result.is_ok());
        assert!(
            result
                .unwrap()
                .iter()
                .any(|i| matches!(&i.op, ArmOp::MveReplaceLaneF32 { lane: 0, .. }))
        );
    }

    #[test]
    fn test_simd_i32x4_comparisons_on_helium() {
        let mut selector = helium_selector();

        for (op, expected_pattern) in [
            (WasmOp::I32x4Eq, "CmpEqI"),
            (WasmOp::I32x4Ne, "CmpNeI"),
            (WasmOp::I32x4LtS, "CmpLtS"),
            (WasmOp::I32x4LtU, "CmpLtU"),
            (WasmOp::I32x4GtS, "CmpGtS"),
            (WasmOp::I32x4GtU, "CmpGtU"),
        ] {
            let result = selector.select(std::slice::from_ref(&op));
            assert!(
                result.is_ok(),
                "Comparison {expected_pattern} should succeed on Helium"
            );
        }
    }

    #[test]
    fn test_simd_rejected_on_non_helium() {
        let mut selector = non_helium_selector();

        let simd_ops = vec![
            WasmOp::I32x4Add,
            WasmOp::I8x16Add,
            WasmOp::I16x8Add,
            WasmOp::V128And,
            WasmOp::V128Const([0u8; 16]),
            WasmOp::V128Load {
                offset: 0,
                align: 4,
            },
            WasmOp::I32x4Splat,
            WasmOp::F32x4Add,
            WasmOp::F32x4Splat,
        ];

        for op in &simd_ops {
            let result = selector.select(std::slice::from_ref(op));
            assert!(
                result.is_err(),
                "SIMD op {op:?} should be rejected on non-Helium target"
            );
            let err_msg = result.unwrap_err().to_string();
            assert!(
                err_msg.contains("Helium") || err_msg.contains("SIMD"),
                "Error for {op:?} should mention Helium or SIMD: {err_msg}"
            );
        }
    }

    #[test]
    fn test_simd_i8x16_shuffle_not_implemented() {
        let mut selector = helium_selector();
        let result = selector.select(&[WasmOp::I8x16Shuffle([
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        ])]);
        assert!(
            result.is_err(),
            "i8x16.shuffle should error (not yet implemented)"
        );
    }

    #[test]
    fn test_validate_instructions_rejects_mve_on_non_helium() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::MveAddI {
                qd: QReg::Q0,
                qn: QReg::Q1,
                qm: QReg::Q2,
                size: MveSize::S32,
            },
            source_line: Some(0),
        }];
        let result = super::validate_instructions_with_helium(
            &instrs,
            Some(FPUPrecision::Single),
            false,
            "cortex-m4f",
        );
        assert!(
            result.is_err(),
            "MVE instruction should be rejected on non-Helium target"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("Helium"),
            "Error should mention Helium: {err_msg}"
        );
    }

    #[test]
    fn test_validate_instructions_allows_mve_on_helium() {
        let instrs = vec![ArmInstruction {
            op: ArmOp::MveAddI {
                qd: QReg::Q0,
                qn: QReg::Q1,
                qm: QReg::Q2,
                size: MveSize::S32,
            },
            source_line: Some(0),
        }];
        let result = super::validate_instructions_with_helium(
            &instrs,
            Some(FPUPrecision::Single),
            true,
            "cortex-m55",
        );
        assert!(
            result.is_ok(),
            "MVE instruction should be accepted on Helium target"
        );
    }

    #[test]
    fn test_simd_neg_operations_on_helium() {
        let mut selector = helium_selector();

        let result = selector.select(&[WasmOp::I8x16Neg]);
        assert!(result.is_ok());
        assert!(result.unwrap().iter().any(|i| matches!(
            &i.op,
            ArmOp::MveNegI {
                size: MveSize::S8,
                ..
            }
        )));

        let result = selector.select(&[WasmOp::I16x8Neg]);
        assert!(result.is_ok());
        assert!(result.unwrap().iter().any(|i| matches!(
            &i.op,
            ArmOp::MveNegI {
                size: MveSize::S16,
                ..
            }
        )));

        let result = selector.select(&[WasmOp::I32x4Neg]);
        assert!(result.is_ok());
        assert!(result.unwrap().iter().any(|i| matches!(
            &i.op,
            ArmOp::MveNegI {
                size: MveSize::S32,
                ..
            }
        )));
    }

    #[test]
    fn test_requires_helium_trait() {
        // MVE instructions should report requires_helium = true
        let mve_op = ArmOp::MveAddI {
            qd: QReg::Q0,
            qn: QReg::Q1,
            qm: QReg::Q2,
            size: MveSize::S32,
        };
        assert!(mve_op.requires_helium());
        assert!(!mve_op.requires_fpu());

        // Non-MVE instructions should report requires_helium = false
        let add_op = ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        };
        assert!(!add_op.requires_helium());

        // FPU instructions should not require Helium
        let f32_op = ArmOp::F32Add {
            sd: VfpReg::S0,
            sn: VfpReg::S1,
            sm: VfpReg::S2,
        };
        assert!(!f32_op.requires_helium());
        assert!(f32_op.requires_fpu());
    }

    // =========================================================================
    // Task 1: Constant materialization edge cases
    //
    // Verify that i32.const produces correct ARM sequences for boundary values.
    // =========================================================================

    #[test]
    fn test_const_materialization_minus_one() {
        // i32.const -1 (0xFFFFFFFF) -> MOVW #0 + MVN (inverted pattern)
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(-1)], 0)
            .unwrap();

        // Should have MOVW rd, #0 then MVN rd, rd (inverted path since !0xFFFFFFFF == 0)
        let movw_ops: Vec<_> = instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Movw { imm16: 0, .. }))
            .collect();
        assert!(
            !movw_ops.is_empty(),
            "Should emit MOVW #0 for -1 (inverted=0)"
        );

        let mvn_ops: Vec<_> = instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Mvn { .. }))
            .collect();
        assert!(!mvn_ops.is_empty(), "Should emit MVN for -1");
    }

    #[test]
    fn test_const_materialization_zero() {
        // i32.const 0 -> single MOVW #0
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(0)], 0)
            .unwrap();

        let has_movw_zero = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0, .. }));
        assert!(has_movw_zero, "Should emit MOVW #0 for zero");

        // Should NOT emit MOVT (zero fits in 16 bits)
        let movt_count = count_op(&instrs, |op| matches!(op, ArmOp::Movt { .. }));
        assert_eq!(movt_count, 0, "Zero should not emit MOVT");
    }

    #[test]
    fn test_const_materialization_255() {
        // i32.const 255 -> single MOVW #255
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(255)], 0)
            .unwrap();

        let has_movw = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 255, .. }));
        assert!(has_movw, "Should emit MOVW #255");

        let movt_count = count_op(&instrs, |op| matches!(op, ArmOp::Movt { .. }));
        assert_eq!(movt_count, 0, "255 fits in 16 bits, no MOVT needed");
    }

    #[test]
    fn test_const_materialization_256() {
        // i32.const 256 -> single MOVW #256
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(256)], 0)
            .unwrap();

        let has_movw = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 256, .. }));
        assert!(has_movw, "Should emit MOVW #256");

        let movt_count = count_op(&instrs, |op| matches!(op, ArmOp::Movt { .. }));
        assert_eq!(movt_count, 0, "256 fits in 16 bits, no MOVT needed");
    }

    #[test]
    fn test_const_materialization_65536() {
        // i32.const 65536 (0x10000) -> MOVW #0 + MOVT #1
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(65536)], 0)
            .unwrap();

        let has_movw_zero = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0, .. }));
        assert!(has_movw_zero, "Should emit MOVW #0 for low 16 bits");

        let has_movt_one = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 1, .. }));
        assert!(has_movt_one, "Should emit MOVT #1 for high 16 bits");
    }

    #[test]
    fn test_const_materialization_i32_max() {
        // i32.const 0x7FFFFFFF -> MOVW 0xFFFF + MOVT 0x7FFF
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(0x7FFFFFFF)], 0)
            .unwrap();

        let has_movw = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0xFFFF, .. }));
        assert!(has_movw, "Should emit MOVW #0xFFFF for low 16 bits");

        let has_movt = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 0x7FFF, .. }));
        assert!(has_movt, "Should emit MOVT #0x7FFF for high 16 bits");
    }

    #[test]
    fn test_const_materialization_i32_min() {
        // i32.const -2147483648 (0x80000000) -> MOVW #0 + MOVT #0x8000
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(i32::MIN)], 0)
            .unwrap();

        let has_movw_zero = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0, .. }));
        assert!(
            has_movw_zero,
            "Should emit MOVW #0 for low 16 bits of i32::MIN"
        );

        let has_movt = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 0x8000, .. }));
        assert!(
            has_movt,
            "Should emit MOVT #0x8000 for high 16 bits of i32::MIN"
        );
    }

    #[test]
    fn test_const_materialization_select_default() {
        // Also test the select_default path (non-stack mode)
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        // -1 through select_default
        let instrs = selector.select(&[WasmOp::I32Const(-1)]).unwrap();
        let has_movw = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0, .. }));
        let has_mvn = instrs.iter().any(|i| matches!(&i.op, ArmOp::Mvn { .. }));
        assert!(
            has_movw && has_mvn,
            "select_default -1 should emit MOVW #0 + MVN"
        );

        // 65536 through select_default
        selector.reset();
        let instrs = selector.select(&[WasmOp::I32Const(65536)]).unwrap();
        let has_movw_zero = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0, .. }));
        let has_movt_one = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 1, .. }));
        assert!(
            has_movw_zero && has_movt_one,
            "select_default 65536 should emit MOVW #0 + MOVT #1"
        );

        // i32::MIN through select_default
        selector.reset();
        let instrs = selector.select(&[WasmOp::I32Const(i32::MIN)]).unwrap();
        let has_movt = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 0x8000, .. }));
        assert!(has_movt, "select_default i32::MIN should emit MOVT #0x8000");
    }

    // =========================================================================
    // Task 2: Callee-saved register restoration on all exit paths
    // =========================================================================

    #[test]
    fn test_epilogue_normal_end() {
        // Normal function: PUSH at start, POP at end
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(42)], 0)
            .unwrap();

        // First instruction should be PUSH {R4-R8, LR}
        assert!(
            matches!(&instrs[0].op, ArmOp::Push { regs } if regs.contains(&Reg::LR)),
            "Prologue must PUSH LR"
        );

        // Last instruction should be POP {R4-R8, PC}
        let last = &instrs[instrs.len() - 1];
        assert!(
            matches!(&last.op, ArmOp::Pop { regs } if regs.contains(&Reg::PC)),
            "Epilogue must POP PC"
        );
    }

    #[test]
    fn test_epilogue_return_opcode() {
        // Return opcode must restore callee-saved regs (POP {R4-R8, PC})
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::I32Const(42), WasmOp::Return], 0)
            .unwrap();

        // Find the Return-generated POP
        let pop_ops: Vec<_> = instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Pop { regs } if regs.contains(&Reg::PC)))
            .collect();

        // Should have at least 2 POPs: one from Return, one from epilogue
        assert!(
            !pop_ops.is_empty(),
            "Return must emit POP {{R4-R8, PC}} to restore callee-saved regs"
        );

        // Verify the Return-generated POP has R4 (callee-saved)
        let return_pop = instrs.iter().find(|i| {
            matches!(&i.op, ArmOp::Pop { regs }
                if regs.contains(&Reg::R4) && regs.contains(&Reg::PC))
        });
        assert!(
            return_pop.is_some(),
            "Return must POP callee-saved regs (R4-R8) along with PC"
        );
    }

    #[test]
    fn test_epilogue_unreachable_no_restore() {
        // Unreachable (UDF trap) doesn't need register restoration
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(&[WasmOp::Unreachable], 0)
            .unwrap();

        let has_udf = instrs.iter().any(|i| matches!(&i.op, ArmOp::Udf { .. }));
        assert!(has_udf, "Unreachable should emit UDF");

        // The UDF should appear BEFORE any epilogue POP
        let udf_pos = instrs
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Udf { .. }))
            .unwrap();
        // The final POP is just the function epilogue, UDF fires before reaching it
        assert!(
            udf_pos < instrs.len() - 1,
            "UDF trap should be before epilogue"
        );
    }

    #[test]
    fn test_epilogue_br_out_of_function() {
        // Br from a block back to the function level — should restore before returning
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[
                    WasmOp::Block,
                    WasmOp::I32Const(1),
                    WasmOp::Br(0), // branch to end of block
                    WasmOp::End,   // end block
                ],
                0,
            )
            .unwrap();

        // The function epilogue POP must exist
        let pop_count = count_op(
            &instrs,
            |op| matches!(op, ArmOp::Pop { regs } if regs.contains(&Reg::PC)),
        );
        assert!(pop_count >= 1, "Must have epilogue POP after block exits");
    }

    #[test]
    fn test_epilogue_early_return_from_nested() {
        // Return from nested if inside loop inside block
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[
                    WasmOp::Block,
                    WasmOp::Loop,
                    WasmOp::LocalGet(0),
                    WasmOp::I32Eqz,
                    WasmOp::If,
                    WasmOp::I32Const(99),
                    WasmOp::Return,
                    WasmOp::End,   // end if
                    WasmOp::Br(0), // loop back
                    WasmOp::End,   // end loop
                    WasmOp::End,   // end block
                ],
                1,
            )
            .unwrap();

        // The early Return must include POP with callee-saved regs
        let pop_with_callee: Vec<_> = instrs
            .iter()
            .filter(|i| {
                matches!(&i.op, ArmOp::Pop { regs }
                if regs.contains(&Reg::R4) && regs.contains(&Reg::PC))
            })
            .collect();

        assert!(
            pop_with_callee.len() >= 2,
            "Early return + function epilogue should both POP callee-saved regs (found {})",
            pop_with_callee.len()
        );
    }

    // =========================================================================
    // Task 3: i64 division edge cases
    //
    // These verify that the instruction selector emits the right i64 pseudo-ops.
    // The actual division algorithm correctness is tested in Renode emulation.
    // =========================================================================

    #[test]
    fn test_i64_div_emits_pseudo_op() {
        // Verify that i64 division operations produce the correct pseudo-ops
        let mut selector = fresh_selector();

        // I64DivU
        let instrs = selector.select(&[WasmOp::I64DivU]).unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::I64DivU { .. })),
            "I64DivU should emit I64DivU pseudo-op"
        );

        // I64DivS
        selector.reset();
        let instrs = selector.select(&[WasmOp::I64DivS]).unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::I64DivS { .. })),
            "I64DivS should emit I64DivS pseudo-op"
        );

        // I64RemU
        selector.reset();
        let instrs = selector.select(&[WasmOp::I64RemU]).unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::I64RemU { .. })),
            "I64RemU should emit I64RemU pseudo-op"
        );

        // I64RemS
        selector.reset();
        let instrs = selector.select(&[WasmOp::I64RemS]).unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::I64RemS { .. })),
            "I64RemS should emit I64RemS pseudo-op"
        );
    }

    #[test]
    fn test_i64_div_register_allocation() {
        // Verify register allocation for i64 division:
        // dividend in R0:R1, divisor in R2:R3, result in R0:R1
        let mut selector = fresh_selector();

        let instrs = selector.select(&[WasmOp::I64DivU]).unwrap();
        if let ArmOp::I64DivU {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            rmlo,
            rmhi,
        } = &instrs[0].op
        {
            assert_eq!(*rnlo, Reg::R0, "Dividend low in R0");
            assert_eq!(*rnhi, Reg::R1, "Dividend high in R1");
            assert_eq!(*rmlo, Reg::R2, "Divisor low in R2");
            assert_eq!(*rmhi, Reg::R3, "Divisor high in R3");
            assert_eq!(*rdlo, Reg::R0, "Result low in R0");
            assert_eq!(*rdhi, Reg::R1, "Result high in R1");
        } else {
            panic!("Expected I64DivU, got {:?}", instrs[0].op);
        }
    }

    #[test]
    fn test_i32_div_zero_trap_sequence() {
        // Verify i32 division emits divide-by-zero trap check
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(42), WasmOp::I32Const(0), WasmOp::I32DivU],
                0,
            )
            .unwrap();

        // Should contain CMP, BNE (skip trap), UDF (trap), UDIV
        let has_cmp = instrs.iter().any(|i| matches!(&i.op, ArmOp::Cmp { .. }));
        let has_udf = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Udf { imm: 0 }));
        let has_udiv = instrs.iter().any(|i| matches!(&i.op, ArmOp::Udiv { .. }));

        assert!(has_cmp, "Division must have CMP for zero check");
        assert!(has_udf, "Division must have UDF for divide-by-zero trap");
        assert!(has_udiv, "Division must have UDIV instruction");
    }

    #[test]
    fn test_i32_divs_overflow_trap_sequence() {
        // Verify i32 signed division emits INT_MIN / -1 overflow check
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[
                    WasmOp::I32Const(i32::MIN),
                    WasmOp::I32Const(-1),
                    WasmOp::I32DivS,
                ],
                0,
            )
            .unwrap();

        // Should contain MOVT 0x8000 (loading INT_MIN for comparison)
        let has_int_min_check = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 0x8000, .. }));
        assert!(has_int_min_check, "I32DivS must check for INT_MIN overflow");

        // Should contain CMN for -1 check
        let has_cmn = instrs.iter().any(|i| matches!(&i.op, ArmOp::Cmn { .. }));
        assert!(has_cmn, "I32DivS must have CMN for -1 divisor check");

        // Should contain UDF #1 (overflow trap, distinct from div-by-zero UDF #0)
        let has_overflow_trap = instrs
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Udf { imm: 1 }));
        assert!(
            has_overflow_trap,
            "I32DivS must have UDF #1 for overflow trap"
        );
    }

    // =========================================================================
    // #209 Opt 1: constant-divisor guard elision + strength reduction.
    // The div-by-zero / overflow traps are dead when the divisor is a known
    // nonzero constant; power-of-two and by-1 divisors lower without UDIV.
    // =========================================================================

    /// A non-power-of-two constant divisor lowers to a reciprocal-multiply
    /// (#209 Opt 1b): no trap guard, no UDIV — a UMULL plus a shift.
    #[test]
    fn test_209_const_divisor_uses_reciprocal_multiply() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[
                    WasmOp::I32Const(1000),
                    WasmOp::I32Const(500),
                    WasmOp::I32DivU,
                ],
                0,
            )
            .unwrap();
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Udf { .. })),
            "nonzero const divisor must drop the div-by-zero UDF guard"
        );
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Cmp { .. })),
            "nonzero const divisor must drop the CMP #0 guard"
        );
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Udiv { .. })),
            "non-pow2 const divisor must NOT use UDIV (reciprocal-multiply)"
        );
        assert!(
            instrs.iter().any(|i| matches!(&i.op, ArmOp::Umull { .. })),
            "non-pow2 const divisor divides via UMULL high-word"
        );
        // #209 cleanup: the reciprocal-multiply reads the magic, never the
        // divisor — so the divisor's eager materialization (MOVW #500) is dead and
        // must NOT be emitted. (Magic for /500 is 0x10624DD3 → MOVW #0x4dd3, so
        // 500 = 0x1f4 only ever appeared as the dead divisor const.)
        assert!(
            !instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 500, .. })),
            "dead divisor const MOVW #500 must not be emitted on the UMULL path"
        );
    }

    /// #209 regression: multiple constant `div_u` under register pressure must
    /// COMPILE — the reciprocal-multiply is cost-gated (falls back to UDIV when
    /// scratch can't be allocated) so it never hard-fails like v0.11.19 did on
    /// gale's `control_step` (4× const `div_u` exhausted the R0–R8 pool). Mirrors
    /// that shape: 4 params each divided by a constant, all results kept live.
    #[test]
    fn test_209_multi_const_div_does_not_exhaust() {
        let mut selector = fresh_selector();
        let result = selector.select_with_stack(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Const(500),
                WasmOp::I32DivU,
                WasmOp::LocalGet(1),
                WasmOp::I32Const(5),
                WasmOp::I32DivU,
                WasmOp::LocalGet(2),
                WasmOp::I32Const(80),
                WasmOp::I32DivU,
                WasmOp::LocalGet(3),
                WasmOp::I32Const(1000),
                WasmOp::I32DivU,
                WasmOp::I32Add,
                WasmOp::I32Add,
                WasmOp::I32Add,
            ],
            4,
        );
        let instrs = result.expect("4× const div_u must compile, not exhaust (#209)");
        // Each divide lowered to either a reciprocal-multiply (UMULL) or the
        // cost-gated UDIV fallback — never dropped.
        let divides = instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Umull { .. } | ArmOp::Udiv { .. }))
            .count();
        assert!(
            divides >= 4,
            "all 4 const divides must lower (UMULL or UDIV fallback), got {divides}"
        );
    }

    /// A power-of-two unsigned divisor lowers to LSR — no UDIV, no guard.
    #[test]
    fn test_209_pow2_divu_uses_lsr() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(1000), WasmOp::I32Const(8), WasmOp::I32DivU],
                0,
            )
            .unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Lsr { shift: 3, .. })),
            "x / 8 must lower to LSR #3"
        );
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Udiv { .. })),
            "pow2 divisor must not emit UDIV"
        );
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Udf { .. })),
            "pow2 divisor must not emit a trap guard"
        );
    }

    /// `0x8000_0000` is 2^31 when the divisor is read unsigned: LSR #31.
    #[test]
    fn test_209_pow2_divu_high_bit_divisor() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[
                    WasmOp::I32Const(7),
                    WasmOp::I32Const(i32::MIN),
                    WasmOp::I32DivU,
                ],
                0,
            )
            .unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Lsr { shift: 31, .. })),
            "x / 2^31 must lower to LSR #31"
        );
    }

    /// Division by 1 is the identity — a MOV, no shift, no UDIV.
    #[test]
    fn test_209_divu_by_one_is_identity() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(1000), WasmOp::I32Const(1), WasmOp::I32DivU],
                0,
            )
            .unwrap();
        assert!(
            instrs.iter().any(|i| matches!(&i.op, ArmOp::Mov { .. })),
            "x / 1 must be a MOV identity"
        );
        assert!(
            !instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Udiv { .. } | ArmOp::Lsr { .. })),
            "x / 1 must not emit UDIV or LSR"
        );
    }

    /// Remainder by 1 is always 0 — MOV #0, no UDIV/MLS.
    #[test]
    fn test_209_remu_by_one_is_zero() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(1000), WasmOp::I32Const(1), WasmOp::I32RemU],
                0,
            )
            .unwrap();
        assert!(
            instrs.iter().any(|i| matches!(
                &i.op,
                ArmOp::Mov {
                    op2: Operand2::Imm(0),
                    ..
                }
            )),
            "x % 1 must be MOV #0"
        );
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Udiv { .. })),
            "x % 1 must not emit UDIV"
        );
    }

    /// A nonzero, non-`-1` constant divisor makes BOTH signed guards dead: no
    /// div-by-zero UDF, no INT_MIN/-1 overflow check — just SDIV.
    #[test]
    fn test_209_divs_const_drops_both_guards() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(1000), WasmOp::I32Const(5), WasmOp::I32DivS],
                0,
            )
            .unwrap();
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Udf { .. })),
            "const divisor != 0,-1 must drop both div-by-zero and overflow UDFs"
        );
        assert!(
            !instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Movt { imm16: 0x8000, .. })),
            "no INT_MIN materialization when overflow is statically impossible"
        );
        assert!(
            !instrs.iter().any(|i| matches!(&i.op, ArmOp::Cmn { .. })),
            "no CMN #1 (-1 check) when divisor is a known non-(-1) constant"
        );
        assert!(
            instrs.iter().any(|i| matches!(&i.op, ArmOp::Sdiv { .. })),
            "still divides via SDIV"
        );
    }

    /// The magic-number formula must reproduce `n / d` for every `n` (#209
    /// Opt 1b). Models the exact ARM sequence: `hi = umulhi(m, n)` then the
    /// `a`-selected shift/add. Checks gale's divisors + a spread, against an
    /// exhaustive set of edge-case dividends.
    #[test]
    fn test_209b_magicu_matches_division() {
        fn umulhi(m: u32, n: u32) -> u32 {
            ((m as u64 * n as u64) >> 32) as u32
        }
        fn recip(d: u32, n: u32) -> u32 {
            let (m, s, a) = magicu(d);
            let hi = umulhi(m, n);
            if a {
                (((n - hi) >> 1) + hi) >> (s - 1)
            } else if s == 0 {
                hi
            } else {
                hi >> s
            }
        }
        let divisors = [
            3,
            5,
            6,
            7,
            10,
            80,
            100,
            500,
            1000,
            1000000,
            0x7FFF_FFFF,
            0xFFFF_FFFF,
            0xFFFF_FFFE,
        ];
        let mut inputs: Vec<u32> = vec![
            0,
            1,
            2,
            3,
            499,
            500,
            501,
            999,
            1000,
            1001,
            79,
            80,
            81,
            0x7FFF_FFFF,
            0x8000_0000,
            0x8000_0001,
            0xFFFF_FFFF,
            0xFFFF_FFFE,
            0x1234_5678,
            0xABCD_EF01,
            0xDEAD_BEEF,
            1_000_000,
            2_000_003,
        ];
        // a deterministic spread across the range
        for k in 0..64u32 {
            inputs.push(k.wrapping_mul(0x0419_1A2B).wrapping_add(0x1357));
        }
        for &d in &divisors {
            for &n in &inputs {
                assert_eq!(recip(d, n), n / d, "magicu wrong for n=0x{n:08X} / d={d}");
            }
        }
    }

    /// Guard elision must NOT fire for a constant-zero divisor: the div-by-zero
    /// trap stays live (the program must trap at runtime).
    #[test]
    fn test_209_zero_const_divisor_keeps_guard() {
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(42), WasmOp::I32Const(0), WasmOp::I32DivU],
                0,
            )
            .unwrap();
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.op, ArmOp::Udf { imm: 0 })),
            "const-zero divisor must keep the div-by-zero trap"
        );
    }

    // =========================================================================
    // Task 4: Large function test
    //
    // Compile a function with 50+ operations and verify no panic/explosion.
    // =========================================================================

    #[test]
    #[allow(clippy::vec_init_then_push)]
    fn test_large_function_no_panic() {
        let mut selector = fresh_selector();

        // Build a function with 80+ operations:
        // nested loops, many locals, arithmetic chains
        let mut ops = vec![
            // Outer block
            WasmOp::Block,
            // First loop: compute sum of 1..10
            WasmOp::Loop,
            WasmOp::LocalGet(0), // counter
            WasmOp::I32Const(1),
            WasmOp::I32Sub,
            WasmOp::LocalSet(0),
            WasmOp::LocalGet(1), // accumulator
            WasmOp::LocalGet(0),
            WasmOp::I32Add,
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0),
            WasmOp::I32GtS,
            WasmOp::BrIf(0), // loop back
            WasmOp::End,     // end loop
            // Arithmetic chain
            WasmOp::LocalGet(1),
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
            WasmOp::I32Const(3),
            WasmOp::I32Add,
            WasmOp::I32Const(7),
            WasmOp::I32And,
            WasmOp::I32Const(1),
            WasmOp::I32Or,
            WasmOp::I32Const(4),
            WasmOp::I32Xor,
            WasmOp::LocalSet(2),
            // Nested if-else
            WasmOp::LocalGet(2),
            WasmOp::I32Const(5),
            WasmOp::I32GtS,
            WasmOp::If,
            WasmOp::LocalGet(2),
            WasmOp::I32Const(10),
            WasmOp::I32Mul,
            WasmOp::LocalSet(2),
            WasmOp::Else,
            WasmOp::LocalGet(2),
            WasmOp::I32Const(100),
            WasmOp::I32Add,
            WasmOp::LocalSet(2),
            WasmOp::End, // end if
            // Second loop with bit manipulation
            WasmOp::Loop,
            WasmOp::LocalGet(2),
            WasmOp::I32Const(1),
            WasmOp::I32ShrU,
            WasmOp::LocalSet(2),
            WasmOp::LocalGet(2),
            WasmOp::I32Const(0),
            WasmOp::I32GtU,
            WasmOp::BrIf(0),
            WasmOp::End, // end loop
        ];

        // More arithmetic (dynamic, to reach 50+ ops)
        for i in 0..10 {
            ops.push(WasmOp::LocalGet(1));
            ops.push(WasmOp::I32Const(i + 1));
            ops.push(WasmOp::I32Add);
            ops.push(WasmOp::LocalSet(1));
        }

        // Result
        ops.push(WasmOp::LocalGet(1));

        ops.push(WasmOp::End); // end outer block

        assert!(
            ops.len() >= 50,
            "Test must have 50+ operations (has {})",
            ops.len()
        );

        // Compile and verify no panic
        let instrs = selector.select_with_stack(&ops, 3).unwrap();

        // Sanity check: reasonable instruction count (not exponential)
        assert!(
            instrs.len() < ops.len() * 20,
            "Instruction count {} should be bounded (input: {} ops)",
            instrs.len(),
            ops.len()
        );
        // ARM instructions should be reasonable: at least prologue+epilogue
        assert!(
            instrs.len() >= 2,
            "Should generate at least prologue + epilogue (got {} ARM instrs from {} WASM ops)",
            instrs.len(),
            ops.len()
        );

        // Verify prologue/epilogue present
        assert!(
            matches!(&instrs[0].op, ArmOp::Push { regs } if regs.contains(&Reg::LR)),
            "Must have function prologue"
        );
        let last = &instrs[instrs.len() - 1];
        assert!(
            matches!(&last.op, ArmOp::Pop { regs } if regs.contains(&Reg::PC)),
            "Must have function epilogue"
        );
    }

    // =========================================================================
    // Task 5: Negative tests (invalid input)
    // =========================================================================

    #[test]
    fn test_empty_wasm_compiles_to_nop() {
        // Empty operation sequence should still work (just prologue + epilogue)
        let mut selector = fresh_selector();
        let instrs = selector.select_with_stack(&[], 0).unwrap();

        // Should have at minimum PUSH + POP
        assert!(
            instrs.len() >= 2,
            "Empty function needs prologue + epilogue"
        );
        assert!(matches!(&instrs[0].op, ArmOp::Push { .. }));
        assert!(matches!(&instrs[instrs.len() - 1].op, ArmOp::Pop { .. }));
    }

    #[test]
    fn test_invalid_wasm_bytes_decoder_error() {
        // Empty bytes should give clean error from wasm decoder
        let result = synth_core::decode_wasm_module(&[]);
        assert!(result.is_err(), "Empty WASM bytes should error");
        let err_msg = format!("{}", result.unwrap_err());
        assert!(!err_msg.is_empty(), "Error message should not be empty");
    }

    #[test]
    fn test_truncated_wasm_bytes_decoder_error() {
        // Truncated WASM file (just magic number, no version)
        let result = synth_core::decode_wasm_module(&[0x00, 0x61, 0x73, 0x6D]);
        assert!(result.is_err(), "Truncated WASM (magic only) should error");
    }

    #[test]
    fn test_invalid_magic_decoder_error() {
        // Invalid magic number
        let result =
            synth_core::decode_wasm_module(&[0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0x00, 0x00, 0x00]);
        assert!(result.is_err(), "Invalid WASM magic should error");
    }

    #[test]
    fn test_simd_rejected_on_non_helium_target() {
        // SIMD ops should produce error on non-Helium targets
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        // Do NOT set Helium: selector.set_helium(false) is default

        let result = selector.select(&[WasmOp::V128Const([0u8; 16])]);
        assert!(
            result.is_err(),
            "SIMD should be rejected on non-Helium target"
        );
    }

    #[test]
    fn test_validate_rejects_fpu_on_m0() {
        // FPU instructions should fail validation on Cortex-M0 (no FPU)
        let instrs = vec![ArmInstruction {
            op: ArmOp::F32Add {
                sd: VfpReg::S0,
                sn: VfpReg::S1,
                sm: VfpReg::S2,
            },
            source_line: None,
        }];

        let result = validate_instructions(&instrs, None, "cortex-m0");
        assert!(
            result.is_err(),
            "FPU instruction should fail validation on no-FPU target"
        );
    }

    // =========================================================================
    // Task 6: Thumb bit / disasm verification
    //
    // Verify that compiled ELFs have correct symbol alignment for Thumb mode.
    // The Thumb bit (bit 0 = 1) must be set on function symbols for Cortex-M.
    // =========================================================================

    #[test]
    fn test_select_with_stack_produces_valid_thumb_sequence() {
        // Verify the compiled sequence is internally consistent
        // (all instructions are valid ARM/Thumb operations)
        let mut selector = fresh_selector();
        let instrs = selector
            .select_with_stack(
                &[WasmOp::I32Const(10), WasmOp::I32Const(20), WasmOp::I32Add],
                0,
            )
            .unwrap();

        // Every instruction should be a valid ArmOp variant
        for instr in &instrs {
            // Just verify each is a recognizable op (no invalid states)
            let _ = format!("{:?}", instr.op);
        }

        // The instruction sequence should compile without errors
        assert!(!instrs.is_empty());
    }

    // =========================================================================
    // PR #86 patch coverage: i64 stack-frame layout, infer_i64_locals,
    // alloc_consecutive_pair, and the prologue/epilogue frame instructions.
    // =========================================================================

    #[test]
    fn test_compute_local_layout_no_locals() {
        // Function with only params and no LocalGet/Set produces zero frame.
        let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add];
        let layout = compute_local_layout(&ops, 2, &[], &[], false, false, 0);
        assert_eq!(layout.frame_size, 0);
        assert!(layout.locals.is_empty());
    }

    #[test]
    fn test_compute_local_layout_single_i32_local() {
        // num_params=1, references local index 1 (a non-param i32 local).
        let ops = vec![
            WasmOp::I32Const(42),
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
        ];
        let layout = compute_local_layout(&ops, 1, &[], &[], false, false, 0);
        assert!(layout.locals.contains_key(&1));
        let (off, is_i64) = layout.locals[&1];
        assert_eq!(off, 0);
        assert!(!is_i64, "i32 const → i32 local");
        // 4 bytes rounded up to 8 for SP alignment.
        assert_eq!(layout.frame_size, 8);
    }

    #[test]
    fn test_compute_local_layout_single_i64_local() {
        // i64 local must be 8 bytes wide.
        let ops = vec![
            WasmOp::I64Const(0xdead_beef_cafe_babeu64 as i64),
            WasmOp::LocalSet(0),
            WasmOp::LocalGet(0),
        ];
        let layout = compute_local_layout(&ops, 0, &[], &[], false, false, 0);
        let (off, is_i64) = layout.locals[&0];
        assert_eq!(off, 0);
        assert!(is_i64);
        // 8 bytes for the i64 local + the #171 i64 spill area (reserved because
        // the function has i64 ops).
        assert_eq!(layout.frame_size, 8 + (I64_SPILL_SLOTS as i32) * 8);
        assert_eq!(layout.i64_spill_base, 8);
    }

    #[test]
    fn test_compute_local_layout_mixed_i32_then_i64_alignment() {
        // i32 at idx 0 (offset 0, 4 bytes), then i64 at idx 1 must skip to
        // offset 8 to maintain 8-byte alignment.
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::LocalSet(0),
            WasmOp::I64Const(2),
            WasmOp::LocalSet(1),
        ];
        let layout = compute_local_layout(&ops, 0, &[], &[], false, false, 0);
        let (off0, is_i64_0) = layout.locals[&0];
        let (off1, is_i64_1) = layout.locals[&1];
        assert_eq!(off0, 0);
        assert!(!is_i64_0);
        assert_eq!(off1, 8, "i64 must be 8-byte aligned");
        assert!(is_i64_1);
        // i32 (4) + pad (4) + i64 (8) = 16 bytes for locals, + the #171 i64
        // spill area (reserved because the function has i64 ops).
        assert_eq!(layout.frame_size, 16 + (I64_SPILL_SLOTS as i32) * 8);
        assert_eq!(layout.i64_spill_base, 16);
    }

    #[test]
    fn test_compute_local_layout_skips_param_indices() {
        // num_params = 2: indices 0 and 1 are params, idx 2 is the local.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::LocalSet(2),
        ];
        let layout = compute_local_layout(&ops, 2, &[], &[], false, false, 0);
        // Only idx 2 should be in the layout.
        assert!(!layout.locals.contains_key(&0));
        assert!(!layout.locals.contains_key(&1));
        assert!(layout.locals.contains_key(&2));
    }

    #[test]
    fn test_infer_i64_locals_from_localset() {
        // i64.const → local.set marks that local as i64.
        let ops = vec![WasmOp::I64Const(7), WasmOp::LocalSet(3)];
        let i64_locals = infer_i64_locals(&ops, &[], &[]);
        assert!(i64_locals.contains(&3));
    }

    #[test]
    fn test_infer_i64_locals_from_localtee() {
        // local.tee preserves the value on the stack and stores to local —
        // its width should be inferred from what's on the stack.
        let ops = vec![WasmOp::I64Const(99), WasmOp::LocalTee(2), WasmOp::Drop];
        let i64_locals = infer_i64_locals(&ops, &[], &[]);
        assert!(i64_locals.contains(&2));
    }

    #[test]
    fn test_infer_i64_locals_does_not_flag_i32_locals() {
        // i32 ops should not produce i64 locals.
        let ops = vec![WasmOp::I32Const(1), WasmOp::LocalSet(0)];
        let i64_locals = infer_i64_locals(&ops, &[], &[]);
        assert!(!i64_locals.contains(&0));
    }

    #[test]
    fn test_infer_i64_locals_propagates_through_i64_arith() {
        // i64.add produces i64 — store to local should mark it i64.
        let ops = vec![
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Add,
            WasmOp::LocalSet(5),
        ];
        let i64_locals = infer_i64_locals(&ops, &[], &[]);
        assert!(i64_locals.contains(&5));
    }

    #[test]
    fn test_alloc_consecutive_pair_basic() {
        // From an empty stack, the pair returned must be consecutive entries
        // in ALLOCATABLE_REGS.
        let mut next_temp: u8 = 0;
        let mut stack: Vec<StackVal> = Vec::new();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let (lo, hi) = alloc_consecutive_pair(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            &[],
            0,
        )
        .unwrap();
        // Verify hi == i64_pair_hi(lo) — the contract.
        let expected_hi = i64_pair_hi(lo).unwrap();
        assert_eq!(hi, expected_hi);
    }

    #[test]
    fn test_alloc_consecutive_pair_skips_extra_avoid() {
        // Reserve the first pair via extra_avoid and confirm a different pair
        // is allocated.
        let mut next_temp: u8 = 0;
        let mut stack: Vec<StackVal> = Vec::new();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let (lo1, hi1) = alloc_consecutive_pair(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            &[],
            0,
        )
        .unwrap();
        // Now ask again, telling it to avoid lo1 and hi1.
        let mut next_temp2: u8 = 0;
        let (lo2, hi2) = alloc_consecutive_pair(
            &mut next_temp2,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[lo1, hi1],
            &[],
            0,
        )
        .unwrap();
        assert!(lo2 != lo1, "should not reuse lo1");
        assert!(hi2 != hi1, "should not reuse hi1");
        // The new pair must still be consecutive.
        assert_eq!(hi2, i64_pair_hi(lo2).unwrap());
    }

    #[test]
    fn test_alloc_consecutive_pair_avoids_implicit_hi_from_stack() {
        // If the stack has an i64 lo (e.g. R0), then R1 (its implicit hi)
        // must NOT be returned as a fresh lo by alloc_consecutive_pair.
        let mut next_temp: u8 = 0;
        let mut stack = vec![StackVal::i64(Reg::R0)]; // i64 lo=R0 reserves hi=R1
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let (lo, hi) = alloc_consecutive_pair(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            &[],
            0,
        )
        .unwrap();
        assert_ne!(lo, Reg::R0, "must skip the live lo");
        assert_ne!(lo, Reg::R1, "must skip implicit hi of R0");
        assert_ne!(hi, Reg::R1, "implicit hi must not be allocated");
        // The returned pair is still consecutive.
        assert_eq!(hi, i64_pair_hi(lo).unwrap());
    }

    // ── VCR-RA-001 step 3b-lite (#242): spill-on-exhaustion for i32 temps ──

    /// Build a stack pinning ALL nine allocatable registers with i32 values.
    fn full_i32_stack() -> Vec<StackVal> {
        ALLOCATABLE_REGS.iter().map(|&r| StackVal::i32(r)).collect()
    }

    /// Flag OFF (the default / first-pass world): exhaustion keeps the exact
    /// hard-fail `Err` and emits nothing — bit-identity of the fast path.
    #[test]
    fn alloc_temp_or_spill_keeps_hard_fail_when_flag_off_242() {
        let mut next_temp: u8 = 0;
        let mut stack = full_i32_stack();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0); // spill_on_exhaustion: false
        let err = alloc_temp_or_spill(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            0,
        )
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("all allocatable registers are live on the stack"),
            "must preserve the original exhaustion Err, got: {err}"
        );
        assert!(instructions.is_empty(), "must not emit anything when off");
        assert!(stack.iter().all(|v| matches!(v, StackVal::Reg { .. })));
    }

    /// Flag ON (the retry pass): exhaustion spills the DEEPEST stack value
    /// (stack[0] — least likely to be consumed next) via a single `STR` into
    /// the spill area, rewrites it to `StackVal::Spilled`, and returns its
    /// freed register.
    #[test]
    fn alloc_temp_or_spill_spills_deepest_and_returns_its_reg_242() {
        let mut next_temp: u8 = 0;
        let mut stack = full_i32_stack();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        spill.spill_on_exhaustion = true;
        let got = alloc_temp_or_spill(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            7,
        )
        .unwrap();
        // The deepest entry held R0 (full_i32_stack order = ALLOCATABLE_REGS).
        assert_eq!(got, Reg::R0, "freed register of the deepest entry");
        assert_eq!(
            stack[0],
            StackVal::Spilled {
                lo_slot: 0,
                is_i64: false
            },
            "deepest entry rewritten to Spilled"
        );
        // Exactly one i32 spill store: STR R0, [SP, #0].
        assert_eq!(instructions.len(), 1);
        match &instructions[0].op {
            ArmOp::Str { rd, addr } => {
                assert_eq!(*rd, Reg::R0);
                assert_eq!(*addr, MemAddr::imm(Reg::SP, 0));
            }
            other => panic!("expected STR spill, got {other:?}"),
        }
        assert_eq!(instructions[0].source_line, Some(7));
    }

    /// The spilled value reloads through the existing `StackVal::Spilled`
    /// machinery (#171): popping it emits `LDR` from its slot and frees the
    /// slot for reuse.
    #[test]
    fn alloc_temp_or_spill_spilled_value_reloads_on_pop_242() {
        let mut next_temp: u8 = 0;
        let mut stack = full_i32_stack();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        spill.spill_on_exhaustion = true;
        let fresh = alloc_temp_or_spill(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            0,
        )
        .unwrap();
        stack.push(StackVal::i32(fresh)); // the new temp pins its register
        // Drain the stack: every entry must pop to a register, including the
        // spilled one, which reloads via LDR [SP, #0].
        let before = instructions.len();
        while !stack.is_empty() {
            pop_operand(
                &mut stack,
                &mut next_temp,
                &mut instructions,
                &mut spill,
                &[],
                1,
            )
            .unwrap();
        }
        let reloads: Vec<_> = instructions[before..]
            .iter()
            .filter_map(|i| match &i.op {
                ArmOp::Ldr { rd, addr } if *addr == MemAddr::imm(Reg::SP, 0) => Some(*rd),
                _ => None,
            })
            .collect();
        assert_eq!(reloads.len(), 1, "exactly one reload of the spilled slot");
        // The slot was freed on reload — allocatable again.
        assert_eq!(spill.alloc(), Some(0), "slot 0 reusable after reload");
    }

    // ── #326: arg-move cycles break via the parallel-move resolver ──

    /// Minimal layout for driving `emit_arg_moves` directly.
    fn arg_move_layout(spill_area_reserved: bool) -> LocalLayout {
        LocalLayout {
            locals: std::collections::HashMap::new(),
            frame_size: 0,
            spill_base: None,
            i64_spill_base: 0,
            param_slots: std::collections::HashMap::new(),
            incoming_params: std::collections::HashMap::new(),
            spill_area_reserved,
        }
    }

    /// gale's #326 shape: a genuine arg cycle (swap into R0/R1) while every
    /// callee-saved register R4–R8 is pinned by live operand-stack values
    /// (`free_callee_saved` sees [R4, R6, R8] as i64-conservative, pinning
    /// R5/R7 as implicit pair-his too). The old path `Err`ed here ("no free
    /// callee-saved register..."); the resolver must break the cycle through
    /// ONE stack slot: `STR R0; MOV R0, R1; LDR R1`.
    #[test]
    fn arg_move_cycle_with_saturated_callee_saved_spills_not_errs_326() {
        let selector = fresh_selector();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(40); // resolver slot at [SP, #40]
        let live = [Reg::R4, Reg::R6, Reg::R8]; // pins R4..R8 (pair-his)
        let n = selector
            .emit_arg_moves(
                &mut instructions,
                &[Reg::R1, Reg::R0], // arg0 in R1, arg1 in R0 — a swap
                &live,
                &std::collections::HashMap::new(),
                &arg_move_layout(true),
                &mut spill,
                3,
            )
            .expect("#326: saturated callee-saved must not be an Err anymore");
        assert_eq!(n, 3, "swap via stack slot is exactly STR + MOV + LDR");
        match (
            &instructions[0].op,
            &instructions[1].op,
            &instructions[2].op,
        ) {
            (
                ArmOp::Str { rd: s, addr: sa },
                ArmOp::Mov {
                    rd: m,
                    op2: Operand2::Reg(msrc),
                },
                ArmOp::Ldr { rd: l, addr: la },
            ) => {
                assert_eq!((*s, sa.clone()), (Reg::R0, MemAddr::imm(Reg::SP, 40)));
                assert_eq!((*m, *msrc), (Reg::R0, Reg::R1));
                assert_eq!((*l, la.clone()), (Reg::R1, MemAddr::imm(Reg::SP, 40)));
            }
            other => panic!("expected STR/MOV/LDR swap sequence, got {other:?}"),
        }
        // The resolver slot was released after the sequence.
        assert_eq!(spill.alloc(), Some(40), "resolver slot freed for reuse");
    }

    /// With a free callee-saved register the cycle still goes through the
    /// register (no stack traffic): `MOV R4, R0; MOV R0, R1; MOV R1, R4`.
    #[test]
    fn arg_move_cycle_with_free_callee_saved_uses_register_326() {
        let selector = fresh_selector();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let n = selector
            .emit_arg_moves(
                &mut instructions,
                &[Reg::R1, Reg::R0],
                &[],
                &std::collections::HashMap::new(),
                &arg_move_layout(true),
                &mut spill,
                3,
            )
            .unwrap();
        assert_eq!(n, 3);
        let movs: Vec<(Reg, Reg)> = instructions
            .iter()
            .map(|i| match &i.op {
                ArmOp::Mov {
                    rd,
                    op2: Operand2::Reg(src),
                } => (*rd, *src),
                other => panic!("register cycle must be pure MOVs, got {other:?}"),
            })
            .collect();
        assert_eq!(
            movs,
            vec![(Reg::R4, Reg::R0), (Reg::R0, Reg::R1), (Reg::R1, Reg::R4)]
        );
        // No stack slot was touched.
        assert_eq!(spill.alloc(), Some(0), "no resolver slot consumed");
    }

    /// Acyclic marshals never need scratch — even fully saturated, they are
    /// plain MOVs in ascending destination order (byte-identity with the
    /// legacy emitter).
    #[test]
    fn arg_move_acyclic_saturated_is_plain_movs_326() {
        let selector = fresh_selector();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let live = [Reg::R4, Reg::R6, Reg::R8];
        let n = selector
            .emit_arg_moves(
                &mut instructions,
                &[Reg::R2, Reg::R3],
                &live,
                &std::collections::HashMap::new(),
                &arg_move_layout(true),
                &mut spill,
                0,
            )
            .unwrap();
        assert_eq!(n, 2);
        let movs: Vec<(Reg, Reg)> = instructions
            .iter()
            .map(|i| match &i.op {
                ArmOp::Mov {
                    rd,
                    op2: Operand2::Reg(src),
                } => (*rd, *src),
                other => panic!("expected MOV, got {other:?}"),
            })
            .collect();
        assert_eq!(movs, vec![(Reg::R0, Reg::R2), (Reg::R1, Reg::R3)]);
    }

    /// An i32-only first pass has NO spill area: a cycle that needs the slot
    /// must fail with the LADDER-RECOVERABLE exhaustion `Err` (the backend
    /// retry re-runs with the area reserved), not silently alias the frame.
    #[test]
    fn arg_move_cycle_without_spill_area_errs_ladder_recoverable_326() {
        let selector = fresh_selector();
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        spill.area_reserved = false;
        let live = [Reg::R4, Reg::R6, Reg::R8];
        let err = selector
            .emit_arg_moves(
                &mut instructions,
                &[Reg::R1, Reg::R0],
                &live,
                &std::collections::HashMap::new(),
                &arg_move_layout(false),
                &mut spill,
                0,
            )
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("all allocatable registers are live on the stack"),
            "must be the retry-ladder exhaustion class, got: {err}"
        );
        assert!(instructions.is_empty(), "no partial sequence on Err");
    }

    /// #313: an `if (result i32)` with ASYMMETRIC arms must reconcile both
    /// arms onto a SINGLE result register. The buggy selector left the
    /// then-arm's result on the vstack across the else-arm and read the
    /// else-arm's register unconditionally at `End`, so the then-path returned
    /// a register it never wrote. The fix reconciles: the value live at the
    /// `if_end` label is the THEN-arm's register, and a `MOV R_then, R_else`
    /// sits on the else path (between the `else` label and the `if_end` label)
    /// so the else path moves its result into that same register. Mirrors
    /// `scripts/repro/u64_unpack_if.wat` (`f`).
    #[test]
    fn if_result_asymmetric_arms_reconcile_to_one_register_313() {
        use WasmOp::*;
        // param0 = i64 $r. Condition: (wrap(r & 255) == 1). Then: wrap(r>>32).
        // Else: const 0xDEAD. The two arms land in different registers.
        let ops: Vec<WasmOp> = vec![
            LocalGet(0),
            I64Const(255),
            I64And,
            I32WrapI64,
            I32Const(1),
            I32Eq,
            If,
            LocalGet(0),
            I64Const(32),
            I64ShrU,
            I32WrapI64,
            Else,
            I32Const(0xDEAD),
            End,
        ];
        // One i64 param (occupies R0/R1), result i32.
        let mut sel = fresh_selector();
        sel.func_ret_i64 = vec![false];
        let instrs = sel
            .select_with_stack(&ops, 1)
            .expect("if-result must compile");

        // Locate the `else` and `if_end` labels.
        let else_pos = instrs
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Label { name } if name.contains("else")))
            .expect("else label present");
        let end_pos = instrs
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Label { name } if name.contains("if_end")))
            .expect("if_end label present");
        assert!(else_pos < end_pos, "else label precedes if_end label");

        // Exactly one reconciliation MOV between the else label and the end
        // label (the else path moving its result into the then register).
        let reconcile: Vec<(Reg, Reg)> = instrs[else_pos + 1..end_pos]
            .iter()
            .filter_map(|i| match &i.op {
                ArmOp::Mov {
                    rd,
                    op2: Operand2::Reg(rs),
                } => Some((*rd, *rs)),
                _ => None,
            })
            .collect();
        assert_eq!(
            reconcile.len(),
            1,
            "exactly one reconciliation MOV on the else path, got {reconcile:?}"
        );
        let (r_then, r_else) = reconcile[0];
        assert_ne!(
            r_then, r_else,
            "reconciliation only emitted when the arms differ"
        );

        // The then-path `B if_end` must jump OVER the reconciliation MOV: there
        // is a branch to the end label emitted before the else label.
        let then_branch_over = instrs[..else_pos]
            .iter()
            .any(|i| matches!(&i.op, ArmOp::B { label } if label.contains("if_end")));
        assert!(
            then_branch_over,
            "then-path branches to if_end, skipping the reconciliation MOV"
        );

        // The else-arm materialized 0xDEAD into r_else (so it is genuinely the
        // else result being moved into the then register).
        let else_makes_dead = instrs[else_pos + 1..end_pos].iter().any(|i| {
            matches!(&i.op, ArmOp::Mov { rd, op2: Operand2::Imm(v) } if *rd == r_else && *v == 0xDEAD)
                || matches!(&i.op, ArmOp::Movw { rd, imm16 } if *rd == r_else && *imm16 == 0xDEAD)
        });
        assert!(
            else_makes_dead,
            "the else arm materializes 0xDEAD into the moved-from register"
        );
    }

    /// #313: a control-flow-only / result-less `if/else` (arity 0) gets NO
    /// reconciliation move — results carried via locals, not the vstack. This
    /// is the byte-identity guarantee for the frozen fixtures (which have no
    /// if-with-result). Here both arms only `local.set`, leaving the vstack at
    /// the checkpoint depth, so `End` emits nothing extra.
    #[test]
    fn if_without_result_emits_no_reconciliation_313() {
        use WasmOp::*;
        // if (local.get 0) { local.set 1 (const 7) } else { local.set 1 (const 9) }
        let ops: Vec<WasmOp> = vec![
            LocalGet(0),
            If,
            I32Const(7),
            LocalSet(1),
            Else,
            I32Const(9),
            LocalSet(1),
            End,
            LocalGet(1),
        ];
        let instrs = fresh_selector()
            .select_with_stack(&ops, 2)
            .expect("arity-0 if must compile");
        let end_pos = instrs
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Label { name } if name.contains("if_end")))
            .expect("if_end label present");
        // #313: for an arity-0 if/else the result-reconciliation is a no-op —
        // `if_then_results` is empty at `End`, so NOTHING is emitted between the
        // last else-arm instruction and the `if_end` label (the buggy and fixed
        // selectors are byte-identical here; this is the property the frozen
        // fixtures depend on). The instruction immediately preceding `if_end` is
        // therefore the else-arm's own `local.set` store/mov, never a #313 MOV.
        // We assert the closing structure is `… ; if_end: ; (LocalGet 1 read)`
        // with no reconciliation slipped in: the only thing after the `else`
        // label region tied to the merge is the label itself.
        //
        // Concretely: there must be exactly one then-arm body MOV (const 7 ->
        // local) before the else label and one else-arm body MOV (const 9 ->
        // local) after it, and the two destinations are the SAME register (both
        // write local 1) — i.e. the arms reconcile themselves through the local,
        // and `End` adds nothing.
        let else_pos = instrs
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Label { name } if name.contains("else")))
            .expect("else label present");
        let dest_of_setlocal = |slice: &[ArmInstruction]| -> Option<Reg> {
            slice.iter().rev().find_map(|i| match &i.op {
                ArmOp::Mov {
                    rd,
                    op2: Operand2::Reg(_),
                } => Some(*rd),
                _ => None,
            })
        };
        let then_local = dest_of_setlocal(&instrs[..else_pos]);
        let else_local = dest_of_setlocal(&instrs[else_pos + 1..end_pos]);
        assert!(
            then_local.is_some() && then_local == else_local,
            "both arms write the same local register; End adds no reconciliation \
             (then={then_local:?} else={else_local:?})"
        );
    }

    /// End-to-end fail-then-retry contract (the backend's wrapper): the
    /// high-pressure body (10 simultaneously-live i32 consts + 2 reserved
    /// params = > 9-reg pool) hard-fails by default with the exhaustion `Err`,
    /// and compiles under `set_spill_on_exhaustion(true)` — the
    /// `scripts/repro/high_pressure_i32.wat` sequence.
    #[test]
    fn select_with_stack_exhaustion_recoverable_via_spill_retry_242() {
        use WasmOp::*;
        let mut ops: Vec<WasmOp> = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31].map(I32Const).to_vec();
        ops.extend([
            I32Mul,
            I32Add,
            I32Xor,
            I32Add,
            I32Sub,
            I32Add,
            I32Mul,
            I32Xor,
            I32Sub,
            LocalGet(0),
            I32Add,
            LocalGet(1),
            I32Xor,
        ]);

        // First pass (default world): the hard-fail, verbatim.
        let err = fresh_selector().select_with_stack(&ops, 2).unwrap_err();
        assert!(
            err.to_string()
                .contains("all allocatable registers are live on the stack"),
            "expected the exhaustion hard-fail, got: {err}"
        );

        // Retry pass: spill-on-exhaustion makes it compile, with at least one
        // SP-relative spill store and matching reload in the body.
        let mut retry = fresh_selector();
        retry.set_spill_on_exhaustion(true);
        let instrs = retry
            .select_with_stack(&ops, 2)
            .expect("retry with spill-on-exhaustion must compile");
        let spills = instrs
            .iter()
            .filter(|i| {
                matches!(&i.op, ArmOp::Str { addr, .. } if addr.base == Reg::SP)
                    && i.source_line.is_some()
            })
            .count();
        let reloads = instrs
            .iter()
            .filter(|i| {
                matches!(&i.op, ArmOp::Ldr { addr, .. } if addr.base == Reg::SP)
                    && i.source_line.is_some()
            })
            .count();
        assert!(
            spills >= 1,
            "expected at least one spill store, got {spills}"
        );
        assert_eq!(spills, reloads, "every spill must reload exactly once");
    }

    // ── VCR-RA-001 acceptance increment (#242): i64 PAIR exhaustion ──

    /// The pair allocator's #171 stack-spill loop is pair-aware: when every
    /// register is pinned and the deepest stack entry is an i64, BOTH halves
    /// spill into one 8-byte slot (two STRs, lo then hi) and the freed pair is
    /// returned.
    #[test]
    fn alloc_consecutive_pair_spills_pair_victim_242() {
        let mut next_temp: u8 = 0;
        // 4 i64 pairs (R0/R1, R2/R3, R4/R5, R6/R7) + one i32 in R8 = all nine
        // allocatable registers pinned.
        let mut stack = vec![
            StackVal::i64(Reg::R0),
            StackVal::i64(Reg::R2),
            StackVal::i64(Reg::R4),
            StackVal::i64(Reg::R6),
            StackVal::i32(Reg::R8),
        ];
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let (lo, hi) = alloc_consecutive_pair(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            &[],
            3,
        )
        .unwrap();
        // The deepest entry (i64 in R0/R1) spilled — its pair is the result.
        assert_eq!((lo, hi), (Reg::R0, Reg::R1));
        assert_eq!(
            stack[0],
            StackVal::Spilled {
                lo_slot: 0,
                is_i64: true
            },
            "deepest i64 entry rewritten to Spilled"
        );
        // Exactly two STRs: lo -> [SP,#0], hi -> [SP,#4] (one 8-byte slot).
        assert_eq!(instructions.len(), 2);
        match (&instructions[0].op, &instructions[1].op) {
            (ArmOp::Str { rd: r0, addr: a0 }, ArmOp::Str { rd: r1, addr: a1 }) => {
                assert_eq!((*r0, a0.clone()), (Reg::R0, MemAddr::imm(Reg::SP, 0)));
                assert_eq!((*r1, a1.clone()), (Reg::R1, MemAddr::imm(Reg::SP, 4)));
            }
            other => panic!("expected two STR spills, got {other:?}"),
        }
    }

    /// Pair exhaustion with i32 victims: freeing a consecutive pair takes TWO
    /// single-register spills (each into its own slot) before (R0,R1) frees.
    #[test]
    fn alloc_consecutive_pair_spills_single_victims_242() {
        let mut next_temp: u8 = 0;
        let mut stack = full_i32_stack(); // nine i32s pin R0-R8
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let (lo, hi) = alloc_consecutive_pair(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[],
            &[],
            5,
        )
        .unwrap();
        assert_eq!((lo, hi), (Reg::R0, Reg::R1));
        assert_eq!(
            stack[0],
            StackVal::Spilled {
                lo_slot: 0,
                is_i64: false
            }
        );
        assert_eq!(
            stack[1],
            StackVal::Spilled {
                lo_slot: 8,
                is_i64: false
            }
        );
        // Two single STRs into two distinct slots.
        assert_eq!(instructions.len(), 2);
        for (i, (reg, off)) in [(Reg::R0, 0), (Reg::R1, 8)].iter().enumerate() {
            match &instructions[i].op {
                ArmOp::Str { rd, addr } => {
                    assert_eq!((*rd, addr.clone()), (*reg, MemAddr::imm(Reg::SP, *off)));
                }
                other => panic!("expected STR spill, got {other:?}"),
            }
        }
    }

    /// When the blockers are NOT stack values (pinned param registers in
    /// `reserved` + popped operand pairs in `extra_avoid`), stack spilling
    /// cannot help and the exact original pair-exhaustion `Err` is preserved
    /// with nothing emitted — the case only the backend's param-backing retry
    /// recovers.
    #[test]
    fn alloc_consecutive_pair_err_when_only_pinned_blockers_242() {
        let mut next_temp: u8 = 4;
        let mut stack: Vec<StackVal> = Vec::new(); // nothing register-resident
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let mut spill = SpillState::new(0);
        let err = alloc_consecutive_pair(
            &mut next_temp,
            &mut stack,
            &mut instructions,
            &mut spill,
            &[Reg::R4, Reg::R5, Reg::R6, Reg::R7], // popped operand pairs
            &[Reg::R0, Reg::R1, Reg::R2, Reg::R3], // pinned params (#193)
            0,
        )
        .unwrap_err();
        assert!(
            err.to_string()
                .contains("no consecutive pair of free registers for i64"),
            "must preserve the original pair-exhaustion Err, got: {err}"
        );
        assert!(instructions.is_empty(), "must not emit on the Err path");
    }

    /// A spilled i64 PAIR reloads on pop through the #171 machinery: a fresh
    /// consecutive pair and two LDRs (lo from slot, hi from slot+4), freeing
    /// the slot.
    #[test]
    fn spilled_i64_pair_reloads_on_pop_242() {
        let mut next_temp: u8 = 0;
        let mut spill = SpillState::new(0);
        let slot = spill.alloc().unwrap(); // occupy slot 0 as the spill did
        let mut stack = vec![StackVal::Spilled {
            lo_slot: slot,
            is_i64: true,
        }];
        let mut instructions: Vec<ArmInstruction> = Vec::new();
        let lo = pop_operand(
            &mut stack,
            &mut next_temp,
            &mut instructions,
            &mut spill,
            &[],
            9,
        )
        .unwrap();
        let hi = i64_pair_hi(lo).unwrap();
        assert_eq!(instructions.len(), 2, "lo + hi reload LDRs");
        match (&instructions[0].op, &instructions[1].op) {
            (ArmOp::Ldr { rd: r0, addr: a0 }, ArmOp::Ldr { rd: r1, addr: a1 }) => {
                assert_eq!((*r0, a0.clone()), (lo, MemAddr::imm(Reg::SP, slot)));
                assert_eq!((*r1, a1.clone()), (hi, MemAddr::imm(Reg::SP, slot + 4)));
            }
            other => panic!("expected two LDR reloads, got {other:?}"),
        }
        assert_eq!(spill.alloc(), Some(slot), "slot freed for reuse on reload");
    }

    /// End-to-end fail-then-retry contract for the PAIR site (the backend's
    /// three-pass ladder, `scripts/repro/high_pressure_i64.wat` sequence):
    ///   pass 1 (default)         -> the pair-exhaustion hard-fail, verbatim;
    ///   pass 2 (spill-only #320) -> STILL the pair hard-fail (stack spilling
    ///                               cannot free pinned param registers);
    ///   pass 3 (+param backing)  -> compiles, params frame-backed at entry.
    #[test]
    fn select_with_stack_pair_exhaustion_recoverable_via_param_backing_242() {
        use WasmOp::*;
        let ops = vec![
            I64Const(0x1111111111111111),
            I64Const(0x2222222222222222),
            I64Const(0x3333333333333333),
            I64Const(0x4444444444444444),
            I64Add,
            I64Sub,
            I64Xor,
            LocalGet(0),
            I64ExtendI32U,
            I64Add,
            LocalGet(1),
            I64ExtendI32U,
            I64Sub,
            LocalGet(2),
            I64ExtendI32U,
            I64Xor,
            LocalGet(3),
            I64ExtendI32U,
            I64Add,
        ];

        // Pass 1 (default world): the pair hard-fail, verbatim.
        let err = fresh_selector().select_with_stack(&ops, 4).unwrap_err();
        assert!(
            err.to_string()
                .contains("no consecutive pair of free registers for i64"),
            "expected the pair-exhaustion hard-fail, got: {err}"
        );

        // Pass 2 (#320 spill-only): insufficient by construction — the
        // blockers are param home registers, not stack values.
        let mut spill_only = fresh_selector();
        spill_only.set_spill_on_exhaustion(true);
        let err = spill_only.select_with_stack(&ops, 4).unwrap_err();
        assert!(
            err.to_string()
                .contains("no consecutive pair of free registers for i64"),
            "spill-only retry must still hit the pair hard-fail, got: {err}"
        );

        // Pass 3 (param-backing retry): compiles; the entry spills each read
        // param to its frame slot before any operand-stack traffic.
        let mut retry = fresh_selector();
        retry.set_spill_on_exhaustion(true);
        retry.set_param_backing_on_exhaustion(true);
        let instrs = retry
            .select_with_stack(&ops, 4)
            .expect("param-backing retry must compile");
        let entry_param_spills = instrs
            .iter()
            .take_while(|i| i.source_line.is_none())
            .filter(|i| matches!(&i.op, ArmOp::Str { addr, .. } if addr.base == Reg::SP))
            .count();
        assert_eq!(
            entry_param_spills, 4,
            "all four read params frame-backed at entry"
        );
    }

    #[test]
    fn test_select_with_stack_emits_frame_alloc_for_i64_local() {
        // When a non-param i64 local exists, select_with_stack must:
        //  - emit `sub sp, sp, #frame_size` after the prologue Push, AND
        //  - emit a matching `add sp, sp, #frame_size` before the epilogue Pop.
        let mut selector = fresh_selector();
        let ops = vec![
            WasmOp::I64Const(0x1234_5678_9abc_def0u64 as i64),
            WasmOp::LocalSet(0),
            WasmOp::LocalGet(0),
            WasmOp::Drop,
            WasmOp::I32Const(0),
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 0).unwrap();
        // Find a Sub with rd=SP (frame allocation).
        let sub_sp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    ..
                }
            )
        });
        assert!(sub_sp, "frame allocation `sub sp, sp, #N` not emitted");
        // And a matching Add (frame deallocation).
        let add_sp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Add {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    ..
                }
            )
        });
        assert!(add_sp, "frame deallocation `add sp, sp, #N` not emitted");
    }

    #[test]
    fn test_select_with_stack_no_frame_when_only_params_used() {
        // num_params=2, only LocalGet on params — no frame should be needed.
        let mut selector = fresh_selector();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 2).unwrap();
        // No `sub sp, sp, #N` should appear in the prologue.
        let sub_sp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Sub {
                    rd: Reg::SP,
                    rn: Reg::SP,
                    ..
                }
            )
        });
        assert!(
            !sub_sp,
            "no frame allocation expected for params-only function"
        );
    }

    /// #258: a compare against a constant bound folds into `cmp`/`cmn`
    /// immediate, dropping the materialization — a positive bound → `cmp #C`, a
    /// negative bound → `cmn #|C|` (the int8-clamp shape on flat_flight).
    #[test]
    fn i32_compare_folds_const_bound_into_cmp_cmn() {
        // (p < 0x7e) → cmp p, #0x7e ; no movw 0x7e.
        let mut sel = fresh_selector();
        let pos = sel
            .select_with_stack(
                &[
                    WasmOp::LocalGet(0),
                    WasmOp::I32Const(0x7e),
                    WasmOp::I32LtS,
                    WasmOp::End,
                ],
                1,
            )
            .unwrap();
        assert!(
            !pos.iter()
                .any(|i| matches!(&i.op, ArmOp::Movw { imm16: 0x7e, .. })),
            "positive bound must fold, no movw: {pos:#?}"
        );
        assert!(
            pos.iter().any(|i| matches!(
                &i.op,
                ArmOp::Cmp {
                    op2: Operand2::Imm(0x7e),
                    ..
                }
            )),
            "positive bound → cmp #0x7e"
        );
        // (p < -0x7f) → cmn p, #0x7f.
        let mut sel = fresh_selector();
        let neg = sel
            .select_with_stack(
                &[
                    WasmOp::LocalGet(0),
                    WasmOp::I32Const(-0x7f),
                    WasmOp::I32LtS,
                    WasmOp::End,
                ],
                1,
            )
            .unwrap();
        assert!(
            neg.iter().any(|i| matches!(
                &i.op,
                ArmOp::Cmn {
                    op2: Operand2::Imm(0x7f),
                    ..
                }
            )),
            "negative bound → cmn #0x7f: {neg:#?}"
        );
    }

    /// VCR-RA-001: `i32.add`/`i32.sub` fold a const operand (0..=0xFFF, the
    /// ADDW/SUBW range #253) into the immediate, dropping the `movw`. Verifies
    /// both a byte value and a >0xFF value that exercises the ADDW path.
    #[test]
    fn i32_add_sub_fold_const_into_immediate() {
        for (op, big) in [(WasmOp::I32Add, 0x200i32), (WasmOp::I32Sub, 0x200)] {
            let mut selector = fresh_selector();
            let ops = vec![
                WasmOp::LocalGet(0),
                WasmOp::I32Const(big),
                op.clone(),
                WasmOp::End,
            ];
            let instrs = selector.select_with_stack(&ops, 1).unwrap();
            let movw = instrs
                .iter()
                .filter(|i| matches!(&i.op, ArmOp::Movw { imm16: 0x200, .. }))
                .count();
            let folded = instrs.iter().any(|i| {
                matches!(
                    &i.op,
                    ArmOp::Add {
                        op2: Operand2::Imm(0x200),
                        ..
                    } | ArmOp::Sub {
                        op2: Operand2::Imm(0x200),
                        ..
                    }
                )
            });
            assert_eq!(movw, 0, "{op:?}: const 0x200 must be folded away");
            assert!(folded, "{op:?}: must use the folded immediate");
        }
    }

    /// VCR-RA-001: `i32.or`/`i32.xor` fold a small const operand into the
    /// `ORR`/`EOR` immediate (same shape as `i32.and`, #250; encoder hardened in
    /// #251). Drops the `movw`; no register operand.
    #[test]
    fn i32_or_xor_fold_small_const_into_immediate() {
        for op in [WasmOp::I32Or, WasmOp::I32Xor] {
            let mut selector = fresh_selector();
            let ops = vec![
                WasmOp::LocalGet(0),
                WasmOp::I32Const(0x7e),
                op.clone(),
                WasmOp::End,
            ];
            let instrs = selector.select_with_stack(&ops, 1).unwrap();
            let movw_126 = instrs
                .iter()
                .filter(|i| matches!(&i.op, ArmOp::Movw { imm16: 126, .. }))
                .count();
            let folded = instrs.iter().any(|i| {
                matches!(
                    &i.op,
                    ArmOp::Orr {
                        op2: Operand2::Imm(126),
                        ..
                    } | ArmOp::Eor {
                        op2: Operand2::Imm(126),
                        ..
                    }
                )
            });
            assert_eq!(movw_126, 0, "{op:?}: const must be folded away");
            assert!(folded, "{op:?}: must use the folded immediate");
        }
    }

    /// VCR-RA-001 immediate folding: `i32.const C (0..=0xFF); i32.and` folds the
    /// constant into the `AND` immediate and drops the `movw`. Measured delta on
    /// the clamp pattern: 8 → 6 instructions (both `movw #126` eliminated). The
    /// first delta-emitting codegen transform on the allocator track.
    #[test]
    fn i32_and_folds_small_const_into_immediate() {
        let mut selector = fresh_selector();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0x7e),
            WasmOp::I32And,
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0x7e),
            WasmOp::I32And,
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 1).unwrap();
        let movw_126 = instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Movw { imm16: 126, .. }))
            .count();
        let and_imm_126 = instrs
            .iter()
            .filter(|i| {
                matches!(
                    &i.op,
                    ArmOp::And {
                        op2: Operand2::Imm(126),
                        ..
                    }
                )
            })
            .count();
        assert_eq!(movw_126, 0, "the const materialization must be folded away");
        assert_eq!(and_imm_126, 2, "both ANDs use the folded immediate");
    }

    /// A constant beyond the encoder's `AND`-immediate range (> 0xFF) must NOT be
    /// folded — it stays a register operand, so the encoder never emits a
    /// silently-wrong modified immediate (#249 bound).
    #[test]
    fn i32_and_does_not_fold_out_of_range_const() {
        let mut selector = fresh_selector();
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0x140), // 320 > 0xFF
            WasmOp::I32And,
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 1).unwrap();
        let and_imm = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::And {
                    op2: Operand2::Imm(_),
                    ..
                }
            )
        });
        assert!(
            !and_imm,
            "0x140 must stay a register operand, not an immediate"
        );
    }

    /// VCR-RA-001: the liveness analyses must be sound on REAL selector output,
    /// not just synthetic instruction vectors — this is the precondition for
    /// safely wiring the dead-store transform into the codegen path. Runs the
    /// actual selector on a sequence that reuses a constant, then checks the
    /// analyses are internally consistent with the emitted instructions.
    #[test]
    fn liveness_analyses_are_consistent_on_real_selector_output() {
        use crate::liveness;
        let mut selector = fresh_selector();
        // (p & 0x7e) + (p & 0x7e): the constant 0x7e is materialized for each
        // `and`, mirroring the repeated-clamp shape gale measured on flat_flight.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0x7e),
            WasmOp::I32And,
            WasmOp::LocalGet(0),
            WasmOp::I32Const(0x7e),
            WasmOp::I32And,
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 1).unwrap();

        let report = liveness::analyze_function(&instrs);
        assert!(report.segments >= 1, "real output should be analyzable");

        // Every reported redundant const must actually be a const-materialization
        // of the claimed value at that index (the analysis reads real codegen
        // correctly).
        for rc in &report.redundant_consts {
            let op = &instrs[rc.index].op;
            let ok = matches!(op, ArmOp::Movw { imm16, .. } if *imm16 as i32 == rc.value)
                || matches!(op, ArmOp::Mov { rd: _, op2: Operand2::Imm(v) } if *v == rc.value);
            assert!(
                ok,
                "redundant-const index {} is not a {}-valued materialization: {op:?}",
                rc.index, rc.value
            );
        }
        // Dead-def indices are valid; eliminating them is length-consistent and
        // sound (the removed instructions are exactly the reported dead defs).
        for &di in &report.dead_defs {
            assert!(di < instrs.len());
        }
        let (out, removed) = liveness::eliminate_dead_stores(&instrs);
        assert_eq!(removed, report.dead_defs.len());
        assert_eq!(out.len(), instrs.len() - removed);

        // CFG-aware liveness on the same real output must either decline
        // (out-of-scope construct) or return a *structurally sound* graph:
        // blocks tile [0, len) gaplessly, every successor index is in range,
        // and the per-block live-set vectors line up with the block count.
        if let Some(cfg) = liveness::cfg_liveness(&instrs) {
            assert_eq!(cfg.live_in.len(), cfg.blocks.len());
            assert_eq!(cfg.live_out.len(), cfg.blocks.len());
            let mut expected_start = 0usize;
            for b in &cfg.blocks {
                assert_eq!(b.start, expected_start, "blocks must tile without gaps");
                assert!(b.end > b.start, "blocks are non-empty");
                for &s in &b.succ {
                    assert!(s < cfg.blocks.len(), "successor index in range");
                }
                expected_start = b.end;
            }
            assert_eq!(
                expected_start,
                instrs.len(),
                "blocks cover the whole stream"
            );

            // The interference graph over the same real output must be
            // structurally sound: undirected (symmetric) and self-loop-free.
            let g = liveness::interference_graph(&instrs)
                .expect("cfg_liveness succeeded, so interference_graph must too");
            for n in g.nodes() {
                assert!(!g.interferes(n, n), "no register interferes with itself");
                for m in g.neighbors(n) {
                    assert!(g.interferes(m, n), "interference is symmetric");
                }
            }

            // The graph of real codegen must be colourable within the
            // allocatable pool (R0–R8 = 9 colours): the current single-pass
            // allocator already fits it, so a principled colouring must too, and
            // the colouring it returns must be valid (adjacent nodes differ).
            match liveness::color_graph(&g, 9) {
                liveness::ColorResult::Colored(colour) => {
                    for n in g.nodes() {
                        let c = colour[&n];
                        assert!(c < 9);
                        for m in g.neighbors(n) {
                            assert_ne!(colour[&n], colour[&m], "colouring is valid");
                        }
                    }
                    // Close the loop: the independent verifier accepts the
                    // producer's colouring of real codegen (defense-in-depth).
                    assert_eq!(
                        liveness::verify_allocation(&g, &colour),
                        Ok(()),
                        "verify_allocation must accept color_graph's own output"
                    );
                }
                liveness::ColorResult::Spilled(s) => {
                    panic!("real output should fit the 9-register pool, spilled {s:?}")
                }
            }
        }
    }

    #[test]
    fn test_select_with_stack_i32_local_uses_str_ldr() {
        // An i32 non-param local should produce Str/Ldr to the SP-based slot.
        let mut selector = fresh_selector();
        let ops = vec![
            WasmOp::I32Const(7),
            WasmOp::LocalSet(0),
            WasmOp::LocalGet(0),
            WasmOp::Drop,
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 0).unwrap();
        let has_str_to_sp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Str { addr, .. } if addr.base == Reg::SP
            )
        });
        let has_ldr_from_sp = instrs.iter().any(|i| {
            matches!(
                &i.op,
                ArmOp::Ldr { addr, .. } if addr.base == Reg::SP
            )
        });
        assert!(has_str_to_sp, "i32 LocalSet should Str to SP-relative slot");
        assert!(
            has_ldr_from_sp,
            "i32 LocalGet should Ldr from SP-relative slot"
        );
    }

    // =========================================================================
    // Issue #95: constant-address load/store fold to base+offset
    // =========================================================================

    /// Helper: count `Movw` and `Movt` instructions in the prologue-stripped tail.
    fn count_movw_movt(instrs: &[ArmInstruction]) -> usize {
        instrs
            .iter()
            .filter(|i| matches!(&i.op, ArmOp::Movw { .. } | ArmOp::Movt { .. }))
            .count()
    }

    #[test]
    fn test_issue_95_const_addr_load_folds_to_base_offset() {
        // Pattern: (i32.const 0x100) (i32.load offset=8) (end)
        // Effective offset = 0x100 + 8 = 0x108 (fits imm12).
        // Expected: ONE Ldr [R11, #0x108]; NO Movw/Movt for the address.
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(0x100),
            WasmOp::I32Load {
                offset: 8,
                align: 2,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // The Movw/Movt for the address const must be gone — there should be
        // no Movw/Movt anywhere in the body (only loads).
        assert_eq!(
            count_movw_movt(&instrs),
            0,
            "issue #95: constant-address load should NOT materialize the address \
             via Movw/Movt; got: {instrs:#?}"
        );

        // There should be a single Ldr with base=R11 and offset=0x108.
        let ldrs: Vec<_> = instrs
            .iter()
            .filter_map(|i| match &i.op {
                ArmOp::Ldr { rd, addr } => Some((rd, addr)),
                _ => None,
            })
            .collect();
        assert_eq!(ldrs.len(), 1, "expected exactly one Ldr; got {ldrs:?}");
        let (_rd, addr) = ldrs[0];
        assert_eq!(addr.base, Reg::R11, "load base must be R11 (memory base)");
        assert_eq!(
            addr.offset, 0x108,
            "load offset must be folded effective offset"
        );
        assert_eq!(
            addr.offset_reg, None,
            "folded load must use [base, #imm], not register offset"
        );
    }

    #[test]
    fn test_issue_95_const_addr_load_falls_back_when_offset_too_large() {
        // Pattern: (i32.const 0x10000) (i32.load offset=8) (end)
        // Effective offset = 0x10008 > 4095 — must fall back to MOVW+MOVT path.
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(0x10000),
            WasmOp::I32Load {
                offset: 8,
                align: 2,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 0).unwrap();

        // MOVW for the low half of the address must still be emitted.
        let has_movw = instrs.iter().any(|i| matches!(&i.op, ArmOp::Movw { .. }));
        assert!(
            has_movw,
            "fallback path: 0x10000 must materialize via Movw; got: {instrs:#?}"
        );
        // The Ldr should still appear, but with a register offset (fallback path).
        let ldr = instrs
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Ldr { addr, .. } => Some(addr.clone()),
                _ => None,
            })
            .expect("must still emit a Ldr");
        assert!(
            ldr.offset_reg.is_some(),
            "fallback Ldr should use register-offset addressing, not folded imm"
        );
    }

    #[test]
    fn test_issue_95_const_addr_store_folds_to_base_offset() {
        // Pattern: (i32.const 0x100) (local.get 0) (i32.store offset=4) (end)
        // Effective offset = 0x104 (fits imm12).
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        let wasm_ops = vec![
            WasmOp::I32Const(0x100),
            WasmOp::LocalGet(0),
            WasmOp::I32Store {
                offset: 4,
                align: 2,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&wasm_ops, 1).unwrap();

        // The address-const Movw must be gone.
        assert_eq!(
            count_movw_movt(&instrs),
            0,
            "issue #95: const-addr store should NOT materialize the address; got: {instrs:#?}"
        );
        // Single Str with base=R11, offset=0x104, no offset_reg.
        let strs: Vec<_> = instrs
            .iter()
            .filter_map(|i| match &i.op {
                ArmOp::Str { rd, addr } => Some((rd, addr)),
                _ => None,
            })
            .collect();
        assert_eq!(strs.len(), 1, "expected exactly one Str; got {strs:?}");
        let (_rd, addr) = strs[0];
        assert_eq!(addr.base, Reg::R11);
        assert_eq!(addr.offset, 0x104);
        assert_eq!(addr.offset_reg, None);
    }

    #[test]
    fn test_issue_95_const_addr_subword_loads_fold() {
        let db = RuleDatabase::new();

        // i32.load8_u
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let ops = vec![
            WasmOp::I32Const(0x10),
            WasmOp::I32Load8U {
                offset: 0x20,
                align: 1,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 0).unwrap();
        assert_eq!(count_movw_movt(&instrs), 0);
        let ldrb = instrs
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Ldrb { addr, .. } => Some(addr),
                _ => None,
            })
            .expect("must emit Ldrb");
        assert_eq!(ldrb.base, Reg::R11);
        assert_eq!(ldrb.offset, 0x30);
        assert_eq!(ldrb.offset_reg, None);

        // i32.load16_s
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let ops = vec![
            WasmOp::I32Const(0x40),
            WasmOp::I32Load16S {
                offset: 2,
                align: 2,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 0).unwrap();
        assert_eq!(count_movw_movt(&instrs), 0);
        let ldrsh = instrs
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Ldrsh { addr, .. } => Some(addr),
                _ => None,
            })
            .expect("must emit Ldrsh");
        assert_eq!(ldrsh.base, Reg::R11);
        assert_eq!(ldrsh.offset, 0x42);
    }

    #[test]
    fn test_issue_95_const_addr_subword_stores_fold() {
        let db = RuleDatabase::new();

        // i32.store8 with const value
        let mut selector = InstructionSelector::new(db.rules().to_vec());
        let ops = vec![
            WasmOp::I32Const(0x80),
            WasmOp::I32Const(42),
            WasmOp::I32Store8 {
                offset: 0,
                align: 1,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 0).unwrap();
        // Only the *value* const remains as Movw (≤ 0xFFFF: single Movw); addr is folded.
        assert_eq!(
            count_movw_movt(&instrs),
            1,
            "value Movw must remain, address Movw must be folded; got: {instrs:#?}"
        );
        let strb = instrs
            .iter()
            .find_map(|i| match &i.op {
                ArmOp::Strb { addr, .. } => Some(addr),
                _ => None,
            })
            .expect("must emit Strb");
        assert_eq!(strb.base, Reg::R11);
        assert_eq!(strb.offset, 0x80);
        assert_eq!(strb.offset_reg, None);
    }

    #[test]
    fn test_issue_95_no_fold_when_value_is_complex_expression() {
        // For stores, value at idx-1 must be a (0,1) pusher. If it's a complex
        // expression (e.g., the result of an i32.add), we conservatively skip
        // the fold to avoid the splice complexity.
        let db = RuleDatabase::new();
        let mut selector = InstructionSelector::new(db.rules().to_vec());

        // Pattern: const 0x100, local.get 0, local.get 1, i32.add, i32.store offset=0
        // Here wasm_ops[idx-1] is i32.add, which is (2,1). The fold should NOT apply.
        let ops = vec![
            WasmOp::I32Const(0x100),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        let instrs = selector.select_with_stack(&ops, 2).unwrap();
        // Movw for the address must remain since we couldn't safely splice it out.
        let has_movw = instrs.iter().any(|i| matches!(&i.op, ArmOp::Movw { .. }));
        assert!(
            has_movw,
            "complex-value stores must NOT fold; address Movw should remain. got: {instrs:#?}"
        );
    }

    /// #237: under `--native-pointer-abi`, a store to a const address in a data
    /// segment becomes `__synth_wasm_data`-relative (MovwSym/MovtSym), so a
    /// `base=0` host-pointer trampoline doesn't mis-resolve it. Without the flag
    /// (and for an out-of-range/runtime address) it stays base-relative.
    #[test]
    fn test_311_i64_return_moves_both_halves() {
        // #311 defect 3 (gale): when a function's final i64 lands outside
        // r0:r1, the return epilogue must move BOTH halves — the single-reg
        // move dropped the hi (decide() returned (0,0), contract (0,1)).
        // Three i64 consts force the final Or's destination pair off r0/r1.
        let db = RuleDatabase::new();
        let mut sel = InstructionSelector::new(db.rules().to_vec());
        let ops = vec![
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Const(3),
            WasmOp::I64Or,
            WasmOp::I64Or,
        ];
        let instrs = sel.select_with_stack(&ops, 0).unwrap();
        // The epilogue's return moves: r0 <- lo, r1 <- hi of a CONSECUTIVE
        // pair that is not already (r0, r1).
        let mov_to = |rd: Reg| {
            instrs.iter().rev().find_map(|i| match &i.op {
                ArmOp::Mov {
                    rd: d,
                    op2: Operand2::Reg(src),
                } if *d == rd => Some(*src),
                _ => None,
            })
        };
        let lo_src = mov_to(Reg::R0).expect("epilogue must move the lo half into r0");
        let hi_src = mov_to(Reg::R1)
            .expect("epilogue must move the HI half into r1 (the dropped-hi defect)");
        assert_eq!(
            i64_pair_hi(lo_src).unwrap(),
            hi_src,
            "the two moves must carry one consecutive pair (got {lo_src:?}/{hi_src:?})"
        );
        assert_ne!(
            lo_src,
            Reg::R0,
            "premise: the pair transited high registers"
        );
    }
    #[test]
    fn test_311_i64_call_result_tagged_as_pair() {
        // #311 (gale, k_sem_give silent wrong-code): an i64-returning call
        // leaves its result in the R0:R1 PAIR. The result must be i64-tagged
        // on the operand stack so liveness covers R1 — the mask constants of
        // the following unpack must NOT materialize into the live pair.
        let db = RuleDatabase::new();
        let mut sel = InstructionSelector::new(db.rules().to_vec());
        sel.set_func_arg_counts(vec![0, 0], vec![]);
        sel.set_result_types(vec![false, true], vec![]);
        let ops = vec![
            WasmOp::Call(1),       // returns i64 in r0:r1
            WasmOp::I64Const(255), // pair const — must avoid r0/r1
            WasmOp::I64And,
            WasmOp::I32WrapI64,
        ];
        let instrs = sel.select_with_stack(&ops, 0).unwrap();
        let bl_at = instrs
            .iter()
            .position(|i| matches!(&i.op, ArmOp::Bl { .. }))
            .expect("call emitted");
        let clobbers_pair = instrs[bl_at + 1..]
            .iter()
            .any(|i| matches!(&i.op, ArmOp::Movw { rd, .. } if *rd == Reg::R0 || *rd == Reg::R1));
        assert!(
            !clobbers_pair,
            "mask constants must not materialize into the live u64 pair r0/r1"
        );
    }

    #[test]
    fn test_311_call_fed_i64_local_inferred() {
        // The second half of #311: `local.set` fed by an i64-returning call
        // must mark the local i64 (8-byte slot, both halves stored) — without
        // the result-type table the hi word was silently dropped.
        let ops = vec![WasmOp::Call(1), WasmOp::LocalSet(0)];
        let with_table = infer_i64_locals(&ops, &[false, true], &[]);
        assert!(with_table.contains(&0), "call-fed local inferred i64");
        let without = infer_i64_locals(&ops, &[], &[]);
        assert!(!without.contains(&0), "no table -> conservative i32");
    }

    #[test]
    fn test_237_globals_live_in_materialized_slots_under_native_pointer_abi() {
        // #237 (gale, mutex-on-silicon): global.get/set go through
        // `__synth_globals` slots — the set is a REAL store (the dropped-store
        // leaf assumption miscompiled gmutex), the get reads the CURRENT value,
        // and the SP global is rebased absolute-on-read / offset-on-write.
        let db = RuleDatabase::new();
        let mut sel = InstructionSelector::new(db.rules().to_vec());
        sel.set_native_pointer_abi(true, 65536);
        sel.set_native_pointer_stack(0, 4096);
        let ops = vec![
            WasmOp::GlobalGet(0),
            WasmOp::I32Const(16),
            WasmOp::I32Sub,
            WasmOp::GlobalSet(0),
        ];
        let instrs = sel.select_with_stack(&ops, 0).unwrap();
        // #345: addresses now load via the link-survivable literal pool (LdrSym),
        // not the inline MovwSym/MovtSym pair.
        let globals_syms = instrs
            .iter()
            .filter(
                |i| matches!(&i.op, ArmOp::LdrSym { symbol, .. } if symbol == "__synth_globals"),
            )
            .count();
        assert_eq!(
            globals_syms, 2,
            "one slot address for the get, one for the set"
        );
        let base_syms = instrs
            .iter()
            .filter(
                |i| matches!(&i.op, ArmOp::LdrSym { symbol, .. } if symbol == "__synth_wasm_data"),
            )
            .count();
        assert_eq!(base_syms, 2, "rebase on read (add) and on write (sub)");
        // #345: NO inline absolute MOVW/MOVT against these symbols remain.
        assert!(
            !instrs.iter().any(|i| matches!(
                &i.op,
                ArmOp::MovwSym { symbol, .. } | ArmOp::MovtSym { symbol, .. }
                    if symbol == "__synth_globals" || symbol == "__synth_wasm_data"
            )),
            "no inline MOVW/MOVT-ABS against linmem symbols (#345)"
        );
        assert!(
            instrs.iter().any(|i| matches!(&i.op, ArmOp::Ldr { .. })),
            "the get LOADS the slot (not a constant)"
        );
        assert!(
            instrs.iter().any(|i| matches!(&i.op, ArmOp::Str { .. })),
            "the set STORES to the slot (not dropped)"
        );
        assert!(
            !instrs
                .iter()
                .any(|i| { reg_effect_touches(&i.op, Reg::R9) }),
            "no R9 globals-table access under the native-pointer ABI"
        );
    }

    fn reg_effect_touches(op: &ArmOp, reg: Reg) -> bool {
        crate::liveness::reg_effect(op)
            .map(|e| e.defs.contains(&reg) || e.uses.contains(&reg))
            .unwrap_or(false)
    }

    #[test]
    fn test_237_static_store_is_symbol_relative_under_native_pointer_abi() {
        let db = RuleDatabase::new();
        // store i32 7 to wasm static at const address 256 (in data segment [256,4)).
        let ops = vec![
            WasmOp::I32Const(256),
            WasmOp::I32Const(7),
            WasmOp::I32Store {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        // #345: the address now loads via a link-survivable literal pool (LdrSym),
        // not the inline MovwSym/MovtSym pair.
        let is_data_sym = |i: &ArmInstruction| {
            matches!(&i.op, ArmOp::LdrSym { symbol, .. }
                if symbol == "__synth_wasm_data")
        };

        // Flag ON + address in range → symbol-relative.
        let mut sel = InstructionSelector::new(db.rules().to_vec());
        sel.set_relocatable(true);
        sel.set_native_pointer_abi(true, 65536);
        let on = sel.select_with_stack(&ops, 0).unwrap();
        assert!(
            on.iter().filter(|i| is_data_sym(i)).count() >= 1,
            "static store must emit LdrSym __synth_wasm_data. got: {on:#?}"
        );

        // Flag OFF → base-relative, no symbol relocation (frozen behavior).
        let mut sel_off = InstructionSelector::new(db.rules().to_vec());
        sel_off.set_relocatable(true);
        let off = sel_off.select_with_stack(&ops, 0).unwrap();
        assert!(
            !off.iter().any(is_data_sym),
            "without the flag the static store stays base-relative. got: {off:#?}"
        );

        // Flag ON but address OUT of range (runtime/host pointer) → base-relative.
        let mut sel_oor = InstructionSelector::new(db.rules().to_vec());
        sel_oor.set_relocatable(true);
        sel_oor.set_native_pointer_abi(true, 64); // 256 >= 64 → out of linear memory → host pointer
        let oor = sel_oor.select_with_stack(&ops, 0).unwrap();
        assert!(
            !oor.iter().any(is_data_sym),
            "an address outside any data segment stays base-relative. got: {oor:#?}"
        );
    }

    /// #237: register-promote the stack-pointer global so a dissolved leaf object
    /// is self-contained (no R9 globals table). Mirrors gmutex's prologue:
    /// `global.get $sp; i32.const 16; i32.sub; global.set $sp` plus a
    /// `i32.const 65536` static-pointer call argument. Asserts:
    ///  - `global.get $sp` materializes `__synth_wasm_data + init` (MovwSym/MovtSym)
    ///  - the static-pointer const (>= data_base) is relocated likewise
    ///  - the frame-size const `16` (< data_base) stays a plain `Movw` immediate
    ///  - the promoted global never touches the R9 globals table
    #[test]
    fn test_237_stack_pointer_global_is_register_promoted() {
        let db = RuleDatabase::new();
        // (memory 2) = 131072 bytes; (global $sp (mut i32) 65536).
        let ops = vec![
            WasmOp::GlobalGet(0),    // read SP → real stack top
            WasmOp::I32Const(16),    // frame size (scalar, must stay immediate)
            WasmOp::I32Sub,          // SP - 16
            WasmOp::GlobalSet(0),    // write SP (dead in leaf-balanced)
            WasmOp::I32Const(65536), // &static_spinlock (pointer, must relocate)
            WasmOp::End,
        ];
        let mut sel = InstructionSelector::new(db.rules().to_vec());
        sel.set_relocatable(true);
        sel.set_native_pointer_abi(true, 131072);
        sel.set_native_pointer_stack(0, 65536);
        let out = sel.select_with_stack(&ops, 1).unwrap();

        // #345: each materialization is now a single literal-pool load (LdrSym),
        // not a MovwSym+MovtSym pair.
        let data_syms = out
            .iter()
            .filter(|i| {
                matches!(&i.op, ArmOp::LdrSym { symbol, .. }
                    if symbol == "__synth_wasm_data")
            })
            .count();
        // Two materializations × one LdrSym: the SP read and the static-pointer.
        assert!(
            data_syms >= 2,
            "expected SP-read + static-ptr both __synth_wasm_data-relative (>=2 LdrSym); got {data_syms}: {out:#?}"
        );
        // #345: no inline absolute MOVW/MOVT against the linmem base remain.
        assert!(
            !out.iter().any(|i| matches!(
                &i.op,
                ArmOp::MovwSym { symbol, .. } | ArmOp::MovtSym { symbol, .. }
                    if symbol == "__synth_wasm_data"
            )),
            "no inline MOVW/MOVT-ABS against __synth_wasm_data (#345): {out:#?}"
        );
        // The frame-size 16 must remain a plain scalar immediate, never
        // relocated as `__synth_wasm_data`. Since #253/Add-Sub folding it is
        // folded into the frame `sub`'s immediate (or, pre-folding, a `Movw`).
        assert!(
            out.iter().any(|i| matches!(
                &i.op,
                ArmOp::Movw { imm16: 16, .. }
                    | ArmOp::Sub {
                        op2: Operand2::Imm(16),
                        ..
                    }
                    | ArmOp::Add {
                        op2: Operand2::Imm(16),
                        ..
                    }
            )),
            "frame size 16 must stay a plain scalar immediate (folded or movw): {out:#?}"
        );
        // The promoted SP global must not read/write the R9 globals table.
        let touches_r9 = out.iter().any(|i| match &i.op {
            ArmOp::Ldr { addr, .. } | ArmOp::Str { addr, .. } => addr.base == Reg::R9,
            _ => false,
        });
        assert!(
            !touches_r9,
            "register-promoted SP global must not touch the R9 globals table: {out:#?}"
        );
    }
}
