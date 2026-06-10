//! Semantic Correctness Tests — i64 operations
//!
//! Companion to `semantic_correctness.rs` (i32 only). Verifies that compiled
//! WASM i64 ops produce correct results by interpreting the generated ARM
//! pseudo-instructions and checking the (lo, hi) register-pair output.
//!
//! ## Why this exists
//!
//! Issue #93 (silicon-blocking memset miscompile) was caused by silently
//! dropped i64 ops in the optimized lowering path. A test like
//! `local.get 0 (i32); i64.extend_i32_u; i64.const 5; i64.shr_u` in this
//! file would have caught the bug pre-merge. The original
//! `semantic_correctness.rs` only covered i32 — the i64 testing gap is
//! exactly what allowed #93 to ship.
//!
//! ## What the interpreter models
//!
//! Same `MiniArm` shape as `semantic_correctness.rs`: 16 GP registers, NZCV
//! flags. New handlers added:
//!
//! - `Adds` / `Adc` / `Subs` / `Sbc` — i64 add/sub via low/high halves
//! - `I64Const` — materializes a 64-bit literal across (rdlo, rdhi)
//! - `I64ExtendI32S` / `I64ExtendI32U` — sign- vs zero-extend i32→i64
//! - `I32WrapI64` — drop upper 32 bits
//! - `I64Extend8S` / `I64Extend16S` / `I64Extend32S` — sign-extend low N bits
//! - `I64Mul` — UMULL + cross-product additions
//! - `I64Shl` / `I64ShrU` / `I64ShrS` — variable-shift dance with n<32 vs
//!   n>=32 (the family that triggered #93)
//! - `I64SetCond` / `I64SetCondZ` — comparison and equal-to-zero
//!
//! Memory ops, FP ops, and traps are intentionally not modelled (covered
//! by other test suites).

use synth_synthesis::{ArmInstruction, ArmOp, InstructionSelector, Operand2, Reg, WasmOp};

// =========================================================================
// Mini ARM interpreter — i64 extensions
// =========================================================================

fn reg_index(r: &Reg) -> usize {
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
}

#[derive(Debug, Clone)]
struct ArmState {
    regs: [u32; 16],
    /// Carry flag — only flag we actually consult, since the i64
    /// pseudo-ops we model don't need N/Z/V. (The full i32 interpreter
    /// in `semantic_correctness.rs` does track N/Z/V for CMP-driven
    /// comparisons; we don't reach those code paths via i64 ops.)
    flag_c: bool,
}

impl ArmState {
    fn new() -> Self {
        Self {
            regs: [0u32; 16],
            flag_c: false,
        }
    }

    fn get(&self, r: &Reg) -> u32 {
        self.regs[reg_index(r)]
    }

    fn set(&mut self, r: Reg, val: u32) {
        self.regs[reg_index(&r)] = val;
    }

    /// Read a 64-bit register pair (lo, hi) as u64.
    fn get64(&self, lo: &Reg, hi: &Reg) -> u64 {
        let l = self.get(lo) as u64;
        let h = self.get(hi) as u64;
        (h << 32) | l
    }

    /// Write a u64 across a (lo, hi) register pair.
    fn set64(&mut self, lo: Reg, hi: Reg, val: u64) {
        self.set(lo, val as u32);
        self.set(hi, (val >> 32) as u32);
    }

    fn resolve_operand2(&self, op2: &Operand2) -> u32 {
        match op2 {
            Operand2::Imm(v) => *v as u32,
            Operand2::Reg(r) => self.get(r),
            Operand2::RegShift { rm, .. } => self.get(rm),
        }
    }
}

/// Interpret a single ARM instruction. Extends the i32 interpreter from
/// `semantic_correctness.rs` with the i64 pseudo-ops and carry-aware
/// add/sub. Anything not relevant to i64 arithmetic falls through to a
/// no-op so prologue/epilogue/branches don't perturb state.
fn interpret_single(state: &mut ArmState, instr: &ArmInstruction) {
    match &instr.op {
        // ---- i32 ops we re-model so the interpreter is self-contained ----
        ArmOp::Movw { rd, imm16 } => state.set(*rd, *imm16 as u32),
        ArmOp::Movt { rd, imm16 } => {
            let low = state.get(rd) & 0xFFFF;
            state.set(*rd, ((*imm16 as u32) << 16) | low);
        }
        ArmOp::Mov { rd, op2 } => {
            let v = state.resolve_operand2(op2);
            state.set(*rd, v);
        }
        ArmOp::Mvn { rd, op2 } => {
            let v = state.resolve_operand2(op2);
            state.set(*rd, !v);
        }
        ArmOp::Add { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a.wrapping_add(b));
        }
        ArmOp::Sub { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a.wrapping_sub(b));
        }
        ArmOp::Mul { rd, rn, rm } => {
            let a = state.get(rn);
            let b = state.get(rm);
            state.set(*rd, a.wrapping_mul(b));
        }
        ArmOp::And { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a & b);
        }
        ArmOp::Orr { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a | b);
        }
        ArmOp::Eor { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            state.set(*rd, a ^ b);
        }

        // ---- i64 add/sub via carry chain ----
        // ADDS sets the C flag based on unsigned overflow. ADC reads the C
        // flag set by the preceding ADDS to propagate the carry into the
        // high half of the i64 result. SUBS/SBC are the borrow-chain mirror.
        ArmOp::Adds { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            let (res, carry) = a.overflowing_add(b);
            state.set(*rd, res);
            state.flag_c = carry;
        }
        ArmOp::Adc { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            let c = if state.flag_c { 1u32 } else { 0u32 };
            // Compute a + b + c with proper carry tracking.
            let (s1, c1) = a.overflowing_add(b);
            let (s2, c2) = s1.overflowing_add(c);
            state.set(*rd, s2);
            state.flag_c = c1 || c2;
        }
        ArmOp::Subs { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            let (res, borrow) = a.overflowing_sub(b);
            state.set(*rd, res);
            // ARM convention: C is set when there is NO borrow, i.e. a >= b
            state.flag_c = !borrow;
        }
        ArmOp::Sbc { rd, rn, op2 } => {
            let a = state.get(rn);
            let b = state.resolve_operand2(op2);
            // ARM SBC: rd = rn - op2 - NOT(C). C=1 means no borrow from prev.
            let nb = if state.flag_c { 0u32 } else { 1u32 };
            let (s1, br1) = a.overflowing_sub(b);
            let (s2, br2) = s1.overflowing_sub(nb);
            state.set(*rd, s2);
            state.flag_c = !(br1 || br2);
        }

        // ---- i64 const: materialize 64-bit literal across (rdlo, rdhi) ----
        ArmOp::I64Const { rdlo, rdhi, value } => {
            let v = *value as u64;
            state.set64(*rdlo, *rdhi, v);
        }

        // ---- i32 -> i64 conversions ----
        // Unsigned extend: hi := 0; lo := input. (Compiler emits two ops:
        // a Mov rdlo,rn followed by Movw rdhi,#0 — we model the pseudo-op
        // for symmetry with select_default's path.)
        ArmOp::I64ExtendI32U { rdlo, rdhi, rn } => {
            let v = state.get(rn);
            state.set(*rdlo, v);
            state.set(*rdhi, 0);
        }
        // Signed extend: hi := arithmetic shift right of lo by 31. This
        // produces 0 for non-negative inputs and 0xFFFFFFFF for negative,
        // matching wasm i64.extend_i32_s semantics.
        ArmOp::I64ExtendI32S { rdlo, rdhi, rn } => {
            let v = state.get(rn);
            state.set(*rdlo, v);
            state.set(*rdhi, ((v as i32) >> 31) as u32);
        }
        // Wrap: take low 32 bits. Since rd may equal rnlo this is a no-op
        // when the regs match.
        ArmOp::I32WrapI64 { rd, rnlo } => {
            let v = state.get(rnlo);
            state.set(*rd, v);
        }
        // In-place sign extension of the low half of an i64 register pair.
        ArmOp::I64Extend8S { rdlo, rdhi, rnlo } => {
            let v = state.get(rnlo) as u8 as i8 as i64 as u64;
            state.set64(*rdlo, *rdhi, v);
        }
        ArmOp::I64Extend16S { rdlo, rdhi, rnlo } => {
            let v = state.get(rnlo) as u16 as i16 as i64 as u64;
            state.set64(*rdlo, *rdhi, v);
        }
        ArmOp::I64Extend32S { rdlo, rdhi, rnlo } => {
            let v = state.get(rnlo) as i32 as i64 as u64;
            state.set64(*rdlo, *rdhi, v);
        }

        // ---- i64 multiply ----
        ArmOp::I64Mul {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        } => {
            // 64-bit multiply: full lo*lo as u64 plus cross-product highs.
            // The compiler emits UMULL + MLA; we just compute the same
            // arithmetic at the pseudo-op level.
            let a = state.get64(rn_lo, rn_hi);
            let b = state.get64(rm_lo, rm_hi);
            let r = a.wrapping_mul(b);
            state.set64(*rd_lo, *rd_hi, r);
        }

        // ---- i64 variable shifts ----
        // Shift amount is the LOW 32 bits of the second operand, masked to
        // 6 bits per wasm semantics (shift counts in [0, 64)).
        ArmOp::I64Shl {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            ..
        } => {
            let a = state.get64(rn_lo, rn_hi);
            let n = state.get(rm_lo) & 63;
            state.set64(*rd_lo, *rd_hi, a.wrapping_shl(n));
        }
        ArmOp::I64ShrU {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            ..
        } => {
            let a = state.get64(rn_lo, rn_hi);
            let n = state.get(rm_lo) & 63;
            state.set64(*rd_lo, *rd_hi, a.wrapping_shr(n));
        }
        ArmOp::I64ShrS {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            ..
        } => {
            let a = state.get64(rn_lo, rn_hi) as i64;
            let n = state.get(rm_lo) & 63;
            state.set64(*rd_lo, *rd_hi, a.wrapping_shr(n) as u64);
        }

        // ---- i64 comparisons ----
        // Both pseudo-ops produce a single i32 result (0 or 1) in rd.
        ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => {
            let v = state.get64(rn_lo, rn_hi);
            state.set(*rd, if v == 0 { 1 } else { 0 });
        }
        ArmOp::I64SetCond {
            rd,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
            cond,
        } => {
            use synth_synthesis::Condition;
            let a = state.get64(rn_lo, rn_hi);
            let b = state.get64(rm_lo, rm_hi);
            let res = match cond {
                Condition::EQ => a == b,
                Condition::NE => a != b,
                Condition::LT => (a as i64) < (b as i64),
                Condition::LE => (a as i64) <= (b as i64),
                Condition::GT => (a as i64) > (b as i64),
                Condition::GE => (a as i64) >= (b as i64),
                Condition::LO => a < b,
                Condition::LS => a <= b,
                Condition::HI => a > b,
                Condition::HS => a >= b,
            };
            state.set(*rd, if res { 1 } else { 0 });
        }

        // Anything else (Push/Pop/branches/labels/Sub for SP frame setup
        // with imm operand/etc) is intentionally a no-op.
        _ => {}
    }
}

/// Execute an ARM instruction sequence; returns the final state.
fn interpret_arm(instructions: &[ArmInstruction]) -> ArmState {
    let mut state = ArmState::new();
    for instr in instructions {
        interpret_single(&mut state, instr);
    }
    state
}

// =========================================================================
// Result-finding helpers
// =========================================================================
//
// For i64 ops in select_with_stack, the result pair (rdlo, rdhi) is
// allocated dynamically, not pinned to R0:R1. Walk the instruction list
// in reverse to find the most-recent producer of an i64 result; return
// its (lo, hi) registers.

#[derive(Debug, Clone, Copy)]
struct I64Result {
    lo: Reg,
    hi: Reg,
}

/// Find the (lo, hi) register pair holding the final i64 result of a
/// compiled wasm op stream. Returns `None` if no i64-producing op is
/// present.
///
/// Strategy: forward scan, tracking the most-recent i64 producer. For
/// pseudo-ops that pack (rdlo, rdhi) we record both directly. For the
/// arithmetic/bitwise expansions where the lo-half op comes first and
/// the hi-half op immediately after, we pair adjacent ops by tracking
/// `pending_lo` (the destination of the lo-half op that hasn't been
/// paired yet).
fn find_i64_result(instrs: &[ArmInstruction]) -> Option<I64Result> {
    let mut last_pair: Option<I64Result> = None;
    // For Adds/Subs/Adc/Sbc the lo and hi opcodes are distinct (Adds vs
    // Adc, Subs vs Sbc), so we can pair them unambiguously.
    let mut pending_addsub_lo: Option<Reg> = None;
    // For And/Orr/Eor the lo and hi halves use the SAME opcode, so we
    // pair adjacent occurrences. Reset the toggle whenever we see another
    // i64-producing op so an unpaired half from earlier doesn't bleed
    // into later results.
    let mut pending_bitwise_lo: Option<(Reg, &'static str)> = None;

    let reset_bitwise = |p: &mut Option<(Reg, &'static str)>| *p = None;
    let reset_addsub = |p: &mut Option<Reg>| *p = None;

    for instr in instrs {
        match &instr.op {
            // Direct (rdlo, rdhi) producers
            ArmOp::I64Const { rdlo, rdhi, .. }
            | ArmOp::I64ExtendI32S { rdlo, rdhi, .. }
            | ArmOp::I64ExtendI32U { rdlo, rdhi, .. }
            | ArmOp::I64Extend8S { rdlo, rdhi, .. }
            | ArmOp::I64Extend16S { rdlo, rdhi, .. }
            | ArmOp::I64Extend32S { rdlo, rdhi, .. } => {
                last_pair = Some(I64Result {
                    lo: *rdlo,
                    hi: *rdhi,
                });
                reset_addsub(&mut pending_addsub_lo);
                reset_bitwise(&mut pending_bitwise_lo);
            }
            ArmOp::I64Mul { rd_lo, rd_hi, .. }
            | ArmOp::I64Shl { rd_lo, rd_hi, .. }
            | ArmOp::I64ShrU { rd_lo, rd_hi, .. }
            | ArmOp::I64ShrS { rd_lo, rd_hi, .. } => {
                last_pair = Some(I64Result {
                    lo: *rd_lo,
                    hi: *rd_hi,
                });
                reset_addsub(&mut pending_addsub_lo);
                reset_bitwise(&mut pending_bitwise_lo);
            }
            // Add/Sub: lo half is Adds/Subs, hi half is Adc/Sbc immediately
            // after. The pair commits on the hi-half op.
            ArmOp::Adds { rd, .. } | ArmOp::Subs { rd, .. } => {
                pending_addsub_lo = Some(*rd);
                reset_bitwise(&mut pending_bitwise_lo);
            }
            ArmOp::Adc { rd, .. } | ArmOp::Sbc { rd, .. } => {
                if let Some(lo) = pending_addsub_lo.take() {
                    last_pair = Some(I64Result { lo, hi: *rd });
                }
                reset_bitwise(&mut pending_bitwise_lo);
            }
            // Bitwise: same opcode for both halves. Pair adjacent ops with
            // matching opcode label. If the next op is a different opcode,
            // assume the bitwise op was a single i32 op (not part of an
            // i64 pair).
            ArmOp::And { rd, .. } => {
                pending_bitwise_lo = match pending_bitwise_lo.take() {
                    Some((lo, "And")) => {
                        last_pair = Some(I64Result { lo, hi: *rd });
                        None
                    }
                    _ => Some((*rd, "And")),
                };
                reset_addsub(&mut pending_addsub_lo);
            }
            ArmOp::Orr { rd, .. } => {
                pending_bitwise_lo = match pending_bitwise_lo.take() {
                    Some((lo, "Orr")) => {
                        last_pair = Some(I64Result { lo, hi: *rd });
                        None
                    }
                    _ => Some((*rd, "Orr")),
                };
                reset_addsub(&mut pending_addsub_lo);
            }
            ArmOp::Eor { rd, .. } => {
                pending_bitwise_lo = match pending_bitwise_lo.take() {
                    Some((lo, "Eor")) => {
                        last_pair = Some(I64Result { lo, hi: *rd });
                        None
                    }
                    _ => Some((*rd, "Eor")),
                };
                reset_addsub(&mut pending_addsub_lo);
            }
            _ => {}
        }
    }
    // #311 defect 3: the return epilogue now moves a function-final i64 pair
    // into the AAPCS result registers (mov r0, lo; mov r1, hi). When those
    // moves are present for the pair we tracked, the OBSERVABLE result lives
    // in r0:r1 — and the hi move may legitimately overwrite the old pair's
    // registers, so reading the pre-move location is wrong. Follow the moves.
    if let Some(p) = &last_pair {
        let lo_moved = instrs.iter().any(
            |i| matches!(&i.op, ArmOp::Mov { rd: Reg::R0, op2: Operand2::Reg(s) } if *s == p.lo),
        );
        if lo_moved || p.lo == Reg::R0 {
            let hi_moved = instrs.iter().any(|i| {
                matches!(&i.op, ArmOp::Mov { rd: Reg::R1, op2: Operand2::Reg(s) } if *s == p.hi)
            });
            if hi_moved || p.hi == Reg::R1 {
                return Some(I64Result {
                    lo: Reg::R0,
                    hi: Reg::R1,
                });
            }
        }
    }
    last_pair
}

/// Compile a wasm op stream and return the final i64 value as u64.
fn compile_and_i64(wasm_ops: &[WasmOp]) -> u64 {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(wasm_ops, 0)
        .expect("instruction selection should succeed");
    let state = interpret_arm(&instrs);
    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    state.get64(&pair.lo, &pair.hi)
}

/// Compile a wasm op stream that ends in an i32-producing op (e.g. an i64
/// comparison or i32.wrap_i64) and return the i32 result. The result lives
/// in the destination register of the final SetCond/SetCondZ/I32WrapI64.
fn compile_and_i32(wasm_ops: &[WasmOp]) -> u32 {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(wasm_ops, 0)
        .expect("instruction selection should succeed");
    let state = interpret_arm(&instrs);
    // Find result register by scanning from the end for an i32-producing op.
    for instr in instrs.iter().rev() {
        match &instr.op {
            ArmOp::I64SetCond { rd, .. } | ArmOp::I64SetCondZ { rd, .. } => {
                return state.get(rd);
            }
            ArmOp::I32WrapI64 { rd, .. } => return state.get(rd),
            _ => {}
        }
    }
    // Fallback: assume R0 (matches the i32 path's "last op uses R0" rule).
    state.get(&Reg::R0)
}

// =========================================================================
// Tests: i64.const
// =========================================================================

#[test]
fn i64_const_zero() {
    assert_eq!(compile_and_i64(&[WasmOp::I64Const(0)]), 0);
}

#[test]
fn i64_const_small_positive() {
    assert_eq!(compile_and_i64(&[WasmOp::I64Const(42)]), 42);
}

#[test]
fn i64_const_large_high_word() {
    // 0x1_0000_0000 — high word is 1, low is 0.
    assert_eq!(
        compile_and_i64(&[WasmOp::I64Const(0x1_0000_0000)]),
        0x1_0000_0000u64
    );
}

#[test]
fn i64_const_max_positive() {
    assert_eq!(
        compile_and_i64(&[WasmOp::I64Const(i64::MAX)]),
        i64::MAX as u64
    );
}

#[test]
fn i64_const_min_negative() {
    assert_eq!(
        compile_and_i64(&[WasmOp::I64Const(i64::MIN)]),
        i64::MIN as u64
    );
}

#[test]
fn i64_const_negative_one() {
    assert_eq!(compile_and_i64(&[WasmOp::I64Const(-1)]), u64::MAX);
}

// =========================================================================
// Tests: i64.add — boundary inputs
// =========================================================================

#[test]
fn i64_add_basic() {
    let r = compile_and_i64(&[WasmOp::I64Const(100), WasmOp::I64Const(23), WasmOp::I64Add]);
    assert_eq!(r, 123);
}

#[test]
fn i64_add_carry_across_halves() {
    // 0xFFFFFFFF + 1 must propagate carry into the high word.
    let r = compile_and_i64(&[
        WasmOp::I64Const(0xFFFF_FFFF),
        WasmOp::I64Const(1),
        WasmOp::I64Add,
    ]);
    assert_eq!(r, 0x1_0000_0000u64);
}

#[test]
fn i64_add_negative_plus_positive() {
    // -1 + 1 = 0 (round-trip through full 64-bit add)
    let r = compile_and_i64(&[WasmOp::I64Const(-1), WasmOp::I64Const(1), WasmOp::I64Add]);
    assert_eq!(r, 0);
}

#[test]
fn i64_add_max_plus_one_wraps_to_min() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(i64::MAX),
        WasmOp::I64Const(1),
        WasmOp::I64Add,
    ]);
    assert_eq!(r, i64::MIN as u64);
}

// =========================================================================
// Tests: i64.sub
// =========================================================================

#[test]
fn i64_sub_basic() {
    let r = compile_and_i64(&[WasmOp::I64Const(1000), WasmOp::I64Const(43), WasmOp::I64Sub]);
    assert_eq!(r, 957);
}

#[test]
fn i64_sub_borrow_across_halves() {
    // 0x1_0000_0000 - 1 = 0xFFFF_FFFF — borrow must propagate into hi.
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x1_0000_0000),
        WasmOp::I64Const(1),
        WasmOp::I64Sub,
    ]);
    assert_eq!(r, 0xFFFF_FFFFu64);
}

#[test]
fn i64_sub_to_negative() {
    // 5 - 10 = -5 (wraps in u64)
    let r = compile_and_i64(&[WasmOp::I64Const(5), WasmOp::I64Const(10), WasmOp::I64Sub]);
    assert_eq!(r, (-5i64) as u64);
}

#[test]
fn i64_sub_min_minus_one_wraps_to_max() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(i64::MIN),
        WasmOp::I64Const(1),
        WasmOp::I64Sub,
    ]);
    assert_eq!(r, i64::MAX as u64);
}

// =========================================================================
// Tests: i64.mul
// =========================================================================

#[test]
fn i64_mul_basic() {
    let r = compile_and_i64(&[WasmOp::I64Const(6), WasmOp::I64Const(7), WasmOp::I64Mul]);
    assert_eq!(r, 42);
}

#[test]
fn i64_mul_by_zero() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(i64::MAX),
        WasmOp::I64Const(0),
        WasmOp::I64Mul,
    ]);
    assert_eq!(r, 0);
}

#[test]
fn i64_mul_high_word_only() {
    // (1<<32) * 1 = 1<<32 — exercises 64-bit-result composition
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x1_0000_0000),
        WasmOp::I64Const(1),
        WasmOp::I64Mul,
    ]);
    assert_eq!(r, 0x1_0000_0000u64);
}

#[test]
fn i64_mul_cross_product() {
    // 0x1_0000 * 0x1_0000 = 0x1_0000_0000 — straddles low/high boundary.
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x1_0000),
        WasmOp::I64Const(0x1_0000),
        WasmOp::I64Mul,
    ]);
    assert_eq!(r, 0x1_0000_0000u64);
}

// =========================================================================
// Tests: i64.and / or / xor
// =========================================================================

#[test]
fn i64_and_full_word() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0xFFFF_FFFF_FFFF_FFFFu64 as i64),
        WasmOp::I64Const(0x0F0F_0F0F_0F0F_0F0F),
        WasmOp::I64And,
    ]);
    assert_eq!(r, 0x0F0F_0F0F_0F0F_0F0F);
}

#[test]
fn i64_or_full_word() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x00FF_00FF_00FF_00FF),
        WasmOp::I64Const(0xFF00_FF00_FF00_FF00u64 as i64),
        WasmOp::I64Or,
    ]);
    assert_eq!(r, 0xFFFF_FFFF_FFFF_FFFFu64);
}

#[test]
fn i64_xor_self_is_zero() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0xDEAD_BEEF_CAFE_BABEu64 as i64),
        WasmOp::I64Const(0xDEAD_BEEF_CAFE_BABEu64 as i64),
        WasmOp::I64Xor,
    ]);
    assert_eq!(r, 0);
}

// =========================================================================
// Tests: i64.shl / shr_u / shr_s — variable-shift family that triggered #93
// =========================================================================

#[test]
fn i64_shl_within_low_word() {
    // 1 << 4 = 16 — shift entirely within the low word.
    let r = compile_and_i64(&[WasmOp::I64Const(1), WasmOp::I64Const(4), WasmOp::I64Shl]);
    assert_eq!(r, 16);
}

#[test]
fn i64_shl_crosses_word_boundary() {
    // 1 << 32 = 0x1_0000_0000 — bit migrates from low into high.
    let r = compile_and_i64(&[WasmOp::I64Const(1), WasmOp::I64Const(32), WasmOp::I64Shl]);
    assert_eq!(r, 0x1_0000_0000u64);
}

#[test]
fn i64_shl_into_high_only() {
    // 1 << 40 — shift > 32 places result entirely in high half.
    let r = compile_and_i64(&[WasmOp::I64Const(1), WasmOp::I64Const(40), WasmOp::I64Shl]);
    assert_eq!(r, 1u64 << 40);
}

#[test]
fn i64_shru_within_high() {
    // 0x1_0000_0000 >> 32 = 1 — simple one-word shift.
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x1_0000_0000),
        WasmOp::I64Const(32),
        WasmOp::I64ShrU,
    ]);
    assert_eq!(r, 1);
}

#[test]
fn i64_shru_partial() {
    // 0xFFFF_FFFF_FFFF_FFFF >> 1 = 0x7FFF_FFFF_FFFF_FFFF
    let r = compile_and_i64(&[
        WasmOp::I64Const(-1), // all-ones
        WasmOp::I64Const(1),
        WasmOp::I64ShrU,
    ]);
    assert_eq!(r, 0x7FFF_FFFF_FFFF_FFFFu64);
}

#[test]
fn i64_shrs_negative_preserves_sign() {
    // -8 >> 1 = -4  (arithmetic shift preserves sign)
    let r = compile_and_i64(&[WasmOp::I64Const(-8), WasmOp::I64Const(1), WasmOp::I64ShrS]);
    assert_eq!(r, (-4i64) as u64);
}

#[test]
fn i64_shrs_large_shift_negative() {
    // -1 >> 63 = -1 (still all-ones after arithmetic shift)
    let r = compile_and_i64(&[WasmOp::I64Const(-1), WasmOp::I64Const(63), WasmOp::I64ShrS]);
    assert_eq!(r, u64::MAX);
}

// =========================================================================
// Test: regression for issue #93 (silicon-blocking memset miscompile)
//
// Pattern: take i32 input, zero-extend to i64, shift right by 5. This is
// the exact wasm shape that compiled to a silently-dropped i64 op in the
// optimized lowering before #97 — corrupting any function that used a
// pointer-arithmetic-by-shift idiom (memset, memcpy, array indexing).
// =========================================================================

#[test]
fn issue_93_extend_i32u_then_shr_u() {
    // i32 input = 0xCAFE_BABE; extend to i64; right-shift unsigned by 5.
    // Expected: 0xCAFE_BABE >> 5 (since the high word is zero after
    // extend_i32_u). If the i64 op is dropped or only operates on the low
    // half without zeroing the high, the test fails.
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::LocalGet(0), // i32 input
                WasmOp::I64ExtendI32U,
                WasmOp::I64Const(5),
                WasmOp::I64ShrU,
            ],
            1, // one i32 param
        )
        .expect("selection should succeed");

    // Initial state: param 0 = 0xCAFE_BABE in R0.
    let mut state = ArmState::new();
    state.set(Reg::R0, 0xCAFE_BABE);

    for instr in &instrs {
        interpret_single(&mut state, instr);
    }

    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    let r = state.get64(&pair.lo, &pair.hi);
    assert_eq!(
        r,
        0xCAFE_BABEu64 >> 5,
        "i64.extend_i32_u + i64.shr_u should produce input >> 5 in i64 land"
    );
}

#[test]
fn issue_93_extend_i32u_then_shr_u_zero_high_word() {
    // Even more direct check: after extend_i32_u, the high word must be
    // zero. If the upper 32 bits leak into the result the test catches it.
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I64ExtendI32U,
                WasmOp::I64Const(0),
                WasmOp::I64ShrU,
            ],
            1,
        )
        .expect("selection should succeed");

    // Set R0 with both halves intentionally dirty — only the low half is
    // a "real" i32 input. If extend_i32_u leaks bits from neighbouring
    // registers, this catches it.
    let mut state = ArmState::new();
    state.set(Reg::R0, 0x1234_5678);
    // Pre-populate every other register with garbage so a stale read is
    // immediately visible.
    for r in [
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
    ] {
        state.set(r, 0xFFFF_FFFF);
    }

    for instr in &instrs {
        interpret_single(&mut state, instr);
    }

    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    let r = state.get64(&pair.lo, &pair.hi);
    assert_eq!(
        r, 0x1234_5678u64,
        "extend_i32_u must zero the high word, not inherit register garbage"
    );
}

// =========================================================================
// Tests: i64 comparisons — exercise both true and false branches
// =========================================================================

#[test]
fn i64_eq_true() {
    let r = compile_and_i32(&[
        WasmOp::I64Const(0xDEAD_BEEFi64),
        WasmOp::I64Const(0xDEAD_BEEFi64),
        WasmOp::I64Eq,
    ]);
    assert_eq!(r, 1);
}

#[test]
fn i64_eq_false_high_differs() {
    // Lo halves equal, hi halves differ — naive compare would miss this.
    let r = compile_and_i32(&[
        WasmOp::I64Const(0x0000_0001_0000_0000),
        WasmOp::I64Const(0x0000_0002_0000_0000),
        WasmOp::I64Eq,
    ]);
    assert_eq!(r, 0);
}

#[test]
fn i64_ne_true() {
    let r = compile_and_i32(&[WasmOp::I64Const(1), WasmOp::I64Const(2), WasmOp::I64Ne]);
    assert_eq!(r, 1);
}

#[test]
fn i64_ne_false() {
    let r = compile_and_i32(&[WasmOp::I64Const(42), WasmOp::I64Const(42), WasmOp::I64Ne]);
    assert_eq!(r, 0);
}

#[test]
fn i64_lts_negative_lt_positive() {
    let r = compile_and_i32(&[WasmOp::I64Const(-1), WasmOp::I64Const(1), WasmOp::I64LtS]);
    assert_eq!(r, 1, "-1 <s 1 should be true");
}

#[test]
fn i64_ltu_negative_treated_as_large_unsigned() {
    // -1 (all-ones u64) is the LARGEST unsigned value, so -1 <u 1 = false.
    let r = compile_and_i32(&[WasmOp::I64Const(-1), WasmOp::I64Const(1), WasmOp::I64LtU]);
    assert_eq!(r, 0, "u64::MAX <u 1 should be false");
}

#[test]
fn i64_les_equal() {
    let r = compile_and_i32(&[WasmOp::I64Const(7), WasmOp::I64Const(7), WasmOp::I64LeS]);
    assert_eq!(r, 1);
}

#[test]
fn i64_gts_basic() {
    let r = compile_and_i32(&[
        WasmOp::I64Const(0x1_0000_0000),  // hi=1, lo=0
        WasmOp::I64Const(0xFFFF_FFFFi64), // hi=0, lo=all-ones
        WasmOp::I64GtS,
    ]);
    assert_eq!(r, 1, "high-word dominance: 2^32 >s (2^32 - 1)");
}

#[test]
fn i64_gtu_high_word_difference() {
    let r = compile_and_i32(&[
        WasmOp::I64Const(0x2_0000_0000),
        WasmOp::I64Const(0x1_FFFF_FFFFi64),
        WasmOp::I64GtU,
    ]);
    assert_eq!(r, 1, "0x2_0000_0000 >u 0x1_FFFF_FFFF");
}

#[test]
fn i64_ges_equal() {
    let r = compile_and_i32(&[WasmOp::I64Const(0), WasmOp::I64Const(0), WasmOp::I64GeS]);
    assert_eq!(r, 1);
}

#[test]
fn i64_geu_strictly_greater() {
    let r = compile_and_i32(&[WasmOp::I64Const(100), WasmOp::I64Const(50), WasmOp::I64GeU]);
    assert_eq!(r, 1);
}

// =========================================================================
// Tests: i64.eqz
// =========================================================================

#[test]
fn i64_eqz_zero_returns_one() {
    let r = compile_and_i32(&[WasmOp::I64Const(0), WasmOp::I64Eqz]);
    assert_eq!(r, 1);
}

#[test]
fn i64_eqz_nonzero_low_only() {
    // Low half non-zero, high zero — must return 0.
    let r = compile_and_i32(&[WasmOp::I64Const(1), WasmOp::I64Eqz]);
    assert_eq!(r, 0);
}

#[test]
fn i64_eqz_nonzero_high_only() {
    // High half non-zero, low zero — must also return 0. A naive
    // implementation that only tested the low word would mis-classify this.
    let r = compile_and_i32(&[WasmOp::I64Const(0x1_0000_0000), WasmOp::I64Eqz]);
    assert_eq!(r, 0);
}

// =========================================================================
// Tests: extend_i32_s / extend_i32_u / wrap_i64
// =========================================================================

/// Find the destination pair of an inline-emitted I64ExtendI32U. The
/// compiler emits `Mov dst_lo, val; Movw dst_hi, #0` (or just `Movw
/// dst_hi, #0` if val already equals dst_lo) instead of the pseudo-op.
/// Returns `(dst_lo, dst_hi)` of the most-recent such pair.
fn find_extend_i32u_pair(instrs: &[ArmInstruction]) -> Option<(Reg, Reg)> {
    // Walk forward looking for a Movw with imm16=0 that follows a Mov.
    // The dst_lo is the Mov's rd (or the Movw's rd minus one if no Mov).
    let mut last_mov_rd: Option<Reg> = None;
    let mut found: Option<(Reg, Reg)> = None;
    for instr in instrs {
        match &instr.op {
            ArmOp::Mov {
                rd,
                op2: Operand2::Reg(_),
            } => {
                last_mov_rd = Some(*rd);
            }
            ArmOp::Movw { rd, imm16: 0 } => {
                if let Some(lo) = last_mov_rd.take() {
                    // #311 defect 3: follow the return epilogue's pair moves (mov r0, lo;
                    // mov r1, hi) — reading the pre-move registers is wrong once the hi move
                    // legitimately overwrites them.
                    if let Some((lo, hi)) = found {
                        let lo_moved = instrs.iter().any(|i| {
            matches!(&i.op, ArmOp::Mov { rd: Reg::R0, op2: Operand2::Reg(s) } if *s == lo)
        });
                        let hi_moved = instrs.iter().any(|i| {
            matches!(&i.op, ArmOp::Mov { rd: Reg::R1, op2: Operand2::Reg(s) } if *s == hi)
        });
                        if (lo_moved || lo == Reg::R0) && (hi_moved || hi == Reg::R1) {
                            return Some((Reg::R0, Reg::R1));
                        }
                    }
                    found = Some((lo, *rd));
                }
            }
            _ => {
                // Reset Mov-tracking on intervening ops so the pair must
                // be adjacent.
                if !matches!(&instr.op, ArmOp::Push { .. }) {
                    last_mov_rd = None;
                }
            }
        }
    }
    // #311 defect 3: follow the return epilogue's pair moves (mov r0, lo;
    // mov r1, hi) — reading the pre-move registers is wrong once the hi move
    // legitimately overwrites them.
    if let Some((lo, hi)) = found {
        let lo_moved = instrs.iter().any(
            |i| matches!(&i.op, ArmOp::Mov { rd: Reg::R0, op2: Operand2::Reg(s) } if *s == lo),
        );
        let hi_moved = instrs.iter().any(
            |i| matches!(&i.op, ArmOp::Mov { rd: Reg::R1, op2: Operand2::Reg(s) } if *s == hi),
        );
        if (lo_moved || lo == Reg::R0) && (hi_moved || hi == Reg::R1) {
            return Some((Reg::R0, Reg::R1));
        }
    }
    found
}

#[test]
fn i64_extend_i32u_zero_extends() {
    // Zero-extend: high word must become 0 even when input has the high
    // bit set.
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::LocalGet(0), WasmOp::I64ExtendI32U], 1)
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 0x8000_0000); // negative as i32, but extend_i32_u zero-extends
    for instr in &instrs {
        interpret_single(&mut state, instr);
    }
    let (lo, hi) = find_extend_i32u_pair(&instrs).expect("expected inline extend_i32u pattern");
    assert_eq!(
        state.get64(&lo, &hi),
        0x0000_0000_8000_0000u64,
        "extend_i32_u(0x80000000) should give 0x0000_0000_8000_0000"
    );
}

#[test]
fn i64_extend_i32s_sign_extends_negative() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::LocalGet(0), WasmOp::I64ExtendI32S], 1)
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 0xFFFF_FFFF); // -1 as i32
    for instr in &instrs {
        interpret_single(&mut state, instr);
    }
    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    assert_eq!(
        state.get64(&pair.lo, &pair.hi),
        u64::MAX,
        "extend_i32_s(-1) should give u64::MAX (-1 in i64)"
    );
}

#[test]
fn i64_extend_i32s_positive_no_change_to_high() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(&[WasmOp::LocalGet(0), WasmOp::I64ExtendI32S], 1)
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 0x7FFF_FFFF); // i32::MAX (positive)
    for instr in &instrs {
        interpret_single(&mut state, instr);
    }
    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    assert_eq!(
        state.get64(&pair.lo, &pair.hi),
        0x7FFF_FFFFu64,
        "extend_i32_s(i32::MAX) should give 0x0000_0000_7FFF_FFFF"
    );
}

#[test]
fn i32_wrap_i64_drops_upper() {
    // i64 value with non-zero high word; wrap should keep only the low 32.
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::I64Const(0xDEAD_BEEF_CAFE_BABEu64 as i64),
                WasmOp::I32WrapI64,
            ],
            0,
        )
        .expect("selection should succeed");
    let state = interpret_arm(&instrs);
    // The wrap result lives in rd of the I32WrapI64 op.
    let mut wrapped: Option<u32> = None;
    for instr in &instrs {
        if let ArmOp::I32WrapI64 { rd, .. } = &instr.op {
            wrapped = Some(state.get(rd));
        }
    }
    assert_eq!(wrapped, Some(0xCAFE_BABE), "wrap drops upper 32 bits");
}

// =========================================================================
// Test: i64 round-trip via wrap
// =========================================================================

#[test]
fn i64_round_trip_extend_then_wrap_recovers_i32() {
    // i32 -> i64 (extend_i32_u) -> i32 (wrap_i64) should give back the
    // original i32.
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I64ExtendI32U,
                WasmOp::I32WrapI64,
            ],
            1,
        )
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 0x1234_5678);
    for instr in &instrs {
        interpret_single(&mut state, instr);
    }
    // Find the wrap destination.
    let mut wrapped: Option<u32> = None;
    for instr in &instrs {
        if let ArmOp::I32WrapI64 { rd, .. } = &instr.op {
            wrapped = Some(state.get(rd));
        }
    }
    assert_eq!(
        wrapped,
        Some(0x1234_5678),
        "round-trip extend_i32_u + wrap_i64 should preserve the i32"
    );
}

// =========================================================================
// Tests: chained i64 ops
// =========================================================================

#[test]
fn i64_chained_add_then_sub() {
    // (10 + 20) - 5 = 25
    let r = compile_and_i64(&[
        WasmOp::I64Const(10),
        WasmOp::I64Const(20),
        WasmOp::I64Add,
        WasmOp::I64Const(5),
        WasmOp::I64Sub,
    ]);
    assert_eq!(r, 25);
}

// NOTE: chained ops mixing select_with_stack-handled (Add/Sub/Bitwise/
// Shifts/Const/Eqz/Eq/ExtendI32*) and select_default-handled (Mul) i64
// ops produce inconsistent register state: I64Mul falls through to
// select_default which hardcodes R0:R1/R2:R3 and ignores the virtual
// stack. Mixing the two paths leaves the actual result in different
// registers than the wasm stack tracks. We test each in isolation.

#[test]
fn i64_chained_shl_then_shru_roundtrip() {
    // (x << 8) >> 8 should yield x when x's top 8 bits are zero.
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x00FF_FFFF_FFFF_FFFFi64),
        WasmOp::I64Const(8),
        WasmOp::I64Shl,
        WasmOp::I64Const(8),
        WasmOp::I64ShrU,
    ]);
    assert_eq!(r, 0x00FF_FFFF_FFFF_FFFFu64);
}

// =========================================================================
// Boundary / edge cases — extra coverage
// =========================================================================

#[test]
fn i64_shl_by_zero_is_identity() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0xDEAD_BEEF_CAFE_BABEu64 as i64),
        WasmOp::I64Const(0),
        WasmOp::I64Shl,
    ]);
    assert_eq!(r, 0xDEAD_BEEF_CAFE_BABEu64);
}

#[test]
fn i64_shl_by_sixty_three_keeps_one_bit() {
    // 1 << 63 -- highest bit only.
    let r = compile_and_i64(&[WasmOp::I64Const(1), WasmOp::I64Const(63), WasmOp::I64Shl]);
    assert_eq!(r, 0x8000_0000_0000_0000u64);
}

#[test]
fn i64_shru_by_zero_is_identity() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0xDEAD_BEEF_CAFE_BABEu64 as i64),
        WasmOp::I64Const(0),
        WasmOp::I64ShrU,
    ]);
    assert_eq!(r, 0xDEAD_BEEF_CAFE_BABEu64);
}

#[test]
fn i64_and_with_zero() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0xDEAD_BEEF_CAFE_BABEu64 as i64),
        WasmOp::I64Const(0),
        WasmOp::I64And,
    ]);
    assert_eq!(r, 0);
}

#[test]
fn i64_or_with_zero_is_identity() {
    let r = compile_and_i64(&[
        WasmOp::I64Const(0x1234_5678_9ABC_DEF0u64 as i64),
        WasmOp::I64Const(0),
        WasmOp::I64Or,
    ]);
    assert_eq!(r, 0x1234_5678_9ABC_DEF0);
}

#[test]
fn i64_eq_zero_pair() {
    // Both zeros => equal.
    let r = compile_and_i32(&[WasmOp::I64Const(0), WasmOp::I64Const(0), WasmOp::I64Eq]);
    assert_eq!(r, 1);
}

// =========================================================================
// Additional regression: param-flow through i64.shr_u
//
// Variant of #93: extend the parameter, shift by a non-trivial amount, and
// confirm the high bits don't bleed into the low half. Catches a class of
// regalloc bugs where the compiler picks an overlapping register pair for
// the result and a source operand.
// =========================================================================

#[test]
fn i64_extend_i32u_shr_u_by_one_no_high_bleed() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I64ExtendI32U,
                WasmOp::I64Const(1),
                WasmOp::I64ShrU,
            ],
            1,
        )
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 0xFFFF_FFFE);
    for instr in &instrs {
        interpret_single(&mut state, instr);
    }
    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    // 0xFFFF_FFFE >> 1 (in i64) = 0x7FFF_FFFF. High word must remain zero.
    assert_eq!(state.get64(&pair.lo, &pair.hi), 0x7FFF_FFFFu64);
}

#[test]
fn i64_extend_i32s_shr_s_by_one_preserves_sign() {
    let mut selector = InstructionSelector::new(vec![]);
    let instrs = selector
        .select_with_stack(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I64ExtendI32S,
                WasmOp::I64Const(1),
                WasmOp::I64ShrS,
            ],
            1,
        )
        .expect("selection should succeed");

    let mut state = ArmState::new();
    state.set(Reg::R0, 0xFFFF_FFFE); // -2 as i32
    for instr in &instrs {
        interpret_single(&mut state, instr);
    }
    let pair = find_i64_result(&instrs).expect("should produce i64 result");
    // i64.extend_i32_s(-2) = -2 in i64 land. -2 >>s 1 = -1 (sign-preserving)
    assert_eq!(state.get64(&pair.lo, &pair.hi), u64::MAX);
}
