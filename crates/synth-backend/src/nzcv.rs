//! RQ-91-M0FLAGS (#1301): the NZCV-liveness verifier, over EMITTED BYTES.
//!
//! THE HAZARD. A flag-preserving `ArmOp` (`Mov`, `Add`, `And`, …) can be
//! encoded as a 16-bit Thumb form that SETS flags outside an IT block: on
//! ARMv7-M today (`ArmOp::Mov rd, #imm8` is `MOVS`, `ArmOp::Add` with low
//! registers is `ADDS`), and on ARMv6-M for every data-processing op, because
//! ARMv6-M has no other encoding. The Rocq model's `MOV`/`ADD`/`AND` leave
//! NZCV alone, so such bytes are only correct while the flags they clobber are
//! DEAD. #709 was this exact bug inside one op (`MOVS rd, #0` between
//! `VMRS APSR_nzcv` and the `IT` that read it: every f32 compare returned 0).
//!
//! WHAT IS CHECKED. The function's encoded bytes are decoded back into Thumb
//! instructions — the flag reads and writes come from the BYTES, never from
//! the `ArmOp` — and a backwards per-flag liveness fixpoint is run over the
//! decoded control-flow graph. Bytes outside every segment (literal-pool
//! words) are data and are never decoded; the branch carrying execution over
//! a mid-stream island is its own segment. Each instruction belongs to the
//! segment of the `ArmOp` that emitted it, and that op's [`FlagContract`]
//! says what its model claims about the flags:
//!
//! * [`FlagContract::Preserves`] (the default for every op not listed in
//!   [`op_flag_contract`]): the model leaves NZCV alone.
//!   - R1: an INCIDENTAL flag write (any write other than a compare-class
//!     `CMP`/`CMN`/`TST`/`TEQ`/`VMRS APSR_nzcv`/`MSR APSR`; calls and
//!     undecodable instructions always count) must write only DEAD flags,
//!     checked per instruction — this is what catches #709's intra-op shape.
//!   - R2: no flag ANY of the op's instructions may write can be live where
//!     control leaves the op — the op as a whole preserves what it claims to.
//! * [`FlagContract::Scratch`]: the op's expansion uses the flags internally
//!   by design (an `ADDS`→`ADC` carry chain, a `SUBS.W`/`BPL` split) but the
//!   model says nothing leaves through them: R2 only. STATED LIMIT: R1 is off
//!   inside a Scratch op, so a #709-shaped clobber INSIDE one of these
//!   expansions (e.g. a `MOVS` between the `SBCS` and the `IT` of an i64
//!   compare) is not seen by this check; the i64 execution differentials are
//!   what cover those expansions.
//! * [`FlagContract::Writes`]`(declared)`: the model DEFINES the `declared`
//!   flags after the op (`Cmp`, `Cmn`, `Adds`, `Subs`: all four). Any OTHER
//!   flag its bytes write, and every write by a call or an undecodable
//!   instruction, is checked like R1. The nine explicit flag-setting variants
//!   (`Movs` … `Muls`) declare NOTHING: no selector marks one as the intended
//!   producer for a consumer yet, so every flag they write must be dead. A
//!   lowering that wants to consume one must declare it here — the naive
//!   `cmp; movs; bne; movs` SetCond rewrite is refused either way.
//!
//! CONSERVATIVE BY CONSTRUCTION. Every decode group ends in an `unknown`
//! arm unless the encoding is positively recognised; an unknown instruction
//! reads every flag, may write every flag (kills none), and leaves every flag
//! live after it. An indirect jump, a branch to a non-instruction offset, or
//! falling off the end / into a data gap leaves every flag live; only a
//! return (`BX LR`, `MOV PC, LR`, `POP {…, PC}`, `LDM SP!` with PC) and a
//! trap (`UDF`, `BKPT`) end liveness, and only when unconditional — inside an
//! IT block a return falls through. A branch landing INSIDE an IT block is
//! refused outright: the member would execute unconditionally, with the
//! flag-setting meaning of its 16-bit bytes. What this check does NOT show:
//! that the flags a `Writes`/`Scratch` op leaves or consumes have the right
//! VALUES (an execution or proof question), and anything about A32 code.

use synth_synthesis::rules::ArmOp;

/// Negative flag.
pub const N: u8 = 0b1000;
/// Zero flag.
pub const Z: u8 = 0b0100;
/// Carry flag.
pub const C: u8 = 0b0010;
/// Overflow flag.
pub const V: u8 = 0b0001;
/// All four.
pub const NZCV: u8 = 0b1111;

/// What an op's MODEL says about the flags. See the module doc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlagContract {
    /// The model leaves NZCV unchanged (R1 + R2).
    Preserves,
    /// The expansion uses flags internally; none escape the op (R2 only).
    Scratch,
    /// The model defines these flags after the op; every other flag the
    /// op's bytes write is checked like R1.
    Writes(u8),
}

/// The [`FlagContract`] of an op. `Preserves` — the most-checked contract —
/// is the default, so an op missing from this list can only be rejected more
/// often, never checked less.
pub fn op_flag_contract(op: &ArmOp) -> FlagContract {
    use ArmOp::*;
    match op {
        // The model DEFINES all four flags: compares and the i64
        // carry/borrow links.
        Cmp { .. } | Cmn { .. } | Adds { .. } | Subs { .. } => FlagContract::Writes(NZCV),
        // RQ-91-M0FLAGS: the explicit flag-setting variants. Their model
        // writes flags, but none is a declared producer yet: every flag they
        // write must be dead (see the module doc).
        Movs { .. }
        | Mvns { .. }
        | Ands { .. }
        | Orrs { .. }
        | Eors { .. }
        | Lsls { .. }
        | Lsrs { .. }
        | Asrs { .. }
        | Muls { .. } => FlagContract::Writes(0),
        // The model is silent about flags, and the ENCODER EXPANSION chains
        // them internally by design: `ADDS`/`SUBS` -> `ADC`/`SBC` carries,
        // `SUBS.W ip, rm, #32; BPL` shift-amount splits, `ORRS ip, lo, hi;
        // BEQ` zero-divisor guards, `CMP lo; SBCS hi` compares. A 16-bit/S=1
        // write cannot be told from a deliberate one by its bytes, so these
        // ops are checked by R2 only. MEASURED: every op here produced R1
        // hits on a v7-M corpus run (all intra-op chains, none crossing an op
        // boundary), except `I64Add`, kept for its `ADDS`/`ADC` expansion
        // although NO selector constructs it today. None of them is ARMv6-M:
        // their expansions are refused by the v6-M byte check.
        I64Add { .. }
        | I64Sub { .. }
        | I64Shl { .. }
        | I64ShrS { .. }
        | I64ShrU { .. }
        | I64Rotl { .. }
        | I64Rotr { .. }
        | I64DivS { .. }
        | I64DivU { .. }
        | I64RemS { .. }
        | I64RemU { .. }
        | I64SetCond { .. } => FlagContract::Scratch,
        _ => FlagContract::Preserves,
    }
}

/// The bytes one `ArmOp` emitted: `code[start .. start + len]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Segment {
    /// Offset in the function's code.
    pub start: usize,
    /// Byte length (0 for a label).
    pub len: usize,
    /// The op's flag contract.
    pub contract: FlagContract,
}

/// A rejected stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NzcvViolation {
    /// Offset of the offending instruction (R1/W), of the op's exit (R2), or
    /// of the branch (IT).
    pub at: usize,
    /// The instruction's halfwords, hex.
    pub bytes: String,
    /// Flags clobbered while live.
    pub flags: u8,
    /// Offset of an instruction that reads one of those flags, if one is
    /// reachable; `None` when liveness comes from an unknown successor.
    pub reader: Option<usize>,
    /// Which rule: "R1" (incidental write of a live flag), "R2" (a
    /// flag-preserving op clobbers a flag live at its exit), "W" (an op
    /// writes a flag it does not declare while it is live), or "IT" (a
    /// branch into the middle of an IT block).
    pub rule: &'static str,
}

/// Render a flag mask as `NZCV` letters.
pub fn flag_names(m: u8) -> String {
    [(N, 'N'), (Z, 'Z'), (C, 'C'), (V, 'V')]
        .iter()
        .filter(|(b, _)| m & b != 0)
        .map(|(_, c)| *c)
        .collect()
}

impl std::fmt::Display for NzcvViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.rule == "IT" {
            return write!(
                f,
                "NZCV: the branch at +0x{:x} ({}) lands inside an IT block, \
                 where the member would execute unconditionally with its \
                 flag-setting meaning (IT)",
                self.at, self.bytes
            );
        }
        let what = match self.rule {
            "R1" => "a flag-preserving op's instruction writes",
            "R2" => "a flag-preserving op clobbers",
            _ => "an op writes undeclared",
        };
        write!(
            f,
            "NZCV live across a clobber ({}): at +0x{:x} ({}) {} {} while {} live",
            self.rule,
            self.at,
            self.bytes,
            what,
            flag_names(self.flags),
            if self.flags.count_ones() == 1 {
                "it is"
            } else {
                "they are"
            }
        )?;
        match self.reader {
            Some(r) => write!(f, " (read at +0x{r:x})"),
            None => write!(
                f,
                " (no reader decoded: liveness comes from an indirect, unknown or \
                 out-of-stream successor, which is treated as reading every flag)"
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Flow {
    /// Falls through.
    Next,
    /// Unconditional direct branch.
    Jump(i64),
    /// Conditional direct branch (or CBZ/CBNZ): target and fall-through.
    Cond(i64),
    /// Function return: no flag is live after it (AAPCS).
    Return,
    /// Trap: execution does not continue.
    Stop,
    /// Indirect / unresolvable: every flag is live after it.
    Unknown,
}

#[derive(Debug, Clone)]
struct Insn {
    off: usize,
    len: usize,
    seg: usize,
    hw: (u16, Option<u16>),
    reads: u8,
    may_write: u8,
    must_write: u8,
    /// A flag write that is not a compare-class producer.
    incidental: bool,
    /// A call or an undecodable instruction: its writes are never a
    /// declared result.
    opaque: bool,
    flow: Flow,
}

fn cond_reads(cond: u16) -> u8 {
    match cond & 0xF {
        0 | 1 => Z,
        2 | 3 => C,
        4 | 5 => N,
        6 | 7 => V,
        8 | 9 => C | Z,
        10 | 11 => N | V,
        12 | 13 => N | Z | V,
        _ => 0,
    }
}

fn sext(v: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    ((v as i64) << shift) >> shift
}

/// Flag effect of a valid data-processing opcode (the Thumb-2 `op` field
/// shared by the modified-immediate and shifted-register groups):
/// `(reads, must_write, may_write, producer)`. `c_logical`: whether a
/// logical op may write C (a rotated immediate or a nonzero shift).
fn dp_effect(op: u16, rd: u16, s: bool, c_logical: bool) -> (u8, u8, u8, bool) {
    let cm = if c_logical { C } else { 0 };
    let (reads, must, may, producer) = match op {
        0 | 4 if rd == 15 && s => (0, N | Z, N | Z | cm, true), // TST / TEQ
        0..=4 => (0, N | Z, N | Z | cm, false),
        8 | 13 if rd == 15 && s => (0, NZCV, NZCV, true), // CMN / CMP
        8 | 13 | 14 => (0, NZCV, NZCV, false),            // ADD / SUB / RSB
        10 | 11 => (C, NZCV, NZCV, false),                // ADC / SBC
        _ => (0, 0, 0, false),                            // PKH
    };
    if s {
        (reads, must, may, producer)
    } else {
        (reads, 0, 0, false)
    }
}

/// Mark `i` as an instruction this decoder does not positively recognise.
fn unknown(i: &mut Insn) {
    i.reads = NZCV;
    i.may_write = NZCV;
    i.must_write = 0;
    i.incidental = true;
    i.opaque = true;
    i.flow = Flow::Unknown;
}

/// Record a flag write.
fn w(i: &mut Insn, must: u8, may: u8, producer: bool) {
    i.must_write |= must;
    i.may_write |= may | must;
    if !producer && (may | must) != 0 {
        i.incidental = true;
    }
}

/// Record a call: AAPCS leaves the flags undefined afterwards.
fn call(i: &mut Insn) {
    w(i, NZCV, 0, false);
    i.opaque = true;
}

/// Decode one 16-bit instruction into `i`.
fn decode16(i: &mut Insn, hw: u16, in_it: bool) {
    let pc = i.off as i64 + 4;
    match hw >> 11 {
        // LSL/LSR/ASR #imm (LSL #0 is MOVS rd, rm: C unchanged)
        0b00000..=0b00010 => {
            if !in_it {
                let imm0 = (hw >> 6) & 0x1F == 0 && hw >> 11 == 0;
                let c = if imm0 { 0 } else { C };
                w(i, N | Z | c, 0, false);
            }
        }
        // ADDS/SUBS reg / imm3, MOVS #imm8, ADDS/SUBS #imm8
        0b00011 | 0b00110 | 0b00111 => {
            if !in_it {
                w(i, NZCV, 0, false);
            }
        }
        0b00100 => {
            if !in_it {
                w(i, N | Z, 0, false);
            }
        }
        0b00101 => w(i, NZCV, 0, true), // CMP #imm8: always sets
        0b01000 if hw & 0x0400 == 0 => {
            // 010000 data processing (register)
            let opc = (hw >> 6) & 0xF;
            match opc {
                0x8 => w(i, N | Z, 0, true),      // TST
                0xA | 0xB => w(i, NZCV, 0, true), // CMP / CMN
                _ => {
                    if matches!(opc, 0x5 | 0x6) {
                        i.reads |= C; // ADC / SBC
                    }
                    if !in_it {
                        let (must, may) = match opc {
                            0x0 | 0x1 | 0xC | 0xD | 0xE | 0xF => (N | Z, 0), // AND EOR ORR MUL BIC MVN
                            0x2..=0x4 | 0x7 => (N | Z, C),                   // shifts by register
                            _ => (NZCV, 0),                                  // ADC SBC RSB
                        };
                        w(i, must, may, false);
                    }
                }
            }
        }
        0b01000 => {
            // 010001 special data processing / branch exchange
            let op = (hw >> 8) & 3;
            let rd = ((hw >> 4) & 0x8) | (hw & 7);
            let rm = (hw >> 3) & 0xF;
            match op {
                0 | 2 if rd == 15 => {
                    // ADD pc / MOV pc: computed jump (MOV pc, lr = return)
                    i.flow = if op == 2 && rm == 14 {
                        Flow::Return
                    } else {
                        Flow::Unknown
                    };
                }
                0 | 2 => {}               // ADD / MOV high: no flags
                1 => w(i, NZCV, 0, true), // CMP high
                _ if hw & 0x7 != 0 => unknown(i),
                _ => {
                    if hw & 0x80 != 0 {
                        call(i); // BLX rm
                    } else if rm == 14 {
                        i.flow = Flow::Return; // BX LR
                    } else {
                        i.flow = Flow::Unknown;
                    }
                }
            }
        }
        0b01001..=0b10101 => {} // LDR literal, loads/stores, ADR, ADD SP
        0b10110 | 0b10111 => match hw >> 8 {
            0xB0 | 0xB2 | 0xB4 | 0xB5 => {} // ADD/SUB SP, extends, PUSH
            0xB1 | 0xB3 | 0xB9 | 0xBB => {
                // CBZ / CBNZ
                let imm = ((((hw >> 9) & 1) << 6) | (((hw >> 3) & 0x1F) << 1)) as i64;
                i.flow = Flow::Cond(pc + imm);
            }
            0xBA if hw & 0xC0 != 0x80 => {} // REV / REV16 / REVSH
            0xBC | 0xBD => {
                if hw & 0x0100 != 0 {
                    i.flow = Flow::Return; // POP {.., pc}
                }
            }
            0xBE => i.flow = Flow::Stop, // BKPT
            // IT: the members read its condition (attached in `verify`); the
            // IT instruction itself reads nothing.
            0xBF if hw & 0xF != 0 => {}
            0xBF if hw & 0xFF0F == 0xBF00 && (hw >> 4) & 0xF <= 4 => {} // NOP/YIELD/WFE/WFI/SEV
            _ => unknown(i),
        },
        0b11000 | 0b11001 => {} // STM / LDM (16-bit LDM cannot load PC)
        0b11010 | 0b11011 => {
            let cond = (hw >> 8) & 0xF;
            match cond {
                0xE => i.flow = Flow::Stop, // UDF
                0xF => call(i),             // SVC: treat as a call
                _ => {
                    i.reads |= cond_reads(cond);
                    i.flow = Flow::Cond(pc + sext(((hw & 0xFF) as u32) << 1, 9));
                }
            }
        }
        0b11100 => i.flow = Flow::Jump(pc + sext(((hw & 0x7FF) as u32) << 1, 12)),
        _ => unknown(i), // a wide prefix never reaches here
    }
}

/// Decode one 32-bit instruction into `i`.
fn decode32(i: &mut Insn, hw: u16, hw2: u16) {
    let pc = i.off as i64 + 4;
    if hw >> 11 == 0b11110 && hw2 & 0x8000 != 0 {
        // branches and miscellaneous control
        let s = ((hw >> 10) & 1) as u32;
        let j1 = ((hw2 >> 13) & 1) as u32;
        let j2 = ((hw2 >> 11) & 1) as u32;
        match hw2 & 0x5000 {
            0x5000 => call(i),                 // BL
            0x4000 if hw2 & 1 == 0 => call(i), // BLX imm
            0x1000 => {
                let i1 = 1 ^ (j1 ^ s);
                let i2 = 1 ^ (j2 ^ s);
                let imm = (s << 24)
                    | (i1 << 23)
                    | (i2 << 22)
                    | (((hw & 0x3FF) as u32) << 12)
                    | (((hw2 & 0x7FF) as u32) << 1);
                i.flow = Flow::Jump(pc + sext(imm, 25));
            }
            0x0000 => {
                let cond = (hw >> 6) & 0xF;
                if cond < 0xE {
                    let imm = (s << 20)
                        | (j2 << 19)
                        | (j1 << 18)
                        | (((hw & 0x3F) as u32) << 12)
                        | (((hw2 & 0x7FF) as u32) << 1);
                    i.reads |= cond_reads(cond);
                    i.flow = Flow::Cond(pc + sext(imm, 21));
                } else if hw & 0xFFE0 == 0xF380 && hw2 & 0xF300 == 0x8000 {
                    // MSR: NZCV only for an APSR-including SYSm (0..=3) with
                    // mask<1> (nzcvq) set; BASEPRI/PRIMASK/MSP… touch none.
                    if hw2 & 0xFF < 4 && hw2 & 0x0800 != 0 {
                        w(i, NZCV, 0, true);
                    }
                } else if hw == 0xF3EF && hw2 & 0xF000 == 0x8000 {
                    if hw2 & 0xFF < 4 {
                        i.reads |= NZCV; // MRS of an APSR-including register
                    }
                } else if hw == 0xF3AF && hw2 & 0xFF00 == 0x8000 && hw2 & 0xFF <= 4 {
                    // NOP.W / YIELD.W / WFE.W / WFI.W / SEV.W
                } else if hw == 0xF3BF && matches!(hw2 & 0xFFF0, 0x8F40 | 0x8F50 | 0x8F60) {
                    // DSB / DMB / ISB
                } else {
                    unknown(i);
                }
            }
            _ => unknown(i),
        }
        return;
    }
    if hw >> 11 == 0b11110 {
        if hw & 0x0200 == 0 {
            // data processing (modified immediate)
            let op = (hw >> 5) & 0xF;
            if !matches!(op, 0..=4 | 8 | 10 | 11 | 13 | 14) {
                return unknown(i);
            }
            let s = hw & 0x10 != 0;
            let rd = (hw2 >> 8) & 0xF;
            // ThumbExpandImm_C writes C only for a rotated immediate.
            let rot = (((hw >> 10) & 1) << 3) | ((hw2 >> 12) & 7);
            let (reads, must, may, producer) = dp_effect(op, rd, s, rot >= 4);
            i.reads |= reads;
            w(i, must, may, producer);
        } else {
            // plain binary immediate (ADDW, MOVW, SUBW, MOVT, SSAT, SBFX,
            // BFI, USAT, UBFX): no NZCV
            let op = (hw >> 4) & 0x1F;
            if !matches!(
                op,
                0b00000
                    | 0b00100
                    | 0b01010
                    | 0b01100
                    | 0b10000
                    | 0b10010
                    | 0b10100
                    | 0b10110
                    | 0b11000
                    | 0b11010
                    | 0b11100
            ) {
                unknown(i);
            }
        }
        return;
    }
    match hw >> 8 {
        0xEA | 0xEB => {
            // data processing (shifted register)
            let op = (hw >> 5) & 0xF;
            if hw2 & 0x8000 != 0 || !matches!(op, 0..=4 | 6 | 8 | 10 | 11 | 13 | 14) {
                return unknown(i); // incl. v8.1-M CSEL & co, which read flags
            }
            let s = hw & 0x10 != 0;
            let rd = (hw2 >> 8) & 0xF;
            let imm = (((hw2 >> 12) & 7) << 2) | ((hw2 >> 6) & 3);
            let ty = (hw2 >> 4) & 3;
            if ty == 3 && imm == 0 {
                i.reads |= C; // RRX reads the carry
            }
            // Shift_C leaves C alone only for LSL #0.
            let (reads, must, may, producer) = dp_effect(op, rd, s, !(ty == 0 && imm == 0));
            i.reads |= reads;
            w(i, must, may, producer);
        }
        0xE8 | 0xE9 if hw & 0x0040 == 0 => {
            // LDM / STM (incl. PUSH.W / POP.W): only IA (01) and DB (10)
            if !matches!((hw >> 7) & 3, 1 | 2) {
                return unknown(i);
            }
            if hw & 0x10 != 0 && hw2 & 0x8000 != 0 {
                // a load of PC: from SP! it is a return, otherwise a jump
                i.flow = if hw & 0xF == 13 {
                    Flow::Return
                } else {
                    Flow::Unknown
                };
            }
        }
        0xE8 | 0xE9 => {
            let p = hw & 0x0100 != 0;
            let wb = hw & 0x0020 != 0;
            if !p && !wb {
                // exclusive / table branch: TBB/TBH are indirect jumps;
                // everything else (LDREX, TT, …) is not emitted
                if hw & 0xFFF0 == 0xE8D0 && hw2 & 0xFFE0 == 0xF000 {
                    i.flow = Flow::Unknown;
                } else {
                    unknown(i);
                }
            } else if hw & 0xF == 15 && wb {
                unknown(i); // LDRD literal with writeback: undefined (SG)
            }
            // else LDRD / STRD: no flags
        }
        0xF8 | 0xF9 => {
            // single load / store
            if hw2 >> 12 == 15 {
                let ldr_word = hw & 0x10 != 0 && hw & 0x0160 == 0x0040;
                if ldr_word {
                    i.flow = Flow::Unknown; // load into PC: indirect jump
                } else {
                    unknown(i);
                }
            }
        }
        0xFA => {
            if hw & 0x80 == 0 && hw2 & 0xF0F0 == 0xF000 {
                // shift by register
                if hw & 0x10 != 0 {
                    w(i, N | Z, C, false);
                }
            } else if hw2 & 0xF0C0 == 0xF080 {
                // extends (hw<7> = 0) / REV, RBIT, CLZ, SEL (hw<7> = 1)
            } else {
                unknown(i);
            }
        }
        0xFB => {
            let ok = match hw & 0xFFF0 {
                0xFB00 => hw2 & 0x00E0 == 0, // MUL / MLA / MLS
                0xFB80 | 0xFBA0 | 0xFBC0 | 0xFBE0 => hw2 & 0x00F0 == 0, // long multiply
                0xFB90 | 0xFBB0 => hw2 & 0x00F0 == 0x00F0, // SDIV / UDIV
                _ => false,
            };
            if !ok {
                unknown(i);
            }
        }
        _ if hw & 0xEC00 == 0xEC00 => {
            // coprocessor / VFP / MVE
            if hw == 0xEEF1 && hw2 == 0xFA10 {
                w(i, NZCV, 0, true); // VMRS APSR_nzcv, FPSCR
            } else if hw & 0xFF80 == 0xFE00 && hw2 & 0x0E50 == 0x0A00 {
                // VSEL<cc> (FPv5): cc = EQ, VS, GE, GT
                let cond = [0u16, 6, 10, 12][((hw >> 4) & 3) as usize];
                i.reads |= cond_reads(cond);
            } else if hw & 0xFFE0 == 0xEC00 {
                unknown(i); // coprocessor op1 = 0000x: undefined
            }
        }
        _ => unknown(i),
    }
}

/// Decode one instruction at `off`. `in_it`: inside an IT block (16-bit data
/// processing does not set flags there).
fn decode(code: &[u8], off: usize, seg: usize, in_it: bool) -> Option<Insn> {
    let rd16 = |o: usize| -> Option<u16> {
        (o + 1 < code.len()).then(|| u16::from_le_bytes([code[o], code[o + 1]]))
    };
    let hw = rd16(off)?;
    let mut i = Insn {
        off,
        len: 2,
        seg,
        hw: (hw, None),
        reads: 0,
        may_write: 0,
        must_write: 0,
        incidental: false,
        opaque: false,
        flow: Flow::Next,
    };
    if matches!(hw >> 11, 0b11101..=0b11111) {
        let hw2 = rd16(off + 2)?;
        i.len = 4;
        i.hw = (hw, Some(hw2));
        decode32(&mut i, hw, hw2);
    } else {
        decode16(&mut i, hw, in_it);
    }
    Some(i)
}

fn hex(i: &Insn) -> String {
    match i.hw {
        (a, Some(b)) => format!("{a:04x} {b:04x}"),
        (a, None) => format!("{a:04x}"),
    }
}

/// The flags a straight-line instruction sequence (outside any IT block) may
/// write, decoded from its bytes. For tests and diagnostics: it reads the
/// same decoder [`verify`] does.
pub fn bytes_may_write(code: &[u8]) -> u8 {
    let mut off = 0;
    let mut m = 0;
    while let Some(i) = decode(code, off, 0, false) {
        m |= i.may_write;
        off += i.len;
    }
    m
}

/// Verify a function's code. `segments` are the per-op byte ranges, in
/// order; bytes outside every segment (literal pools) are data and are not
/// decoded. See the module doc for the rules.
pub fn verify(code: &[u8], segments: &[Segment]) -> Result<(), NzcvViolation> {
    // 1. Decode, tracking IT state linearly across segments.
    let mut insns: Vec<Insn> = Vec::new();
    let mut it_members: Vec<usize> = Vec::new(); // offsets of IT members
    let mut it_left = 0u32;
    let mut it_reads = 0u8;
    for (si, seg) in segments.iter().enumerate() {
        let end = seg.start + seg.len;
        let mut off = seg.start;
        while off < end {
            let in_it = it_left > 0;
            let Some(mut ins) = decode(&code[..end], off, si, in_it) else {
                // A truncated instruction at the end of a segment.
                let mut t = Insn {
                    off,
                    len: end - off,
                    seg: si,
                    hw: (code.get(off).copied().unwrap_or(0) as u16, None),
                    reads: 0,
                    may_write: 0,
                    must_write: 0,
                    incidental: false,
                    opaque: false,
                    flow: Flow::Next,
                };
                unknown(&mut t);
                insns.push(t);
                break;
            };
            if in_it {
                it_left -= 1;
                it_members.push(off);
                // A member reads its condition's flags (the inverse condition
                // reads the same ones) and may not execute: it kills nothing,
                // and a return/trap in it falls through.
                ins.reads |= it_reads;
                ins.must_write = 0;
                ins.flow = match ins.flow {
                    Flow::Return | Flow::Stop => Flow::Next,
                    Flow::Jump(t) => Flow::Cond(t),
                    f => f,
                };
            } else if ins.len == 2 && ins.hw.0 & 0xFF00 == 0xBF00 && ins.hw.0 & 0xF != 0 {
                it_left = 4 - (ins.hw.0 & 0xF).trailing_zeros();
                it_reads = cond_reads((ins.hw.0 >> 4) & 0xF);
            }
            off += ins.len;
            insns.push(ins);
        }
    }
    let n = insns.len();
    let idx_of = |t: i64| -> Option<usize> {
        if t < 0 {
            return None;
        }
        insns.binary_search_by_key(&(t as usize), |i| i.off).ok()
    };
    // A branch into the middle of an IT block is refused outright.
    for ins in &insns {
        if let Flow::Jump(t) | Flow::Cond(t) = ins.flow
            && t >= 0
            && it_members.binary_search(&(t as usize)).is_ok()
        {
            return Err(NzcvViolation {
                at: ins.off,
                bytes: hex(ins),
                flags: 0,
                reader: None,
                rule: "IT",
            });
        }
    }
    // 2. Successors. `None` in the list = unknown (all flags live).
    let succs: Vec<Vec<Option<usize>>> = (0..n)
        .map(|k| {
            let ins = &insns[k];
            let fall = || {
                let nx = ins.off + ins.len;
                if k + 1 < n && insns[k + 1].off == nx {
                    Some(k + 1)
                } else {
                    None // falls into data or off the end
                }
            };
            match ins.flow {
                Flow::Next => vec![fall()],
                Flow::Jump(t) => vec![idx_of(t)],
                Flow::Cond(t) => vec![idx_of(t), fall()],
                Flow::Return | Flow::Stop => vec![],
                Flow::Unknown => vec![None],
            }
        })
        .collect();
    // 3. Backward liveness fixpoint.
    let mut live_in = vec![0u8; n];
    let live_out = |live_in: &[u8], k: usize| -> u8 {
        succs[k]
            .iter()
            .map(|s| s.map_or(NZCV, |j| live_in[j]))
            .fold(0, |a, b| a | b)
    };
    loop {
        let mut changed = false;
        for k in (0..n).rev() {
            let out = live_out(&live_in, k);
            let v = insns[k].reads | (out & !insns[k].must_write);
            if v != live_in[k] {
                live_in[k] = v;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // A reader of `flags` reachable from `from` with no intervening kill.
    let find_reader = |from: usize, flags: u8| -> Option<usize> {
        let mut seen = vec![false; n];
        let mut work: Vec<(usize, u8)> =
            succs[from].iter().flatten().map(|&j| (j, flags)).collect();
        while let Some((j, f)) = work.pop() {
            if seen[j] {
                continue;
            }
            seen[j] = true;
            if insns[j].reads & f != 0 {
                return Some(insns[j].off);
            }
            let f2 = f & !insns[j].must_write;
            if f2 != 0 {
                work.extend(succs[j].iter().flatten().map(|&x| (x, f2)));
            }
        }
        None
    };
    // 4. R1 (Preserves) and W (Writes): per-instruction incidental writes.
    for (k, ins) in insns.iter().enumerate() {
        let (rule, writes) = match segments[ins.seg].contract {
            FlagContract::Preserves if ins.incidental => ("R1", ins.may_write),
            FlagContract::Writes(declared) => (
                "W",
                if ins.opaque {
                    ins.may_write
                } else {
                    ins.may_write & !declared
                },
            ),
            _ => continue,
        };
        let clobbered = writes & live_out(&live_in, k);
        if clobbered != 0 {
            return Err(NzcvViolation {
                at: ins.off,
                bytes: hex(ins),
                flags: clobbered,
                reader: find_reader(k, clobbered),
                rule,
            });
        }
    }
    // 5. R2: a flag-preserving or scratch op leaks no write to its exits.
    let mut seg_writes = vec![0u8; segments.len()];
    for ins in &insns {
        seg_writes[ins.seg] |= ins.may_write;
    }
    for (k, ins) in insns.iter().enumerate() {
        let si = ins.seg;
        if matches!(segments[si].contract, FlagContract::Writes(_)) || seg_writes[si] == 0 {
            continue;
        }
        for s in &succs[k] {
            let (leaving, live) = match s {
                Some(j) => (insns[*j].seg != si, live_in[*j]),
                None => (true, NZCV),
            };
            let clobbered = seg_writes[si] & live;
            if leaving && clobbered != 0 {
                return Err(NzcvViolation {
                    at: ins.off,
                    bytes: hex(ins),
                    flags: clobbered,
                    reader: s.and_then(|j| {
                        if insns[j].reads & clobbered != 0 {
                            Some(insns[j].off)
                        } else {
                            find_reader(j, clobbered)
                        }
                    }),
                    rule: "R2",
                });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn le(hws: &[u16]) -> Vec<u8> {
        hws.iter().flat_map(|h| h.to_le_bytes()).collect()
    }

    /// One segment per instruction (2- or 4-byte), with the given contracts.
    fn stream(insns: &[(&[u16], FlagContract)]) -> (Vec<u8>, Vec<Segment>) {
        let mut code = Vec::new();
        let mut segs = Vec::new();
        for (hws, c) in insns {
            segs.push(Segment {
                start: code.len(),
                len: hws.len() * 2,
                contract: *c,
            });
            code.extend(le(hws));
        }
        (code, segs)
    }

    use FlagContract::{Preserves as P, Scratch as S};
    const W: FlagContract = FlagContract::Writes(NZCV);

    // Encodings (all from the ARM ARM; cross-checked against llvm-mc):
    const CMP_R0_R1: u16 = 0x4288; // cmp r0, r1
    const MOVS_R0_1: u16 = 0x2001; // movs r0, #1
    const MOVS_R0_0: u16 = 0x2000; // movs r0, #0
    const BX_LR: u16 = 0x4770;

    /// RED: `cmp r0, r1; movs r0, #1; beq` — the MOVS (from a flag-preserving
    /// `Mov`) rewrites Z between the compare and the branch that reads it.
    #[test]
    fn cmp_movs_beq_is_rejected() {
        // beq +0 (to the bx lr right after it): d0 00 -> target = pc+4+0
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W), // 0
            (&[MOVS_R0_1], P), // 2
            (&[0xD0FF], P),    // 4: beq -> 4+4-2 = 6
            (&[BX_LR], P),     // 6
        ]);
        let v = verify(&code, &segs).unwrap_err();
        assert_eq!(v.rule, "R1");
        assert_eq!(v.at, 2);
        assert_eq!(v.flags & Z, Z, "{v}");
        assert_eq!(v.reader, Some(4));
    }

    /// The same stream with the flag-preserving move BEFORE the compare is
    /// fine: the MOVS's flags are dead (the CMP rewrites all four).
    #[test]
    fn movs_before_cmp_is_accepted() {
        let (code, segs) = stream(&[
            (&[MOVS_R0_1], P),
            (&[CMP_R0_R1], W),
            (&[0xD0FF], P),
            (&[BX_LR], P),
        ]);
        assert_eq!(verify(&code, &segs), Ok(()));
    }

    /// RED, the M2 shape: `ite eq; moveq r0,#1; movne r0,#0` lowered NAIVELY
    /// for ARMv6-M (no IT) as `movs r0,#0; bne skip; movs r0,#1; skip:` — the
    /// first MOVS destroys the compare the `bne` reads.
    #[test]
    fn naive_setcond_movs_then_branch_is_rejected() {
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W), // 0
            (&[MOVS_R0_0], P), // 2
            (&[0xD100], P),    // 4: bne -> 4+4 = 8 (skips the next movs)
            (&[MOVS_R0_1], P), // 6
            (&[BX_LR], P),     // 8
        ]);
        let v = verify(&code, &segs).unwrap_err();
        assert_eq!((v.rule, v.at, v.reader), ("R1", 2, Some(4)), "{v}");
    }

    /// RED, the other naive rewrite: branch over EACH member.
    /// `beq/bne`-guarded: `bne L1; movs r0,#1; L1: beq L2; movs r0,#0; L2:`
    /// — the first MOVS clears Z before the second branch reads it.
    #[test]
    fn naive_setcond_branch_over_each_member_is_rejected() {
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W), // 0
            (&[0xD100], P),    // 2: bne -> 2+4 = 6 (L1)
            (&[MOVS_R0_1], P), // 4
            (&[0xD000], P),    // 6 (L1): beq -> 6+4 = 10 (L2)
            (&[MOVS_R0_0], P), // 8
            (&[BX_LR], P),     // 10 (L2)
        ]);
        let v = verify(&code, &segs).unwrap_err();
        assert_eq!(v.rule, "R1");
        assert_eq!(v.at, 4, "{v}"); // the first movs, live Z read by beq
    }

    /// GREEN: the correct diamond.
    /// `beq L0; movs r0,#0; b L1; L0: movs r0,#1; L1: bx lr`
    #[test]
    fn diamond_setcond_is_accepted() {
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W), // 0
            (&[0xD002], P),    // 2: beq -> 2+4+4 = 10 (L0)
            (&[MOVS_R0_0], P), // 4
            (&[0xE001], P),    // 6: b -> 6+4+2 = 12 (L1)
            (&[0xBF00], P),    // 8: nop (unreachable)
            (&[MOVS_R0_1], P), // 10 (L0)
            (&[BX_LR], P),     // 12 (L1)
        ]);
        assert_eq!(verify(&code, &segs), Ok(()));
    }

    /// #709's shape, inside ONE op: `vmrs APSR_nzcv, fpscr; movs r0, #0;
    /// it eq; moveq r0, #1` is rejected by R1 even though the clobber and its
    /// reader are in the same op. The fixed order (MOVS first) is accepted.
    #[test]
    fn f32_compare_709_order_is_checked_inside_one_op() {
        let one_op = |hws: &[u16]| {
            let code = le(hws);
            let segs = vec![
                Segment {
                    start: 0,
                    len: code.len(),
                    contract: P,
                },
                Segment {
                    start: code.len(),
                    len: 2,
                    contract: P,
                },
            ];
            let mut c = code;
            c.extend(le(&[BX_LR]));
            verify(&c, &segs)
        };
        // vcmp.f32 s0, s1 = eeb4 0a60
        let bad = one_op(&[0xEEB4, 0x0A60, 0xEEF1, 0xFA10, MOVS_R0_0, 0xBF08, MOVS_R0_1]);
        assert_eq!(bad.unwrap_err().rule, "R1");
        let good = one_op(&[MOVS_R0_0, 0xEEB4, 0x0A60, 0xEEF1, 0xFA10, 0xBF08, MOVS_R0_1]);
        assert_eq!(good, Ok(()));
    }

    /// An i64 carry chain inside one `Scratch` op is allowed; the same op
    /// leaking its carry to a later reader is not (R2).
    #[test]
    fn scratch_op_chain_and_leak() {
        // adds r0, r0, r2 ; adc.w r1, r1, r3
        let chain: &[u16] = &[0x1880, 0xEB41, 0x0103];
        let (code, segs) = stream(&[(chain, S), (&[BX_LR], P)]);
        assert_eq!(verify(&code, &segs), Ok(()));
        // the same op as Preserves: its ADDS feeds a live C -> R1
        let (code, segs) = stream(&[(chain, P), (&[BX_LR], P)]);
        assert_eq!(verify(&code, &segs).unwrap_err().rule, "R1");
        // a Scratch op between a compare and its branch -> R2
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W), // 0
            (chain, S),        // 2..8
            (&[0xD0FF], P),    // 8: beq -> 10
            (&[BX_LR], P),     // 10
        ]);
        let v = verify(&code, &segs).unwrap_err();
        assert_eq!(v.rule, "R2", "{v}");
    }

    /// Calls clobber the flags; a compare whose branch sits after a call is
    /// read across a clobber.
    #[test]
    fn call_between_compare_and_branch_is_rejected() {
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W),      // 0
            (&[0xF000, 0xF800], P), // 2: bl
            (&[0xD0FF], P),         // 6: beq -> 8
            (&[BX_LR], P),          // 8
        ]);
        assert!(verify(&code, &segs).is_err());
    }

    /// Unknown control flow is conservative: an indirect jump leaves every
    /// flag live, so an incidental write before it is rejected.
    #[test]
    fn indirect_jump_is_conservative() {
        let (code, segs) = stream(&[(&[MOVS_R0_1], P), (&[0x4718], P)]); // bx r3
        assert!(verify(&code, &segs).is_err());
        let (code, segs) = stream(&[(&[MOVS_R0_1], P), (&[BX_LR], P)]);
        assert_eq!(verify(&code, &segs), Ok(()));
    }

    /// In an IT block the 16-bit forms do not set flags, and the members
    /// read the condition: `cmp; ite eq; moveq; movne; bx lr` is accepted.
    #[test]
    fn it_block_members_do_not_set_flags() {
        let (code, segs) = stream(&[
            (&[CMP_R0_R1], W),
            (&[0xBF0C, MOVS_R0_1, MOVS_R0_0], P), // ite eq; moveq; movne
            (&[BX_LR], P),
        ]);
        assert_eq!(verify(&code, &segs), Ok(()));
    }

    /// RED on the REAL encoder, ARMv7-M, today: `ArmOp::Mov rd, #imm8` is
    /// flag-preserving in the model and encodes as the flag-setting `MOVS`.
    /// Placed between a compare and its branch, the verifier refuses it; the
    /// same ops with the move before the compare pass.
    #[cfg(feature = "arm-cortex-m")]
    #[test]
    fn real_encoder_mov_between_cmp_and_bcc_is_rejected() {
        use crate::arm_encoder::ArmEncoder;
        use synth_synthesis::rules::{Condition, Operand2, Reg};
        let enc = ArmEncoder::new_thumb2_with_fpu(None);
        let cmp = ArmOp::Cmp {
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        };
        let mov = ArmOp::Mov {
            rd: Reg::R0,
            op2: Operand2::Imm(1),
        };
        // beq to the bx two halfwords on: (6 - 4 - 4) / 2 = -1
        let beq = ArmOp::BCondOffset {
            cond: Condition::EQ,
            offset: -1,
        };
        let bx = ArmOp::Bx { rm: Reg::LR };
        let build = |ops: &[ArmOp]| {
            let mut code = Vec::new();
            let mut segs = Vec::new();
            for op in ops {
                let b = enc.encode(op).unwrap();
                segs.push(Segment {
                    start: code.len(),
                    len: b.len(),
                    contract: op_flag_contract(op),
                });
                code.extend(b);
            }
            (code, segs)
        };
        let (code, segs) = build(&[cmp.clone(), mov.clone(), beq.clone(), bx.clone()]);
        assert_eq!(code.len(), 8, "all four ops are 16-bit: {code:02x?}");
        assert_eq!(&code[2..4], &[0x01, 0x20], "Mov r0,#1 is MOVS on v7-M");
        let v = verify(&code, &segs).unwrap_err();
        assert_eq!((v.rule, v.at, v.reader), ("R1", 2, Some(4)), "{v}");
        let (code, segs) = build(&[mov, cmp, beq, bx]);
        assert_eq!(verify(&code, &segs), Ok(()));
    }

    /// The explicit flag-setting variants: their Thumb and A32 bytes equal
    /// llvm-mc's (`-triple=thumbv7m-none-eabi` / `armv7r-none-eabi`
    /// `-show-encoding`), and the verifier's decoder reads N and Z written by
    /// every Thumb form — the variant NAME and the BYTES agree.
    #[cfg(feature = "arm-cortex-m")]
    #[test]
    fn flag_setting_variants_match_llvm_mc_and_decode_as_flag_writes() {
        use crate::arm_encoder::ArmEncoder;
        use Reg::*;
        use synth_synthesis::rules::{Operand2, Reg};
        let t = ArmEncoder::new_thumb2_with_fpu(None);
        let a = ArmEncoder::new_arm32();
        let imm = Operand2::Imm;
        let reg = Operand2::Reg;
        // (op, thumb bytes, Some(a32 bytes))
        let cases: Vec<(ArmOp, Vec<u8>, Option<Vec<u8>>)> = vec![
            (
                ArmOp::Movs {
                    rd: R1,
                    op2: imm(5),
                },
                vec![0x05, 0x21],
                Some(vec![0x05, 0x10, 0xb0, 0xe3]),
            ),
            (
                ArmOp::Mvns {
                    rd: R1,
                    op2: reg(R2),
                },
                vec![0xd1, 0x43],
                Some(vec![0x02, 0x10, 0xf0, 0xe1]),
            ),
            (
                ArmOp::Ands {
                    rd: R1,
                    rn: R1,
                    op2: reg(R3),
                },
                vec![0x19, 0x40],
                None,
            ),
            (
                ArmOp::Orrs {
                    rd: R1,
                    rn: R1,
                    op2: reg(R3),
                },
                vec![0x19, 0x43],
                None,
            ),
            (
                ArmOp::Eors {
                    rd: R1,
                    rn: R1,
                    op2: reg(R3),
                },
                vec![0x59, 0x40],
                None,
            ),
            (
                ArmOp::Ands {
                    rd: R1,
                    rn: R2,
                    op2: reg(R3),
                },
                vec![0x12, 0xea, 0x03, 0x01],
                Some(vec![0x03, 0x10, 0x12, 0xe0]),
            ),
            (
                ArmOp::Orrs {
                    rd: R1,
                    rn: R2,
                    op2: reg(R3),
                },
                vec![0x52, 0xea, 0x03, 0x01],
                Some(vec![0x03, 0x10, 0x92, 0xe1]),
            ),
            (
                ArmOp::Eors {
                    rd: R1,
                    rn: R2,
                    op2: reg(R3),
                },
                vec![0x92, 0xea, 0x03, 0x01],
                Some(vec![0x03, 0x10, 0x32, 0xe0]),
            ),
            (
                ArmOp::Ands {
                    rd: R8,
                    rn: R9,
                    op2: imm(0xff00),
                },
                vec![0x19, 0xf4, 0x7f, 0x48],
                None,
            ),
            (
                ArmOp::Lsls {
                    rd: R1,
                    rn: R2,
                    shift: 3,
                },
                vec![0xd1, 0x00],
                Some(vec![0x82, 0x11, 0xb0, 0xe1]),
            ),
            (
                ArmOp::Lsrs {
                    rd: R1,
                    rn: R2,
                    shift: 3,
                },
                vec![0xd1, 0x08],
                Some(vec![0xa2, 0x11, 0xb0, 0xe1]),
            ),
            (
                ArmOp::Lsrs {
                    rd: R1,
                    rn: R2,
                    shift: 32,
                },
                vec![0x11, 0x08],
                None,
            ),
            (
                ArmOp::Asrs {
                    rd: R1,
                    rn: R2,
                    shift: 3,
                },
                vec![0xd1, 0x10],
                None,
            ),
            (
                ArmOp::Asrs {
                    rd: R1,
                    rn: R2,
                    shift: 32,
                },
                vec![0x11, 0x10],
                Some(vec![0x42, 0x10, 0xb0, 0xe1]),
            ),
            (
                ArmOp::Asrs {
                    rd: R8,
                    rn: R9,
                    shift: 32,
                },
                vec![0x5f, 0xea, 0x29, 0x08],
                None,
            ),
            (
                ArmOp::Lsls {
                    rd: R8,
                    rn: R9,
                    shift: 3,
                },
                vec![0x5f, 0xea, 0xc9, 0x08],
                None,
            ),
            (
                ArmOp::Movs {
                    rd: R8,
                    op2: imm(1),
                },
                vec![0x5f, 0xf0, 0x01, 0x08],
                None,
            ),
            (
                ArmOp::Movs {
                    rd: R8,
                    op2: reg(R9),
                },
                vec![0x5f, 0xea, 0x09, 0x08],
                None,
            ),
            (
                ArmOp::Mvns {
                    rd: R8,
                    op2: reg(R9),
                },
                vec![0x7f, 0xea, 0x09, 0x08],
                None,
            ),
            (
                ArmOp::Mvns {
                    rd: R8,
                    op2: imm(0),
                },
                vec![0x7f, 0xf0, 0x00, 0x08],
                None,
            ),
            (
                ArmOp::Muls {
                    rd: R1,
                    rn: R1,
                    rm: R2,
                },
                vec![0x51, 0x43],
                Some(vec![0x91, 0x02, 0x11, 0xe0]), // llvm-mc `muls r1, r1, r2`
            ),
        ];
        for (op, th, a32) in &cases {
            let got = t.encode(op).unwrap_or_else(|e| panic!("{op:?}: {e}"));
            assert_eq!(&got, th, "{op:?} thumb");
            assert_eq!(
                bytes_may_write(&got) & (N | Z),
                N | Z,
                "{op:?} must decode as N,Z-writing"
            );
            if let Some(w) = a32 {
                assert_eq!(&a.encode(op).unwrap(), w, "{op:?} a32");
            }
            assert_eq!(op_flag_contract(op), FlagContract::Writes(0), "{op:?}");
        }
        // Loud refusals, never a different instruction.
        for op in [
            ArmOp::Muls {
                rd: R1,
                rn: R2,
                rm: R3,
            },
            ArmOp::Muls {
                rd: R8,
                rn: R8,
                rm: R1,
            },
            ArmOp::Lsrs {
                rd: R1,
                rn: R2,
                shift: 0,
            },
            ArmOp::Asrs {
                rd: R1,
                rn: R2,
                shift: 33,
            },
            ArmOp::Lsls {
                rd: R1,
                rn: R2,
                shift: 32,
            },
            ArmOp::Ands {
                rd: R1,
                rn: R2,
                op2: imm(0x1234_5678),
            },
        ] {
            assert!(t.encode(&op).is_err(), "{op:?} thumb must refuse");
        }
        // F6 (review 7): llvm-mc operand order on A32 (`muls r3, r4, r5`).
        assert_eq!(
            a.encode(&ArmOp::Muls {
                rd: R3,
                rn: R4,
                rm: R5
            })
            .unwrap(),
            vec![0x94, 0x05, 0x13, 0xe0]
        );
        // F6: SP is UNPREDICTABLE in the Thumb-2 S=1 wide forms, PC in A32
        // MULS, and A32 Operand2 has no encoding here for a non-LSL shifted
        // register (it used to be encoded silently as LSL): typed refusals.
        let sp_cases = [
            ArmOp::Movs {
                rd: SP,
                op2: imm(1),
            },
            ArmOp::Movs {
                rd: R8,
                op2: reg(SP),
            },
            ArmOp::Mvns {
                rd: SP,
                op2: reg(R9),
            },
            ArmOp::Ands {
                rd: R1,
                rn: SP,
                op2: reg(R3),
            },
            ArmOp::Orrs {
                rd: R8,
                rn: R9,
                op2: reg(SP),
            },
            ArmOp::Eors {
                rd: SP,
                rn: R9,
                op2: imm(1),
            },
            ArmOp::Lsls {
                rd: SP,
                rn: R9,
                shift: 1,
            },
            ArmOp::Asrs {
                rd: R8,
                rn: SP,
                shift: 1,
            },
        ];
        for op in &sp_cases {
            let e = t.encode(op).unwrap_err().to_string();
            assert!(e.contains("SP"), "{op:?}: {e}");
        }
        for op in [
            ArmOp::Muls {
                rd: PC,
                rn: R1,
                rm: R2,
            },
            ArmOp::Muls {
                rd: R1,
                rn: PC,
                rm: R2,
            },
            ArmOp::Muls {
                rd: R1,
                rn: R1,
                rm: PC,
            },
        ] {
            assert!(a.encode(&op).is_err(), "{op:?} a32 must refuse PC");
        }
        for shift in [
            synth_synthesis::rules::ShiftType::LSR,
            synth_synthesis::rules::ShiftType::ASR,
            synth_synthesis::rules::ShiftType::ROR,
        ] {
            let op = ArmOp::Movs {
                rd: R1,
                op2: Operand2::RegShift {
                    rm: R2,
                    shift,
                    amount: 3,
                },
            };
            assert!(a.encode(&op).is_err(), "{op:?} a32 must refuse");
        }
        assert!(
            a.encode(&ArmOp::Movs {
                rd: R1,
                op2: Operand2::RegShift {
                    rm: R2,
                    shift: synth_synthesis::rules::ShiftType::LSL,
                    amount: 3
                }
            })
            .is_ok()
        );
        assert!(
            a.encode(&ArmOp::Lsrs {
                rd: R1,
                rn: R2,
                shift: 0
            })
            .is_err()
        );
        // The hazard the verifier exists for: the flag-PRESERVING twins'
        // low-register Thumb forms DO write flags on v7-M; the high-register
        // forms do not.
        let w = |op: ArmOp| bytes_may_write(&t.encode(&op).unwrap());
        assert_ne!(
            w(ArmOp::Mov {
                rd: R1,
                op2: imm(5)
            }),
            0
        );
        assert_ne!(
            w(ArmOp::Add {
                rd: R1,
                rn: R2,
                op2: reg(R3)
            }),
            0
        );
        assert_eq!(
            w(ArmOp::Mov {
                rd: R8,
                op2: imm(5)
            }),
            0
        );
        assert_eq!(
            w(ArmOp::Add {
                rd: R8,
                rn: R9,
                op2: reg(R3)
            }),
            0
        );
    }

    /// Every condition code reads exactly the flags the ARM ARM says.
    #[test]
    fn condition_codes_read_their_flags() {
        let want = [
            Z,
            Z,
            C,
            C,
            N,
            N,
            V,
            V,
            C | Z,
            C | Z,
            N | V,
            N | V,
            N | Z | V,
            N | Z | V,
            0,
            0,
        ];
        for (cond, w) in want.iter().enumerate() {
            assert_eq!(cond_reads(cond as u16), *w, "cond {cond:#x}");
            // and a 16-bit Bcond with that condition reads them
            if cond < 0xE {
                let mut i = Insn {
                    off: 0,
                    len: 2,
                    seg: 0,
                    hw: (0, None),
                    reads: 0,
                    may_write: 0,
                    must_write: 0,
                    incidental: false,
                    opaque: false,
                    flow: Flow::Next,
                };
                decode16(&mut i, 0xD000 | ((cond as u16) << 8), false);
                assert_eq!(i.reads, *w, "b{cond:#x}");
                // and the wide Bcond.W
                let mut j = i.clone();
                j.reads = 0;
                decode32(&mut j, 0xF000 | ((cond as u16) << 6), 0x8000);
                assert_eq!(j.reads, *w, "b{cond:#x}.w");
                assert!(matches!(j.flow, Flow::Cond(_)));
            }
        }
    }

    /// The 443-case llvm-mc probe set from cold review 7 (#1301): every
    /// stream gets exactly its expected verdict. Covers the per-flag write
    /// table (16-bit and wide), carry readers, IT blocks (incl. conditional
    /// returns and branches INTO a block), CBZ, loops (the fixpoint), calls,
    /// VMRS/MSR/MRS, VSEL, returns, indirect jumps and undefined encodings.
    #[test]
    fn llvm_mc_probe_set_review7() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/fixtures/nzcv_probe_review7_1301.txt"
        );
        let text = std::fs::read_to_string(path).expect("fixture");
        let mut n = 0;
        let mut bad = Vec::new();
        for line in text.lines().filter(|l| !l.starts_with('#')) {
            let f: Vec<&str> = line.split('|').collect();
            assert_eq!(f.len(), 4, "{line}");
            let code: Vec<u8> = (0..f[1].len() / 2)
                .map(|i| u8::from_str_radix(&f[1][2 * i..2 * i + 2], 16).unwrap())
                .collect();
            let segs: Vec<Segment> = f[2]
                .split(',')
                .map(|s| {
                    let q: Vec<&str> = s.split(':').collect();
                    Segment {
                        start: q[0].parse().unwrap(),
                        len: q[1].parse().unwrap(),
                        contract: match q[2] {
                            "P" => P,
                            "S" => S,
                            _ => W,
                        },
                    }
                })
                .collect();
            let got = match verify(&code, &segs) {
                Ok(()) => "ACCEPT",
                Err(_) => "REJECT",
            };
            if got != f[3] {
                bad.push(format!("{}: want {} got {}", f[0], f[3], got));
            }
            n += 1;
        }
        assert_eq!(n, 443, "probe set size");
        assert!(
            bad.is_empty(),
            "{} mismatches:\n{}",
            bad.len(),
            bad.join("\n")
        );
    }

    /// F2 (review 7): the explicit flag-setting variants declare no flag
    /// result, so written with them the naive SetCond rewrite and a carry
    /// clobber between ADDS and ADC are refused — on the REAL encoder.
    #[cfg(feature = "arm-cortex-m")]
    #[test]
    fn flag_setting_variants_cannot_clobber_live_flags() {
        use crate::arm_encoder::ArmEncoder;
        use synth_synthesis::rules::{Condition, Operand2, Reg};
        let t = ArmEncoder::new_thumb2_with_fpu(None);
        let run = |ops: &[ArmOp]| {
            let mut code = Vec::new();
            let mut segs = Vec::new();
            for op in ops {
                let b = t.encode(op).unwrap();
                segs.push(Segment {
                    start: code.len(),
                    len: b.len(),
                    contract: op_flag_contract(op),
                });
                code.extend(b);
            }
            verify(&code, &segs)
        };
        let cmp = ArmOp::Cmp {
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        };
        let movs = |i| ArmOp::Movs {
            rd: Reg::R0,
            op2: Operand2::Imm(i),
        };
        let bx = ArmOp::Bx { rm: Reg::LR };
        // cmp; movs r0,#0; bne +0 (over the next movs); movs r0,#1; bx lr
        let v = run(&[
            cmp.clone(),
            movs(0),
            ArmOp::BCondOffset {
                cond: Condition::NE,
                offset: 0,
            },
            movs(1),
            bx.clone(),
        ])
        .unwrap_err();
        assert_eq!((v.rule, v.at), ("W", 2), "{v}");
        let adds = ArmOp::Adds {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R2),
        };
        let adc = ArmOp::Adc {
            rd: Reg::R1,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R3),
        };
        for mid in [
            ArmOp::Lsls {
                rd: Reg::R5,
                rn: Reg::R5,
                shift: 1,
            },
            ArmOp::Movs {
                rd: Reg::R8,
                op2: Operand2::Imm(0x1000), // rotated: the wide form writes C
            },
        ] {
            let v = run(&[adds.clone(), mid.clone(), adc.clone(), bx.clone()]).unwrap_err();
            assert_eq!(v.rule, "W", "{mid:?}: {v}");
            assert_eq!(v.flags, C, "{mid:?}: {v}");
        }
        // Dead flags: the variants are fine (the M2 diamond uses them).
        assert_eq!(run(&[movs(1), cmp.clone(), bx.clone()]), Ok(()));
        // A declared producer may leave its flags live; an undeclared flag of
        // its bytes may not (ADDS declared as producing N,Z only).
        let lsls = [0x006du16.to_le_bytes(), 0x4159u16.to_le_bytes()].concat(); // lsls r5,r5,#1 ; adcs r1,r3
        let segs = |d| {
            vec![
                Segment {
                    start: 0,
                    len: 2,
                    contract: FlagContract::Writes(d),
                },
                Segment {
                    start: 2,
                    len: 2,
                    contract: P,
                },
            ]
        };
        let mut code = lsls.clone();
        code.extend(0x4770u16.to_le_bytes());
        let mut s3 = segs(NZCV);
        s3.push(Segment {
            start: 4,
            len: 2,
            contract: P,
        });
        assert_eq!(verify(&code, &s3), Ok(()));
        let mut s4 = segs(N | Z);
        s4.push(Segment {
            start: 4,
            len: 2,
            contract: P,
        });
        assert_eq!(verify(&code, &s4).unwrap_err().flags, C);
    }

    /// F1 (review 7): a mid-stream literal island. The branch over the pool
    /// is its own segment and the pool word is data. Without the branch's
    /// segment the instruction before it falls into a gap (all flags live).
    #[test]
    fn literal_island_is_branched_over_not_decoded() {
        // movs r0,#1 ; b.n +2 (over 2 pad + 4 pool bytes) ; [00 00 de ad be ef] ; bx lr
        let mut code = le(&[MOVS_R0_1, 0xE002]);
        code.extend([0, 0, 0xde, 0xad, 0xbe, 0xef]);
        code.extend(le(&[BX_LR]));
        let seg = |start, len| Segment {
            start,
            len,
            contract: P,
        };
        assert_eq!(verify(&code, &[seg(0, 2), seg(2, 2), seg(10, 2)]), Ok(()));
        let v = verify(&code, &[seg(0, 2), seg(10, 2)]).unwrap_err();
        assert_eq!((v.rule, v.reader), ("R1", None), "{v}");
        assert!(v.to_string().contains("no reader decoded"), "{v}");
    }

    /// Structural cases the probe set reaches only indirectly.
    #[test]
    fn structural_edges() {
        let seg = |start, len, contract| Segment {
            start,
            len,
            contract,
        };
        // A truncated wide prefix at the end of a segment is unknown: the
        // clobber before it is refused.
        let code = le(&[MOVS_R0_1, 0xF000]);
        assert!(verify(&code, &[seg(0, 2, P), seg(2, 2, P)]).is_err());
        // TBB is an indirect jump: it does NOT fall through to the bx lr.
        let code = le(&[MOVS_R0_1, 0xE8DF, 0xF000, BX_LR]);
        assert!(verify(&code, &[seg(0, 2, P), seg(2, 4, P), seg(6, 2, P)]).is_err());
        // B.W's target is followed: movs; b.w +0 (to bx lr, skipping a beq).
        let code = le(&[CMP_R0_R1, MOVS_R0_1, 0xF000, 0xB802, 0xD0FF, BX_LR, BX_LR]);
        // 0: cmp 2: movs 4: b.w -> 4+4+4 = 12 ; 8: beq ; 10: bx ; 12: bx
        let segs = [
            seg(0, 2, W),
            seg(2, 2, P),
            seg(4, 4, P),
            seg(8, 2, P),
            seg(10, 2, P),
            seg(12, 2, P),
        ];
        assert_eq!(verify(&code, &segs), Ok(()));
        // ... and the beq is unreachable only because of the jump: as a
        // fall-through B.W would reach it.
        let code2 = le(&[CMP_R0_R1, MOVS_R0_1, 0xF000, 0xB800, 0xD0FF, BX_LR, BX_LR]);
        assert!(verify(&code2, &segs).is_err());
        // A branch into the middle of an IT block is refused (rule IT).
        // 0: cmp ; 2: b -> 8 ; 4: itt cs ; 6: movcs ; 8: movcs ; 10: bx lr
        let code = le(&[CMP_R0_R1, 0xE001, 0xBF24, 0x2201, 0x2301, BX_LR]);
        let v = verify(
            &code,
            &[seg(0, 2, W), seg(2, 2, P), seg(4, 6, P), seg(10, 2, P)],
        )
        .unwrap_err();
        assert_eq!(v.rule, "IT", "{v}");
        // A conditional return inside an IT block falls through: Z stays
        // live to the beq after it.
        // 0: cmp ; 2: movs ; 4: it cs ; 6: bxcs lr ; 8: beq -> 12 ; 10: nop ; 12: bx
        let code = le(&[CMP_R0_R1, MOVS_R0_1, 0xBF28, BX_LR, 0xD000, 0xBF00, BX_LR]);
        let segs = [
            seg(0, 2, W),
            seg(2, 2, P),
            seg(4, 4, P),
            seg(8, 2, P),
            seg(10, 2, P),
            seg(12, 2, P),
        ];
        assert!(verify(&code, &segs).is_err());
        // Liveness needs the fixpoint: the reader is at the loop HEAD and the
        // clobber at the bottom, reached only over the back edge.
        // 0: cmp ; 2: add r8,r9 ; 4: beq -> 10 ; 6: movs ; 8: b -> 2 ; 10: bx
        let code = le(&[CMP_R0_R1, 0x44C8, 0xD001, MOVS_R0_1, 0xE7FB, BX_LR]);
        let segs = [
            seg(0, 2, W),
            seg(2, 2, P),
            seg(4, 2, P),
            seg(6, 2, P),
            seg(8, 2, P),
            seg(10, 2, P),
        ];
        let v = verify(&code, &segs).unwrap_err();
        assert_eq!((v.rule, v.at), ("R1", 6), "{v}");
        // An undecodable instruction may be a branch: nothing after it is
        // trusted, so even alone before a return it is refused.
        let code = le(&[0xB700, BX_LR]);
        assert!(verify(&code, &[seg(0, 2, P), seg(2, 2, P)]).is_err());
        // A 16-bit data-processing member of an IT block sets NO flags:
        // 0: cmp ; 2: it cs ; 4: andcs r2,r3 ; 6: beq -> 10 ; 8: nop ; 10: bx
        let code = le(&[CMP_R0_R1, 0xBF28, 0x401A, 0xD000, 0xBF00, BX_LR]);
        assert_eq!(
            verify(
                &code,
                &[
                    seg(0, 2, W),
                    seg(2, 4, P),
                    seg(6, 2, P),
                    seg(8, 2, P),
                    seg(10, 2, P)
                ]
            ),
            Ok(())
        );
        // A call inside a Writes op is never a declared result.
        let code = le(&[CMP_R0_R1, 0xF000, 0xF800, 0xD0FF, BX_LR]);
        let v = verify(
            &code,
            &[seg(0, 2, W), seg(2, 4, W), seg(6, 2, P), seg(8, 2, P)],
        )
        .unwrap_err();
        assert_eq!(v.rule, "W", "{v}");
    }

    /// The contract table, pinned: what each listed op's MODEL claims.
    #[test]
    fn contract_table_is_pinned() {
        use synth_synthesis::rules::{Condition, Operand2, Reg};
        let r = Reg::R0;
        let o = Operand2::Reg(Reg::R1);
        assert_eq!(
            op_flag_contract(&ArmOp::Cmp {
                rn: r,
                op2: o.clone()
            }),
            FlagContract::Writes(NZCV)
        );
        assert_eq!(
            op_flag_contract(&ArmOp::Adds {
                rd: r,
                rn: r,
                op2: o.clone()
            }),
            FlagContract::Writes(NZCV)
        );
        let (l, h) = (Reg::R0, Reg::R1);
        let scratch = [
            ArmOp::I64Add {
                rdlo: l,
                rdhi: h,
                rnlo: l,
                rnhi: h,
                rmlo: l,
                rmhi: h,
            },
            ArmOp::I64Shl {
                rd_lo: l,
                rd_hi: h,
                rn_lo: l,
                rn_hi: h,
                rm_lo: l,
                rm_hi: h,
            },
            ArmOp::I64SetCond {
                rd: r,
                rn_lo: l,
                rn_hi: h,
                rm_lo: l,
                rm_hi: h,
                cond: Condition::LT,
            },
        ];
        for op in &scratch {
            assert_eq!(op_flag_contract(op), FlagContract::Scratch, "{op:?}");
        }
        // F5: I64SetCondZ is checked fully (its expansion needs no Scratch).
        assert_eq!(
            op_flag_contract(&ArmOp::I64SetCondZ {
                rd: r,
                rn_lo: l,
                rn_hi: h,
            }),
            FlagContract::Preserves
        );
        assert_eq!(
            op_flag_contract(&ArmOp::Mov { rd: r, op2: o }),
            FlagContract::Preserves
        );
    }

    /// Why the i64 expansions are Scratch, on the REAL encoder: `I64Shl`'s
    /// bytes chain flags internally (rejected as Preserves, accepted as
    /// Scratch); `I64SetCondZ`'s do not (accepted as Preserves).
    #[cfg(feature = "arm-cortex-m")]
    #[test]
    fn real_i64_expansions_and_their_contracts() {
        use crate::arm_encoder::ArmEncoder;
        use synth_synthesis::rules::Reg;
        let t = ArmEncoder::new_thumb2_with_fpu(None);
        let with = |op: &ArmOp, c| {
            let mut code = t.encode(op).unwrap();
            let n = code.len();
            code.extend(le(&[BX_LR]));
            verify(
                &code,
                &[
                    Segment {
                        start: 0,
                        len: n,
                        contract: c,
                    },
                    Segment {
                        start: n,
                        len: 2,
                        contract: P,
                    },
                ],
            )
        };
        let shl = ArmOp::I64Shl {
            rd_lo: Reg::R4,
            rd_hi: Reg::R5,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        };
        assert!(with(&shl, P).is_err(), "I64Shl chains flags internally");
        assert_eq!(with(&shl, op_flag_contract(&shl)), Ok(()));
        let z = ArmOp::I64SetCondZ {
            rd: Reg::R0,
            rn_lo: Reg::R2,
            rn_hi: Reg::R3,
        };
        assert_eq!(with(&z, op_flag_contract(&z)), Ok(()));
    }
}
