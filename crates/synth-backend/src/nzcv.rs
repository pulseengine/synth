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
//! decoded control-flow graph. Each instruction belongs to the segment of the
//! `ArmOp` that emitted it, and that op's [`FlagContract`] says what its
//! model claims about the flags:
//!
//! * [`FlagContract::Preserves`] (the default for every op not listed in
//!   [`op_flag_contract`]): the model leaves NZCV alone.
//!   - R1: an INCIDENTAL flag write (any write other than a compare-class
//!     `CMP`/`CMN`/`TST`/`TEQ`/`VMRS APSR_nzcv`/`MSR APSR`, a call, or an
//!     undecodable instruction treated as one) must write only DEAD flags,
//!     checked per instruction — this is what catches #709's intra-op shape.
//!   - R2: no flag ANY of the op's instructions may write can be live where
//!     control leaves the op — the op as a whole preserves what it claims to.
//! * [`FlagContract::Scratch`]: the op's expansion uses the flags internally
//!   by design (an `ADDS`→`ADC` carry chain, a `CMP`/`IT` select) but the
//!   model says nothing leaves through them: R2 only.
//! * [`FlagContract::Writes`]: the op's model DEFINES the flags afterwards
//!   (`Cmp`, `Adds`, the explicit flag-setting variants): unchecked here; the
//!   value of those flags is the selector's and the proof's obligation.
//!
//! CONSERVATIVE BY CONSTRUCTION. Every unknown answers in the rejecting
//! direction: an undecodable instruction reads every flag and may write every
//! flag (but kills none); an indirect jump, a branch to a non-instruction
//! offset, or falling off the end leaves every flag live; only a return
//! (`BX LR`, `POP {…, PC}`, `LDM`/`POP.W` with PC) and a trap (`UDF`, `BKPT`)
//! end liveness. A misclassified contract can only make the check stricter:
//! `Preserves` is the default and is the most-checked contract. What this
//! check does NOT show: that the flags a `Writes`/`Scratch` op leaves or
//! consumes have the right VALUES (that is an execution or proof question),
//! and anything about non-Thumb code (A32 is out of scope).

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
    /// The model defines the flags after the op (unchecked).
    Writes,
}

/// The [`FlagContract`] of an op. `Preserves` — the most-checked contract —
/// is the default, so an op missing from this list can only be rejected more
/// often, never checked less.
pub fn op_flag_contract(op: &ArmOp) -> FlagContract {
    use ArmOp::*;
    match op {
        // The model DEFINES the flags: compares, the i64 carry/borrow links,
        // and the explicit flag-setting variants (RQ-91-M0FLAGS).
        Cmp { .. } | Cmn { .. } | Adds { .. } | Subs { .. } => FlagContract::Writes,
        Movs { .. }
        | Mvns { .. }
        | Ands { .. }
        | Orrs { .. }
        | Eors { .. }
        | Lsls { .. }
        | Lsrs { .. }
        | Asrs { .. }
        | Muls { .. } => FlagContract::Writes,
        // The model is silent about flags, and the ENCODER EXPANSION chains
        // them internally by design: `ADDS`/`SUBS` -> `ADC`/`SBC` carries,
        // `SUBS.W ip, rm, #32; BPL` shift-amount splits, `ORRS ip, lo, hi;
        // BEQ` zero-divisor guards, `CMP lo; SBCS hi` compares. A 16-bit/S=1
        // write cannot be told from a deliberate one by its bytes, so these
        // ops are checked by R2 only: no flag they write may be live where
        // control LEAVES them. This list is MEASURED, not guessed: it is
        // exactly the ops whose R1 hits a v7-M corpus run produced
        // (RQ-91-M0FLAGS; every hit an intra-op chain, none crossing an op
        // boundary), plus `I64Add` (the `ADDS`/`ADC` twin of `I64Sub`) and
        // `I64SetCondZ` (the `I64SetCond` twin). None of them is ARMv6-M
        // today: their expansions are refused by the v6-M byte check.
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
        | I64SetCond { .. }
        | I64SetCondZ { .. } => FlagContract::Scratch,
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
    /// Offset of the offending instruction (R1) or of the op's exit (R2).
    pub at: usize,
    /// The instruction's halfwords, hex.
    pub bytes: String,
    /// Flags clobbered while live.
    pub flags: u8,
    /// Offset of an instruction that reads one of those flags, if found.
    pub reader: Option<usize>,
    /// Which rule: "R1" (incidental write of a live flag) or "R2" (a
    /// flag-preserving op clobbers a flag live at its exit).
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
        let what = if self.rule == "R1" {
            "a flag-preserving op's instruction writes"
        } else {
            "a flag-preserving op clobbers"
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
        if let Some(r) = self.reader {
            write!(f, " (read at +0x{r:x})")?;
        }
        Ok(())
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

/// Flag effect of a data-processing opcode (the Thumb-2 `op` field shared by
/// the modified-immediate and shifted-register groups):
/// `(reads, must_write, may_write, producer)`.
fn dp_effect(op: u16, rd: u16, s: bool) -> (u8, u8, u8, bool) {
    let logical = |may_c: bool| (0u8, N | Z, N | Z | if may_c { C } else { 0 });
    let (reads, must, may, producer) = match op {
        0 | 4 if rd == 15 && s => {
            // TST / TEQ
            let (r, m, y) = logical(true);
            (r, m, y, true)
        }
        0..=4 => {
            let (r, m, y) = logical(true);
            (r, m, y, false)
        }
        8 | 13 if rd == 15 && s => (0, NZCV, NZCV, true), // CMN / CMP
        8 | 13 | 14 => (0, NZCV, NZCV, false),            // ADD / SUB / RSB
        10 | 11 => (C, NZCV, NZCV, false),                // ADC / SBC
        _ => (0, 0, 0, false),                            // PKH, undefined
    };
    if s {
        (reads, must, may, producer)
    } else {
        (reads, 0, 0, false)
    }
}

/// Decode one instruction at `off`. `in_it`: inside an IT block (16-bit data
/// processing does not set flags there, and every member is conditional).
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
        flow: Flow::Next,
    };
    // Set an incidental (non-producer) write.
    fn w(i: &mut Insn, must: u8, may: u8, producer: bool) {
        i.must_write |= must;
        i.may_write |= may | must;
        if !producer && (may | must) != 0 {
            i.incidental = true;
        }
    }
    let wide = matches!(hw >> 11, 0b11101..=0b11111);
    if !wide {
        let pc = off as i64 + 4;
        match hw >> 11 {
            // LSL/LSR/ASR #imm (LSL #0 is MOVS rd, rm: C unchanged)
            0b00000..=0b00010 => {
                if !in_it {
                    let imm0 = (hw >> 6) & 0x1F == 0 && hw >> 11 == 0;
                    let c = if imm0 { 0 } else { C };
                    w(&mut i, N | Z | c, 0, false);
                }
            }
            0b00011 => {
                // ADDS/SUBS reg / imm3
                if !in_it {
                    w(&mut i, NZCV, 0, false);
                }
            }
            0b00100 => {
                // MOVS #imm8
                if !in_it {
                    w(&mut i, N | Z, 0, false);
                }
            }
            0b00101 => w(&mut i, NZCV, 0, true), // CMP #imm8: always sets
            0b00110 | 0b00111 => {
                // ADDS/SUBS #imm8
                if !in_it {
                    w(&mut i, NZCV, 0, false);
                }
            }
            0b01000 if hw & 0x0400 == 0 => {
                // 010000 data processing (register)
                let opc = (hw >> 6) & 0xF;
                match opc {
                    0x8 => w(&mut i, N | Z, 0, true),      // TST
                    0xA | 0xB => w(&mut i, NZCV, 0, true), // CMP / CMN
                    _ => {
                        if matches!(opc, 0x5 | 0x6) {
                            i.reads |= C; // ADC / SBC
                        }
                        if !in_it {
                            let (must, may) = match opc {
                                0x0 | 0x1 | 0xC | 0xD | 0xE | 0xF => (N | Z, 0), // AND EOR ORR MUL BIC MVN
                                0x2..=0x4 | 0x7 => (N | Z, C), // shifts by register
                                _ => (NZCV, 0),                // ADC SBC RSB
                            };
                            w(&mut i, must, may, false);
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
                    0 | 2 => {}                    // ADD / MOV high: no flags
                    1 => w(&mut i, NZCV, 0, true), // CMP high
                    _ => {
                        if hw & 0x80 != 0 {
                            // BLX rm: a call clobbers the flags (AAPCS)
                            w(&mut i, NZCV, 0, false);
                        } else if rm == 14 {
                            i.flow = Flow::Return; // BX LR
                        } else {
                            i.flow = Flow::Unknown;
                        }
                    }
                }
            }
            0b01001..=0b10101 => {} // LDR literal, loads/stores, ADR, ADD SP
            0b10110 | 0b10111 => {
                // misc 16-bit
                if hw & 0xF500 == 0xB100 {
                    // CBZ / CBNZ
                    let imm = ((((hw >> 9) & 1) << 6) | (((hw >> 3) & 0x1F) << 1)) as i64;
                    i.flow = Flow::Cond(pc + imm);
                } else if hw & 0xFE00 == 0xBC00 {
                    if hw & 0x0100 != 0 {
                        i.flow = Flow::Return; // POP {.., pc}
                    }
                } else if hw & 0xFF00 == 0xBE00 {
                    i.flow = Flow::Stop; // BKPT
                } else if hw & 0xFF00 == 0xBF00 && hw & 0xF != 0 {
                    i.reads |= cond_reads((hw >> 4) & 0xF); // IT
                }
            }
            0b11000 | 0b11001 => {} // STM / LDM (16-bit LDM cannot load PC)
            0b11010 | 0b11011 => {
                let cond = (hw >> 8) & 0xF;
                match cond {
                    0xE => i.flow = Flow::Stop,       // UDF
                    0xF => w(&mut i, NZCV, 0, false), // SVC: treat as a call
                    _ => {
                        i.reads |= cond_reads(cond);
                        i.flow = Flow::Cond(pc + sext(((hw & 0xFF) as u32) << 1, 9));
                    }
                }
            }
            0b11100 => i.flow = Flow::Jump(pc + sext(((hw & 0x7FF) as u32) << 1, 12)),
            _ => unreachable!("wide prefixes handled below"),
        }
        if in_it && matches!(i.flow, Flow::Jump(_)) {
            // A B inside an IT block is conditional.
            if let Flow::Jump(t) = i.flow {
                i.flow = Flow::Cond(t);
            }
        }
        return Some(i);
    }

    let hw2 = rd16(off + 2)?;
    i.len = 4;
    i.hw = (hw, Some(hw2));
    let pc = off as i64 + 4;
    let unknown = |i: &mut Insn| {
        i.reads = NZCV;
        i.may_write = NZCV;
        i.incidental = true;
    };
    if hw >> 11 == 0b11110 && hw2 & 0x8000 != 0 {
        // branches and miscellaneous control
        let s = ((hw >> 10) & 1) as u32;
        let j1 = ((hw2 >> 13) & 1) as u32;
        let j2 = ((hw2 >> 11) & 1) as u32;
        match hw2 & 0xD000 {
            0xD000 | 0xC000 => w(&mut i, NZCV, 0, false), // BL / BLX: call
            0x9000 => {
                let i1 = 1 ^ (j1 ^ s);
                let i2 = 1 ^ (j2 ^ s);
                let imm = (s << 24)
                    | (i1 << 23)
                    | (i2 << 22)
                    | (((hw & 0x3FF) as u32) << 12)
                    | (((hw2 & 0x7FF) as u32) << 1);
                i.flow = Flow::Jump(pc + sext(imm, 25));
            }
            _ => {
                let cond = (hw >> 6) & 0xF;
                if cond < 0xE {
                    let imm = (s << 20)
                        | (j2 << 19)
                        | (j1 << 18)
                        | (((hw & 0x3F) as u32) << 12)
                        | (((hw2 & 0x7FF) as u32) << 1);
                    i.reads |= cond_reads(cond);
                    i.flow = Flow::Cond(pc + sext(imm, 21));
                } else if hw & 0xFFE0 == 0xF380 {
                    // MSR: writes NZCV when mask<1> (nzcvq) is set
                    if hw2 & 0x0800 != 0 {
                        w(&mut i, NZCV, 0, true);
                    }
                } else if hw & 0xFFE0 == 0xF3E0 {
                    i.reads |= NZCV; // MRS: may read APSR
                } else if hw == 0xF3AF || hw == 0xF3BF {
                    // hints / barriers
                } else {
                    unknown(&mut i);
                }
            }
        }
        if in_it && let Flow::Jump(t) = i.flow {
            i.flow = Flow::Cond(t);
        }
        return Some(i);
    }
    if hw >> 11 == 0b11110 {
        if hw & 0x0200 == 0 {
            // data processing (modified immediate)
            let op = (hw >> 5) & 0xF;
            let s = hw & 0x10 != 0;
            let rd = (hw2 >> 8) & 0xF;
            let (reads, must, mut may, producer) = dp_effect(op, rd, s);
            // ThumbExpandImm_C writes C only for a rotated immediate.
            if op <= 4 {
                let rot = (((hw >> 10) & 1) << 3) | ((hw2 >> 12) & 7);
                if rot < 4 {
                    may &= !C;
                }
            }
            i.reads |= reads;
            w(&mut i, must, may, producer);
        }
        // plain binary immediate (ADDW, MOVW, MOVT, BFI, UBFX, SSAT…): no NZCV
        return Some(i);
    }
    if hw & 0xFE00 == 0xEA00 {
        // data processing (shifted register)
        let op = (hw >> 5) & 0xF;
        let s = hw & 0x10 != 0;
        let rd = (hw2 >> 8) & 0xF;
        let imm = (((hw2 >> 12) & 7) << 2) | ((hw2 >> 6) & 3);
        let ty = (hw2 >> 4) & 3;
        if ty == 3 && imm == 0 {
            i.reads |= C; // RRX reads the carry
        }
        let (reads, must, may, producer) = dp_effect(op, rd, s);
        i.reads |= reads;
        w(&mut i, must, may, producer);
        return Some(i);
    }
    if hw & 0xFF00 == 0xFA00 {
        // data processing (register): shifts by register with S
        if hw & 0x0080 == 0 && hw2 & 0xF0F0 == 0xF000 && hw & 0x10 != 0 {
            w(&mut i, N | Z, C, false);
        }
        return Some(i);
    }
    if hw & 0xFF00 == 0xFB00 {
        return Some(i); // multiply / divide: no NZCV
    }
    if hw & 0xFE40 == 0xE800 {
        // LDM/STM (incl. PUSH.W / POP.W): load with PC in the list returns
        if hw & 0x10 != 0 && hw2 & 0x8000 != 0 {
            i.flow = Flow::Return;
        }
        return Some(i);
    }
    if hw & 0xFE40 == 0xE840 {
        // LDRD/STRD/exclusive; TBB/TBH are indirect jumps
        if hw & 0xFFF0 == 0xE8D0 && hw2 & 0xFFE0 == 0xF000 {
            i.flow = Flow::Unknown;
        }
        return Some(i);
    }
    if hw >> 9 == 0b1111100 {
        // single load/store; a load into PC is an indirect jump
        if hw & 0x10 != 0 && hw2 >> 12 == 0xF && hw & 0x0060 == 0x0040 {
            i.flow = Flow::Unknown;
        }
        return Some(i);
    }
    if hw & 0xEC00 == 0xEC00 {
        // coprocessor / VFP / MVE. VMRS APSR_nzcv, FPSCR writes the flags.
        if hw == 0xEEF1 && hw2 == 0xFA10 {
            w(&mut i, NZCV, 0, true);
        }
        return Some(i);
    }
    unknown(&mut i);
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
/// order; bytes outside every segment (literal pools / islands) are data and
/// are not decoded. See the module doc for the rules.
pub fn verify(code: &[u8], segments: &[Segment]) -> Result<(), NzcvViolation> {
    // 1. Decode, tracking IT state linearly across segments.
    let mut insns: Vec<Insn> = Vec::new();
    let mut it_left = 0u32;
    for (si, seg) in segments.iter().enumerate() {
        let end = seg.start + seg.len;
        let mut off = seg.start;
        while off < end {
            let Some(ins) = decode(code, off, si, it_left > 0) else {
                // Truncated: treat as an unknown 2-byte instruction.
                insns.push(Insn {
                    off,
                    len: end - off,
                    seg: si,
                    hw: (0, None),
                    reads: NZCV,
                    may_write: NZCV,
                    must_write: 0,
                    incidental: true,
                    flow: Flow::Unknown,
                });
                break;
            };
            let was_in_it = it_left > 0;
            let next = off + ins.len;
            let mut ins = ins;
            if was_in_it {
                it_left -= 1;
                // A conditional member may not execute: it kills nothing.
                ins.must_write = 0;
            }
            if ins.len == 2 && ins.hw.0 & 0xFF00 == 0xBF00 && ins.hw.0 & 0xF != 0 {
                it_left = 4 - (ins.hw.0 & 0xF).trailing_zeros();
                // Members read the same flags as the IT's firstcond (the
                // inverse condition reads the same flags).
            }
            insns.push(ins);
            off = next;
        }
    }
    // Members inside an IT block read its condition's flags.
    {
        let mut cond_mask = 0u8;
        let mut left = 0u32;
        for ins in insns.iter_mut() {
            if left > 0 {
                ins.reads |= cond_mask;
                left -= 1;
                continue;
            }
            if ins.len == 2 && ins.hw.0 & 0xFF00 == 0xBF00 && ins.hw.0 & 0xF != 0 {
                cond_mask = cond_reads((ins.hw.0 >> 4) & 0xF);
                left = 4 - (ins.hw.0 & 0xF).trailing_zeros();
            }
        }
    }
    let n = insns.len();
    let idx_of = |t: i64| -> Option<usize> {
        if t < 0 {
            return None;
        }
        insns.binary_search_by_key(&(t as usize), |i| i.off).ok()
    };
    // 2. Successors. `None` in the list = unknown (all flags live).
    let succs: Vec<Vec<Option<usize>>> = (0..n)
        .map(|k| {
            let ins = &insns[k];
            let fall = || {
                let nx = ins.off + ins.len;
                if k + 1 < n && insns[k + 1].off == nx {
                    Some(k + 1)
                } else {
                    None
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
    // 4. R1: incidental writes in flag-preserving ops must be dead.
    for (k, ins) in insns.iter().enumerate() {
        if segments[ins.seg].contract != FlagContract::Preserves || !ins.incidental {
            continue;
        }
        let clobbered = ins.may_write & live_out(&live_in, k);
        if clobbered != 0 {
            return Err(NzcvViolation {
                at: ins.off,
                bytes: hex(ins),
                flags: clobbered,
                reader: find_reader(k, clobbered),
                rule: "R1",
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
        if segments[si].contract == FlagContract::Writes || seg_writes[si] == 0 {
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

    use FlagContract::{Preserves as P, Scratch as S, Writes as W};

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
                Some(vec![0x92, 0x01, 0x11, 0xe0]),
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
            assert_eq!(op_flag_contract(op), FlagContract::Writes, "{op:?}");
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
}
