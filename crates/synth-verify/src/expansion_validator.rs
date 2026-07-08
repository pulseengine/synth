//! Expansion-level certifying validation for the i64 pseudo-ops (#667 move 2).
//!
//! The [`crate::validator_pattern`] validator certifies `(WasmOp, [ArmOp])`
//! selections — but for the i64 *pseudo-ops* (`I64Mul`, the `I64SetCond`
//! family, `I64Clz`/`I64Ctz`/`I64Popcnt`, the i64 shifts and rotates) the
//! `ArmOp` is itself a compound: the **encoder**
//! (`synth-backend/src/arm_encoder.rs::encode_thumb`) expands each into a
//! multi-instruction Thumb-2 sequence (UMULL + MLA cross products, IT-block
//! flag materialisation, CMP/BEQ diamonds, the HAKMEM popcount fold with its
//! scratch push/pop). Modeling the pseudo-op with its reference semantics —
//! what `validator_pattern` does — certifies the register *wiring* but is
//! circular about the expansion itself. The expansion is exactly where the
//! #615 (A32 silent NOP), #632 (popcnt result clobbered by the scratch
//! restore `POP`), and #633 (missing i64 `div_s` overflow guard) miscompiles
//! lived.
//!
//! This module closes that gap for the **branch-free and forward-branch**
//! pseudo-ops: it takes the *literal bytes the shipped encoder emitted*,
//! decodes them with a small Thumb-2 decoder (loud `Err` on anything outside
//! the modeled subset — never a silent skip), symbolically executes the
//! decoded sequence over QF_BV terms (path conditions for forward branches,
//! IT-block predication, a concrete-offset stack model for the scratch
//! push/pop), and discharges
//!
//! ```text
//! UNSAT( wasm_op_semantics(inputs) != sequence_semantics(inputs) )
//! ```
//!
//! through [`crate::solver::BvSolver`] (ordeal by default — every `Unsat`
//! carries an LRAT certificate checked before it is reported; Z3 remains the
//! feature-gated differential oracle).
//!
//! # Covered (validated at the emitted-sequence level)
//!
//! | pseudo-op | expansion shape |
//! |---|---|
//! | `I64Mul` | MUL + MLA cross products + UMULL + ADD (branch-free) |
//! | `I64SetCond` (EQ/NE/LT/LE/GT/GE/LO/LS/HI/HS) | CMP (+IT CMP) / SBCS + ITE + MOV pair |
//! | `I64SetCondZ` (`i64.eqz`) | ORR.W + CMP + ITE + MOV pair |
//! | `I64Clz` / `I64Ctz` | CMP.W + BEQ diamond, CLZ / RBIT+CLZ, +32 arm |
//! | `I64Popcnt` | HAKMEM fold ×2 with PUSH/POP scratch discipline (#632) |
//! | `I64Shl` / `I64ShrU` / `I64ShrS` | small/large split, one BPL diamond |
//! | `I64Rotl` / `I64Rotr` | #610 fixed-ABI wrapper (stack marshaling) + diamond |
//!
//! # Held out, honestly
//!
//! - **`I64DivS` / `I64DivU` / `I64RemS` / `I64RemU`** — the Thumb-2
//!   expansions contain a 64-round binary long-division **loop** (backward
//!   branches). The symbolic executor here is a forward-only DAG executor;
//!   sound validation of the division cores needs bounded loop unrolling (64
//!   iterations of a ~10-instruction body is far past the bit-blasting
//!   budget) or loop-invariant reasoning. The decoder rejects backward
//!   branches with a loud error, so these can never be silently
//!   green-washed. This also means the **#633 missing-overflow-guard shape is
//!   not expressible here yet**: the guard sits inside the div expansion, and
//!   guard/trap equivalence additionally needs UDF-reachability (trap-state)
//!   modeling, not just value-domain equivalence. Documented as future work
//!   in `docs/validator-pattern.md`.
//! - **Trap guards in general** — like `validator_pattern`, this module
//!   certifies value-domain equivalence; trap paths are control flow.
//!
//! # Trusted base
//!
//! The decoder (~25 instruction forms, each a direct transcription of the
//! ARM ARM encoding diagram), the micro-op semantics below, and the solver.
//! The *encoder* — the thing that has actually been wrong (#615/#632/#633) —
//! is **not** trusted: its output bytes are the artifact being checked, so
//! encoder/validator drift is structurally impossible (there is no second
//! hand-maintained copy of the expansion to drift).

#![cfg(feature = "arm")]

use crate::solver::{CheckOutcome, new_solver};
use crate::term::{BV, Bool};
use crate::validator_pattern::{
    Flags, I64Pair, SolverResultKind, bool_to_i32, i64_lt_s, i64_lt_u, i64_rotl, i64_rotr, i64_shl,
    i64_shr_s, i64_shr_u, k32, shift_amount64, sym32,
};
use std::collections::HashMap;
use synth_core::WasmOp;
use synth_synthesis::{ArmOp, Reg};
use thiserror::Error;

/// Witness that an emitted expansion was certified: `Unsat` of the negated
/// equivalence, discharged through the certificate-checked solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpansionWitness {
    /// Human-readable label for the WASM op (e.g. `"I64Mul"`).
    pub wasm_op_label: String,
    /// Number of decoded Thumb-2 instructions in the validated sequence.
    pub instr_count: usize,
    /// Byte length of the emitted sequence.
    pub byte_len: usize,
    /// Always `Unsat` for accepted expansions.
    pub solver_result: SolverResultKind,
}

/// Expansion validation failure reasons. Everything is loud: an instruction
/// or shape outside the modeled subset is an error, never a silent accept.
#[derive(Debug, Error)]
pub enum ExpansionError {
    /// The byte sequence contains an instruction (or branch shape) outside
    /// the decoder's subset. Includes backward branches — loops (the i64
    /// div/rem cores) are *held out*, not silently skipped.
    #[error("expansion decode failed at byte offset {offset}: {reason}")]
    Decode { offset: usize, reason: String },

    /// The `(WasmOp, pseudo ArmOp)` pair is not in the covered surface.
    #[error("expansion validator does not support: {0}")]
    Unsupported(String),

    /// The sequence is semantically wrong — a concrete counterexample input
    /// distinguishes the WASM reference from the emitted sequence.
    #[error("counterexample for {wasm_op_label}: {description}")]
    Counterexample {
        wasm_op_label: String,
        description: String,
    },

    /// Solver returned `unknown` (conflict budget exceeded).
    #[error("solver returned unknown for {0}")]
    SolverUnknown(String),

    /// Internal invariant violation (e.g. malformed IT block).
    #[error("internal expansion-validator error: {0}")]
    Internal(String),
}

// ===========================================================================
// Thumb-2 decoder (subset)
// ===========================================================================

/// Shift kinds for the immediate / register shift forms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShiftKind {
    Lsl,
    Lsr,
    Asr,
}

/// Register-to-register data-processing kinds (T32 shifted-register class,
/// used with shift amount 0 — plain register operands).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DpKind {
    And,
    Orr,
    Add,
    Sub,
    /// SBC with S=1 — the only flag-setting member the expansions use.
    Sbcs,
}

/// Decoded micro-op. Registers are 0..=15 indices.
#[derive(Debug, Clone)]
enum T2Op {
    Nop,
    /// IT/ITE block header: `firstcond` + mask (predicates the next 1..4
    /// instructions).
    It {
        firstcond: u8,
        mask: u8,
    },
    /// CMP (register), both the T1 low-reg and T2 high-reg forms.
    CmpReg {
        rn: u8,
        rm: u8,
    },
    /// CMP (immediate), 16-bit T1 or 32-bit T2 (`rd == PC` marker form).
    CmpImm {
        rn: u8,
        imm: u32,
    },
    /// 16-bit MOVS Rd, #imm8 (flag-setting outside IT blocks).
    MovsImm {
        rd: u8,
        imm: u32,
    },
    /// 32-bit MOV.W Rd, #imm (modified immediate, S=0 — never sets flags).
    MovImm {
        rd: u8,
        imm: u32,
    },
    /// MOV (register), 16-bit high-register form.
    MovReg {
        rd: u8,
        rm: u8,
    },
    /// 16-bit ADD Rdn, Rm (high-register form; does not set flags).
    AddReg16 {
        rdn: u8,
        rm: u8,
    },
    /// 16-bit ADDS Rd, Rn, Rm (T1 — sets NZCV). Only reachable from
    /// deliberately-broken shapes (#632 red test); the shipped expansions
    /// route their final add through ADD.W.
    AddsReg16 {
        rd: u8,
        rn: u8,
        rm: u8,
    },
    /// Conditional branch, resolved to an absolute byte target.
    BCond {
        cc: u8,
        target: i64,
    },
    /// Unconditional branch (T2), absolute byte target.
    B {
        target: i64,
    },
    /// PUSH {list} (bit i set = Ri saved).
    Push {
        list: u16,
    },
    /// POP {list}.
    Pop {
        list: u16,
    },
    /// STR Rt, [SP, #-4]! (the fixed-ABI marshaling store).
    StrPreDec {
        rt: u8,
    },
    /// ADD SP, #imm (discard stack slots).
    AddSpImm {
        imm: u32,
    },
    /// Modified-immediate data processing: AND/ADD/SUB(S)/RSB.
    AndImm {
        rd: u8,
        rn: u8,
        imm: u32,
    },
    AddImm {
        rd: u8,
        rn: u8,
        imm: u32,
    },
    /// SUBS.W Rd, Rn, #imm (S=1 — sets NZCV like CMP).
    SubsImm {
        rd: u8,
        rn: u8,
        imm: u32,
    },
    RsbImm {
        rd: u8,
        rn: u8,
        imm: u32,
    },
    /// MOVW: Rd = imm16 (zero-extended).
    MovwImm {
        rd: u8,
        imm16: u32,
    },
    /// MOVT: Rd[31:16] = imm16.
    MovtImm {
        rd: u8,
        imm16: u32,
    },
    /// Register-register data processing (shift amount 0).
    DpReg {
        kind: DpKind,
        rd: u8,
        rn: u8,
        rm: u8,
    },
    /// Immediate shift (T32 MOV-shifted-register form).
    ShiftImm {
        kind: ShiftKind,
        rd: u8,
        rm: u8,
        imm: u32,
    },
    /// Register shift (LSL.W/LSR.W/ASR.W Rd, Rn, Rm).
    ShiftReg {
        kind: ShiftKind,
        rd: u8,
        rn: u8,
        rm: u8,
    },
    Mul {
        rd: u8,
        rn: u8,
        rm: u8,
    },
    Mla {
        rd: u8,
        rn: u8,
        rm: u8,
        ra: u8,
    },
    Umull {
        rdlo: u8,
        rdhi: u8,
        rn: u8,
        rm: u8,
    },
    Clz {
        rd: u8,
        rm: u8,
    },
    Rbit {
        rd: u8,
        rm: u8,
    },
}

/// A decoded instruction with its byte offset and length.
#[derive(Debug, Clone)]
struct Decoded {
    offset: usize,
    len: usize,
    op: T2Op,
}

fn derr<T>(offset: usize, reason: impl Into<String>) -> Result<T, ExpansionError> {
    Err(ExpansionError::Decode {
        offset,
        reason: reason.into(),
    })
}

/// ThumbExpandImm for the subset the expansions use: `i:imm3:imm8` with the
/// top four bits zero (plain 0..=255 immediates). Anything else is a loud
/// decode error.
fn thumb_expand_imm(offset: usize, i: u32, imm3: u32, imm8: u32) -> Result<u32, ExpansionError> {
    let imm12 = (i << 11) | (imm3 << 8) | imm8;
    if imm12 & 0xF00 == 0 {
        Ok(imm8)
    } else {
        derr(
            offset,
            format!("modified immediate 0x{imm12:03x} outside the plain-imm8 subset"),
        )
    }
}

/// Decode a Thumb-2 byte sequence into micro-ops. Anything outside the
/// modeled subset is a loud error.
fn decode_thumb2(code: &[u8]) -> Result<Vec<Decoded>, ExpansionError> {
    if !code.len().is_multiple_of(2) {
        return derr(0, "odd byte length");
    }
    let mut out = Vec::new();
    let mut o = 0usize;
    while o < code.len() {
        let hw1 = u16::from_le_bytes([code[o], code[o + 1]]);
        // 32-bit encodings: top 5 bits 11101 / 11110 / 11111.
        let is32 = (hw1 & 0xE000) == 0xE000 && (hw1 & 0x1800) != 0;
        if !is32 {
            let op = decode16(o, hw1)?;
            out.push(Decoded {
                offset: o,
                len: 2,
                op,
            });
            o += 2;
        } else {
            if o + 4 > code.len() {
                return derr(o, "truncated 32-bit instruction");
            }
            let hw2 = u16::from_le_bytes([code[o + 2], code[o + 3]]);
            let op = decode32(o, hw1, hw2)?;
            out.push(Decoded {
                offset: o,
                len: 4,
                op,
            });
            o += 4;
        }
    }
    Ok(out)
}

fn decode16(o: usize, hw: u16) -> Result<T2Op, ExpansionError> {
    if hw == 0xBF00 {
        return Ok(T2Op::Nop);
    }
    if hw & 0xFF00 == 0xBF00 {
        return Ok(T2Op::It {
            firstcond: ((hw >> 4) & 0xF) as u8,
            mask: (hw & 0xF) as u8,
        });
    }
    if hw & 0xFFC0 == 0x4280 {
        return Ok(T2Op::CmpReg {
            rn: (hw & 7) as u8,
            rm: ((hw >> 3) & 7) as u8,
        });
    }
    if hw & 0xFF00 == 0x4500 {
        return Ok(T2Op::CmpReg {
            rn: ((((hw >> 7) & 1) << 3) | (hw & 7)) as u8,
            rm: ((hw >> 3) & 0xF) as u8,
        });
    }
    if hw & 0xF800 == 0x2800 {
        return Ok(T2Op::CmpImm {
            rn: ((hw >> 8) & 7) as u8,
            imm: (hw & 0xFF) as u32,
        });
    }
    if hw & 0xF800 == 0x2000 {
        return Ok(T2Op::MovsImm {
            rd: ((hw >> 8) & 7) as u8,
            imm: (hw & 0xFF) as u32,
        });
    }
    if hw & 0xFF00 == 0x4600 {
        return Ok(T2Op::MovReg {
            rd: ((((hw >> 7) & 1) << 3) | (hw & 7)) as u8,
            rm: ((hw >> 3) & 0xF) as u8,
        });
    }
    if hw & 0xFF00 == 0x4400 {
        return Ok(T2Op::AddReg16 {
            rdn: ((((hw >> 7) & 1) << 3) | (hw & 7)) as u8,
            rm: ((hw >> 3) & 0xF) as u8,
        });
    }
    if hw & 0xFE00 == 0x1800 {
        return Ok(T2Op::AddsReg16 {
            rd: (hw & 7) as u8,
            rn: ((hw >> 3) & 7) as u8,
            rm: ((hw >> 6) & 7) as u8,
        });
    }
    if hw & 0xF000 == 0xD000 {
        let cc = ((hw >> 8) & 0xF) as u8;
        if cc >= 0xE {
            return derr(o, format!("conditional branch with cc={cc:#x}"));
        }
        let imm8 = (hw & 0xFF) as i64;
        let simm = if imm8 >= 0x80 { imm8 - 0x100 } else { imm8 };
        return Ok(T2Op::BCond {
            cc,
            target: o as i64 + 4 + 2 * simm,
        });
    }
    if hw & 0xF800 == 0xE000 {
        let imm11 = (hw & 0x7FF) as i64;
        let simm = if imm11 >= 0x400 { imm11 - 0x800 } else { imm11 };
        return Ok(T2Op::B {
            target: o as i64 + 4 + 2 * simm,
        });
    }
    if hw & 0xFE00 == 0xB400 {
        if hw & 0x0100 != 0 {
            return derr(o, "PUSH with LR outside the modeled subset");
        }
        return Ok(T2Op::Push { list: hw & 0xFF });
    }
    if hw & 0xFE00 == 0xBC00 {
        if hw & 0x0100 != 0 {
            return derr(o, "POP with PC outside the modeled subset");
        }
        return Ok(T2Op::Pop { list: hw & 0xFF });
    }
    if hw & 0xFF80 == 0xB000 {
        return Ok(T2Op::AddSpImm {
            imm: ((hw & 0x7F) as u32) * 4,
        });
    }
    derr(
        o,
        format!("16-bit instruction {hw:#06x} outside the modeled subset"),
    )
}

fn decode32(o: usize, hw1: u16, hw2: u16) -> Result<T2Op, ExpansionError> {
    let hw1 = hw1 as u32;
    let hw2 = hw2 as u32;

    // STR Rt, [SP, #-4]! — the fixed-ABI marshaling store.
    if hw1 == 0xF84D && hw2 & 0x0FFF == 0x0D04 {
        return Ok(T2Op::StrPreDec {
            rt: ((hw2 >> 12) & 0xF) as u8,
        });
    }

    // CLZ / RBIT (before the shifted-register class; distinct hw1 space).
    if hw1 & 0xFFF0 == 0xFAB0 && hw2 & 0xF0F0 == 0xF080 {
        return Ok(T2Op::Clz {
            rd: ((hw2 >> 8) & 0xF) as u8,
            rm: (hw2 & 0xF) as u8,
        });
    }
    if hw1 & 0xFFF0 == 0xFA90 && hw2 & 0xF0F0 == 0xF0A0 {
        return Ok(T2Op::Rbit {
            rd: ((hw2 >> 8) & 0xF) as u8,
            rm: (hw2 & 0xF) as u8,
        });
    }

    // Register shifts: LSL.W / LSR.W / ASR.W Rd, Rn, Rm.
    if hw1 & 0xFF80 == 0xFA00 && hw2 & 0xF0F0 == 0xF000 {
        let kind = match (hw1 >> 5) & 3 {
            0 => ShiftKind::Lsl,
            1 => ShiftKind::Lsr,
            2 => ShiftKind::Asr,
            _ => return derr(o, "ROR.W (register) outside the modeled subset"),
        };
        return Ok(T2Op::ShiftReg {
            kind,
            rd: ((hw2 >> 8) & 0xF) as u8,
            rn: (hw1 & 0xF) as u8,
            rm: (hw2 & 0xF) as u8,
        });
    }

    // MUL / MLA.
    if hw1 & 0xFFF0 == 0xFB00 && hw2 & 0x00F0 == 0x0000 {
        let ra = ((hw2 >> 12) & 0xF) as u8;
        let rd = ((hw2 >> 8) & 0xF) as u8;
        let rn = (hw1 & 0xF) as u8;
        let rm = (hw2 & 0xF) as u8;
        return Ok(if ra == 0xF {
            T2Op::Mul { rd, rn, rm }
        } else {
            T2Op::Mla { rd, rn, rm, ra }
        });
    }

    // UMULL.
    if hw1 & 0xFFF0 == 0xFBA0 && hw2 & 0x00F0 == 0x0000 {
        return Ok(T2Op::Umull {
            rdlo: ((hw2 >> 12) & 0xF) as u8,
            rdhi: ((hw2 >> 8) & 0xF) as u8,
            rn: (hw1 & 0xF) as u8,
            rm: (hw2 & 0xF) as u8,
        });
    }

    // MOVW / MOVT (checked before the modified-immediate class; they have
    // hw1 bit 9 set, which the DP-modified-imm mask excludes).
    if hw1 & 0xFBF0 == 0xF240 || hw1 & 0xFBF0 == 0xF2C0 {
        let i = (hw1 >> 10) & 1;
        let imm4 = hw1 & 0xF;
        let imm3 = (hw2 >> 12) & 7;
        let rd = ((hw2 >> 8) & 0xF) as u8;
        let imm8 = hw2 & 0xFF;
        let imm16 = (imm4 << 12) | (i << 11) | (imm3 << 8) | imm8;
        return Ok(if hw1 & 0xFBF0 == 0xF240 {
            T2Op::MovwImm { rd, imm16 }
        } else {
            T2Op::MovtImm { rd, imm16 }
        });
    }

    // Data processing, modified immediate.
    if hw1 & 0xFA00 == 0xF000 && hw2 & 0x8000 == 0 {
        let i = (hw1 >> 10) & 1;
        let op = (hw1 >> 5) & 0xF;
        let s = (hw1 >> 4) & 1;
        let rn = (hw1 & 0xF) as u8;
        let imm3 = (hw2 >> 12) & 7;
        let rd = ((hw2 >> 8) & 0xF) as u8;
        let imm8 = hw2 & 0xFF;
        let imm = thumb_expand_imm(o, i, imm3, imm8)?;
        return match (op, s) {
            (0b0000, 0) => Ok(T2Op::AndImm { rd, rn, imm }),
            (0b0010, 0) if rn == 0xF => Ok(T2Op::MovImm { rd, imm }),
            (0b1000, 0) => Ok(T2Op::AddImm { rd, rn, imm }),
            (0b1101, 1) if rd == 0xF => Ok(T2Op::CmpImm { rn, imm }),
            (0b1101, 1) => Ok(T2Op::SubsImm { rd, rn, imm }),
            (0b1110, 0) => Ok(T2Op::RsbImm { rd, rn, imm }),
            _ => derr(
                o,
                format!("modified-immediate DP op={op:#06b} S={s} outside the modeled subset"),
            ),
        };
    }

    // Data processing, shifted register (used with shift amount 0), plus the
    // MOV-shifted-register immediate-shift form (rn == PC, op == ORR).
    if hw1 & 0xFE00 == 0xEA00 {
        let op = (hw1 >> 5) & 0xF;
        let s = (hw1 >> 4) & 1;
        let rn = (hw1 & 0xF) as u8;
        let imm3 = (hw2 >> 12) & 7;
        let rd = ((hw2 >> 8) & 0xF) as u8;
        let imm2 = (hw2 >> 6) & 3;
        let ty = (hw2 >> 4) & 3;
        let rm = (hw2 & 0xF) as u8;
        let imm5 = (imm3 << 2) | imm2;

        if rn == 0xF && op == 0b0010 && s == 0 {
            // MOV (shifted register): LSL/LSR/ASR immediate.
            let kind = match ty {
                0 if imm5 == 0 => return Ok(T2Op::MovReg { rd, rm }),
                0 => ShiftKind::Lsl,
                1 => ShiftKind::Lsr,
                2 => ShiftKind::Asr,
                _ => return derr(o, "ROR-immediate outside the modeled subset"),
            };
            if imm5 == 0 {
                return derr(
                    o,
                    "shift-by-32 encoding (imm5=0) outside the modeled subset",
                );
            }
            return Ok(T2Op::ShiftImm {
                kind,
                rd,
                rm,
                imm: imm5,
            });
        }

        if imm5 != 0 || ty != 0 {
            return derr(
                o,
                format!(
                    "shifted-register operand (type={ty}, imm5={imm5}) outside the modeled subset"
                ),
            );
        }
        let kind = match (op, s) {
            (0b0000, 0) => DpKind::And,
            (0b0010, 0) => DpKind::Orr,
            (0b1000, 0) => DpKind::Add,
            (0b1101, 0) => DpKind::Sub,
            (0b1011, 1) => DpKind::Sbcs,
            _ => {
                return derr(
                    o,
                    format!("register DP op={op:#06b} S={s} outside the modeled subset"),
                );
            }
        };
        return Ok(T2Op::DpReg { kind, rd, rn, rm });
    }

    derr(
        o,
        format!("32-bit instruction {hw1:#06x} {hw2:#06x} outside the modeled subset"),
    )
}

// ===========================================================================
// Symbolic executor (forward-branch DAG, IT predication, concrete stack)
// ===========================================================================

/// Boolean if-then-else (the term API only has BV ite).
fn bool_ite(c: &Bool, t: &Bool, e: &Bool) -> Bool {
    Bool::or(&[&Bool::and(&[c, t]), &Bool::and(&[&c.not(), e])])
}

/// Evaluate a 4-bit ARM condition code against the flags.
fn cc_holds(cc: u8, f: &Flags) -> Result<Bool, ExpansionError> {
    Ok(match cc {
        0x0 => f.z.clone(),                             // EQ
        0x1 => f.z.not(),                               // NE
        0x2 => f.c.clone(),                             // HS/CS
        0x3 => f.c.not(),                               // LO/CC
        0x4 => f.n.clone(),                             // MI
        0x5 => f.n.not(),                               // PL
        0x6 => f.v.clone(),                             // VS
        0x7 => f.v.not(),                               // VC
        0x8 => Bool::and(&[&f.c, &f.z.not()]),          // HI
        0x9 => Bool::or(&[&f.c.not(), &f.z]),           // LS
        0xA => f.n.eq(&f.v),                            // GE
        0xB => f.n.eq(&f.v).not(),                      // LT
        0xC => Bool::and(&[&f.z.not(), &f.n.eq(&f.v)]), // GT
        0xD => Bool::or(&[&f.z, &f.n.eq(&f.v).not()]),  // LE
        _ => {
            return Err(ExpansionError::Internal(format!(
                "condition code {cc:#x} is not evaluatable"
            )));
        }
    })
}

/// CLZ as a QF_BV expression: leading-zero count of a 32-bit value.
fn clz32(x: &BV) -> BV {
    // Fold from the MSB: the first set bit at position i gives 31 - i.
    let mut r = k32(32);
    for i in 0..32u32 {
        // i ascending: bit 0 checked last ⇒ outermost ite is bit 31.
        let bit = x.extract(i, i).eq(BV::from_i64(1, 1));
        r = bit.ite(k32((31 - i) as i64), &r);
    }
    r
}

/// CTZ as a QF_BV expression: trailing-zero count (the WASM reference — the
/// ARM side computes CLZ(RBIT(x)) instead, so the two encodings are
/// independent).
fn ctz32(x: &BV) -> BV {
    let mut r = k32(32);
    for i in (0..32u32).rev() {
        // i descending: bit 31 checked last ⇒ outermost ite is bit 0.
        let bit = x.extract(i, i).eq(BV::from_i64(1, 1));
        r = bit.ite(k32(i as i64), &r);
    }
    r
}

/// POPCNT as a QF_BV expression: the sum of the 32 bits (the textbook truth,
/// used to PIN the HAKMEM reference — see [`popcnt32_hakmem`]; test-only by
/// construction, the runtime queries go through the pinned HAKMEM form).
#[cfg(test)]
fn popcnt32(x: &BV) -> BV {
    let mut acc = k32(0);
    for i in 0..32u32 {
        acc = acc.bvadd(x.extract(i, i).zero_ext(31));
    }
    acc
}

/// The HAKMEM parallel-count fold — the algorithm the shipped `I64Popcnt`
/// expansion implements per word.
///
/// Used as the sequence-side reference in a two-link proof chain:
///
/// 1. `popcnt_hakmem_formula_is_popcnt` (unit test below) proves
///    `∀w. popcnt32_hakmem(w) == popcnt32(w)` symbolically (~7 s).
/// 2. `validate_expansion(I64Popcnt, …)` proves the emitted sequence equals
///    `popcnt32_hakmem(a_lo) + popcnt32_hakmem(a_hi)` — a structural query
///    (the reference's multiply/mask atoms match the instructions'
///    semantics), which discharges the routing/clobber correctness that
///    #632 was about.
///
/// Transitivity gives `sequence == bit-sum popcount`. The direct one-link
/// query (sequence vs the bit-sum over both words) is NOT used: it couples
/// two multiplier folds against 64 single-bit adders and does not converge
/// within any practical conflict budget (measured: > 570 s), while both
/// links above are seconds.
fn popcnt32_hakmem(x: &BV) -> BV {
    let m1 = k32(0x5555_5555);
    let m2 = k32(0x3333_3333);
    let m4 = k32(0x0F0F_0F0F);
    let x1 = x.bvsub(x.bvlshr(k32(1)).bvand(&m1));
    let x2 = x1.bvand(&m2).bvadd(x1.bvlshr(k32(2)).bvand(&m2));
    let x3 = x2.bvadd(x2.bvlshr(k32(4))).bvand(&m4);
    x3.bvmul(k32(0x0101_0101)).bvlshr(k32(24))
}

/// The textbook 32-bit-limb (schoolbook) form of `i64.mul`:
///
/// ```text
/// full  = zext64(a_lo) * zext64(b_lo)      (the exact 32×32→64 product)
/// lo    = full[31:0]
/// hi    = full[63:32] + a_lo*b_hi + a_hi*b_lo   (cross terms, mod 2^32)
/// ```
///
/// `validator_pattern`'s reference uses the native 64-bit `bvmul` on the
/// joined limbs. That form is used here deliberately NOT: proving the 64-bit
/// `bvmul` equal to the UMULL/MUL/MLA sequence makes the solver reason about
/// two *structurally different* multiplier circuits, which bit-blasts past
/// any practical budget (measured: no convergence in 400 s — the same
/// tractability line as the documented i32 `rem_s` MLS scope-out). The
/// schoolbook form's multiply atoms (`zext(a_lo)*zext(b_lo)`, `a_lo*b_hi`,
/// `a_hi*b_lo`) structurally match the instructions' semantics, so the query
/// discharges the *routing and accumulation* of the expansion — exactly the
/// #615/#632 bug classes — in milliseconds. The schoolbook↔`bvmul` identity
/// itself is pinned by exhaustive-edge concrete tests below
/// (`schoolbook_mul_matches_u64_mul`).
fn i64_mul_schoolbook(a: &I64Pair, b: &I64Pair) -> I64Pair {
    let full = a.lo.zero_ext(32).bvmul(b.lo.zero_ext(32));
    let lo = full.extract(31, 0);
    let hi = full
        .extract(63, 32)
        .bvadd(a.lo.bvmul(&b.hi))
        .bvadd(a.hi.bvmul(&b.lo));
    I64Pair { lo, hi }
}

/// RBIT: bit reversal, by concatenating the bits LSB-first.
fn rbit32(x: &BV) -> BV {
    let mut r = x.extract(0, 0);
    for i in 1..32u32 {
        r = r.concat(x.extract(i, i));
    }
    r
}

/// The machine state threaded through the guarded execution.
struct MachineState {
    regs: Vec<BV>,
    flags: Flags,
    /// Stack memory at concrete offsets from the entry SP (which is 0).
    mem: HashMap<i64, BV>,
    sp_off: i64,
    fresh: usize,
}

impl MachineState {
    fn new() -> Self {
        Self {
            regs: (0..16).map(|i| sym32(&format!("init_r{i}"))).collect(),
            flags: Flags::unconstrained(),
            mem: HashMap::new(),
            sp_off: 0,
            fresh: 0,
        }
    }

    fn fresh32(&mut self, label: &str) -> BV {
        self.fresh += 1;
        sym32(&format!("fresh_{label}_{}", self.fresh))
    }

    /// Guarded register write.
    fn set_reg(&mut self, g: &Bool, rd: u8, v: BV) -> Result<(), ExpansionError> {
        let rd = rd as usize;
        if rd == 13 || rd == 15 {
            return Err(ExpansionError::Internal(
                "direct SP/PC register write outside the modeled subset".into(),
            ));
        }
        self.regs[rd] = g.ite(&v, &self.regs[rd]);
        Ok(())
    }

    fn get_reg(&self, r: u8) -> Result<BV, ExpansionError> {
        let r = r as usize;
        if r == 13 || r == 15 {
            return Err(ExpansionError::Internal(
                "direct SP/PC register read outside the modeled subset".into(),
            ));
        }
        Ok(self.regs[r].clone())
    }

    /// Guarded flag update.
    fn set_flags(&mut self, g: &Bool, new: Flags) {
        self.flags = Flags {
            n: bool_ite(g, &new.n, &self.flags.n),
            z: bool_ite(g, &new.z, &self.flags.z),
            c: bool_ite(g, &new.c, &self.flags.c),
            v: bool_ite(g, &new.v, &self.flags.v),
        };
    }

    fn mem_read(&mut self, addr: i64) -> BV {
        if let Some(v) = self.mem.get(&addr) {
            return v.clone();
        }
        // Unwritten stack slot: unconstrained garbage (exactly what a POP of
        // a never-pushed slot yields on hardware).
        let v = self.fresh32("stack");
        self.mem.insert(addr, v.clone());
        v
    }

    fn mem_write(&mut self, g: &Bool, addr: i64, v: BV) {
        let old = self.mem_read(addr);
        self.mem.insert(addr, g.ite(&v, &old));
    }
}

/// Flags for ADDS (rd = rn + rm).
fn flags_from_adds(rn: &BV, rm: &BV, result: &BV) -> Flags {
    let n = result.bvslt(k32(0));
    let z = result.eq(k32(0));
    let c = result.bvult(rn); // unsigned wrap ⇒ carry out
    let rn_neg = rn.bvslt(k32(0));
    let rm_neg = rm.bvslt(k32(0));
    let r_neg = result.bvslt(k32(0));
    let v = Bool::and(&[&rn_neg.eq(&rm_neg), &r_neg.eq(&rn_neg).not()]);
    Flags { n, z, c, v }
}

/// SBCS: rd = rn - rm - (1 - C_in), full NZCV via 33-bit arithmetic.
fn exec_sbcs(rn: &BV, rm: &BV, c_in: &Bool) -> (BV, Flags) {
    let one33 = BV::from_i64(1, 33);
    let zero33 = BV::from_i64(0, 33);
    let borrow = c_in.ite(&zero33, &one33);
    let u = rn.zero_ext(1).bvsub(rm.zero_ext(1)).bvsub(&borrow);
    let result = u.extract(31, 0);
    let c = u.extract(32, 32).eq(BV::from_i64(0, 1)); // no borrow
    let s = rn.sign_ext(1).bvsub(rm.sign_ext(1)).bvsub(&borrow);
    let v = s.extract(32, 32).eq(s.extract(31, 31)).not();
    let n = result.bvslt(k32(0));
    let z = result.eq(k32(0));
    (result, Flags { n, z, c, v })
}

/// Symbolically execute a decoded forward-branch-only sequence.
///
/// Guarded (if-converted) execution over the address-ordered instruction
/// list: every instruction carries the disjunction of the path conditions
/// that reach it, register/flag/memory effects are predicated on that guard,
/// and branches route guards forward. Backward branches were already
/// rejected by the caller. This is sound for DAG control flow because on any
/// concrete input exactly the guard-true instructions execute, in address
/// order.
fn execute(instrs: &[Decoded], state: &mut MachineState) -> Result<(), ExpansionError> {
    let total_len = instrs.last().map(|d| d.offset + d.len).unwrap_or(0);

    let mut incoming: HashMap<usize, Bool> = HashMap::new();
    incoming.insert(0, Bool::from_bool(true));
    // Open forward-branch join points: while any is ahead of the cursor we
    // are inside a conditional region (SP discipline is enforced there).
    let mut pending_joins: Vec<usize> = Vec::new();
    // IT block: remaining condition codes for the next predicated instrs.
    let mut it_queue: Vec<u8> = Vec::new();

    let merge = |incoming: &mut HashMap<usize, Bool>, at: usize, g: Bool| {
        let cur = incoming
            .get(&at)
            .cloned()
            .unwrap_or_else(|| Bool::from_bool(false));
        incoming.insert(at, Bool::or(&[&cur, &g]));
    };

    for d in instrs {
        let o = d.offset;
        pending_joins.retain(|&j| j > o);
        let g = incoming
            .get(&o)
            .cloned()
            .unwrap_or_else(|| Bool::from_bool(false));
        let in_it = !it_queue.is_empty();
        // Effective guard: path condition ∧ IT predicate (if predicated).
        let eff = if in_it {
            let cc = it_queue.remove(0);
            let c = cc_holds(cc, &state.flags)?;
            Bool::and(&[&g, &c])
        } else {
            g.clone()
        };
        let next = o + d.len;
        let in_cond_region = !pending_joins.is_empty();

        // Control flow falls through for everything except unconditional B.
        let mut fallthrough = true;

        match &d.op {
            T2Op::Nop => {}
            T2Op::It { firstcond, mask } => {
                if in_it {
                    return Err(ExpansionError::Internal("nested IT block".into()));
                }
                if *mask == 0 {
                    return Err(ExpansionError::Internal("IT with empty mask".into()));
                }
                // ITSTATE advance: entry j has cond = firstcond[3:1] : bit_j,
                // where bit_0 = firstcond[0] and bit_{j>0} = mask[3-(j-1)].
                let count = 4 - mask.trailing_zeros() as usize;
                let base = firstcond & 0xE;
                it_queue.push(*firstcond);
                for j in 1..count {
                    let bit = (mask >> (3 - (j - 1))) & 1;
                    it_queue.push(base | bit);
                }
            }
            T2Op::CmpReg { rn, rm } => {
                let a = state.get_reg(*rn)?;
                let b = state.get_reg(*rm)?;
                let f = Flags::from_cmp(&a, &b);
                state.set_flags(&eff, f);
            }
            T2Op::CmpImm { rn, imm } => {
                let a = state.get_reg(*rn)?;
                let f = Flags::from_cmp(&a, &k32(*imm as i64));
                state.set_flags(&eff, f);
            }
            T2Op::MovsImm { rd, imm } => {
                let v = k32(*imm as i64);
                if !in_it {
                    // MOVS sets N and Z (C/V unchanged).
                    let f = Flags {
                        n: v.bvslt(k32(0)),
                        z: v.eq(k32(0)),
                        c: state.flags.c.clone(),
                        v: state.flags.v.clone(),
                    };
                    state.set_flags(&eff, f);
                }
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::MovImm { rd, imm } => {
                state.set_reg(&eff, *rd, k32(*imm as i64))?;
            }
            T2Op::MovReg { rd, rm } => {
                let v = state.get_reg(*rm)?;
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::AddReg16 { rdn, rm } => {
                let v = state.get_reg(*rdn)?.bvadd(&state.get_reg(*rm)?);
                state.set_reg(&eff, *rdn, v)?;
            }
            T2Op::AddsReg16 { rd, rn, rm } => {
                let a = state.get_reg(*rn)?;
                let b = state.get_reg(*rm)?;
                let v = a.bvadd(&b);
                if !in_it {
                    let f = flags_from_adds(&a, &b, &v);
                    state.set_flags(&eff, f);
                }
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::BCond { cc, target } => {
                if in_it {
                    return Err(ExpansionError::Internal("branch inside IT block".into()));
                }
                if *target <= o as i64 {
                    return Err(ExpansionError::Decode {
                        offset: o,
                        reason: "backward branch (loop) — held out, needs loop unrolling"
                            .to_string(),
                    });
                }
                let t = *target as usize;
                if t > total_len {
                    return derr(o, "branch target beyond sequence end");
                }
                let c = cc_holds(*cc, &state.flags)?;
                merge(&mut incoming, t, Bool::and(&[&eff, &c]));
                merge(&mut incoming, next, Bool::and(&[&eff, &c.not()]));
                pending_joins.push(t);
                fallthrough = false; // already merged the fall-through edge
            }
            T2Op::B { target } => {
                if in_it {
                    return Err(ExpansionError::Internal("branch inside IT block".into()));
                }
                if *target <= o as i64 {
                    return Err(ExpansionError::Decode {
                        offset: o,
                        reason: "backward branch (loop) — held out, needs loop unrolling"
                            .to_string(),
                    });
                }
                let t = *target as usize;
                if t > total_len {
                    return derr(o, "branch target beyond sequence end");
                }
                merge(&mut incoming, t, eff.clone());
                pending_joins.push(t);
                fallthrough = false;
            }
            T2Op::Push { list } => {
                if in_cond_region {
                    return Err(ExpansionError::Internal(
                        "PUSH inside a conditional region — SP discipline unmodeled".into(),
                    ));
                }
                let n = list.count_ones() as i64;
                state.sp_off -= 4 * n;
                let mut slot = 0i64;
                for r in 0..8u8 {
                    if list & (1 << r) != 0 {
                        let v = state.get_reg(r)?;
                        let addr = state.sp_off + 4 * slot;
                        state.mem_write(&eff, addr, v);
                        slot += 1;
                    }
                }
            }
            T2Op::Pop { list } => {
                if in_cond_region {
                    return Err(ExpansionError::Internal(
                        "POP inside a conditional region — SP discipline unmodeled".into(),
                    ));
                }
                let mut slot = 0i64;
                for r in 0..8u8 {
                    if list & (1 << r) != 0 {
                        let addr = state.sp_off + 4 * slot;
                        let v = state.mem_read(addr);
                        state.set_reg(&eff, r, v)?;
                        slot += 1;
                    }
                }
                state.sp_off += 4 * slot;
            }
            T2Op::StrPreDec { rt } => {
                if in_cond_region {
                    return Err(ExpansionError::Internal(
                        "STR [SP,#-4]! inside a conditional region — SP discipline unmodeled"
                            .into(),
                    ));
                }
                state.sp_off -= 4;
                let v = state.get_reg(*rt)?;
                let addr = state.sp_off;
                state.mem_write(&eff, addr, v);
            }
            T2Op::AddSpImm { imm } => {
                if in_cond_region {
                    return Err(ExpansionError::Internal(
                        "ADD SP inside a conditional region — SP discipline unmodeled".into(),
                    ));
                }
                state.sp_off += *imm as i64;
            }
            T2Op::AndImm { rd, rn, imm } => {
                let v = state.get_reg(*rn)?.bvand(k32(*imm as i64));
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::AddImm { rd, rn, imm } => {
                let v = state.get_reg(*rn)?.bvadd(k32(*imm as i64));
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::SubsImm { rd, rn, imm } => {
                let a = state.get_reg(*rn)?;
                let b = k32(*imm as i64);
                let f = Flags::from_cmp(&a, &b);
                state.set_flags(&eff, f);
                state.set_reg(&eff, *rd, a.bvsub(&b))?;
            }
            T2Op::RsbImm { rd, rn, imm } => {
                let v = k32(*imm as i64).bvsub(&state.get_reg(*rn)?);
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::MovwImm { rd, imm16 } => {
                state.set_reg(&eff, *rd, k32(*imm16 as i64))?;
            }
            T2Op::MovtImm { rd, imm16 } => {
                let low = state.get_reg(*rd)?.bvand(k32(0xFFFF));
                let v = low.bvor(k32(((*imm16 as i64) << 16) & 0xFFFF_FFFF));
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::DpReg { kind, rd, rn, rm } => {
                let a = state.get_reg(*rn)?;
                let b = state.get_reg(*rm)?;
                match kind {
                    DpKind::And => state.set_reg(&eff, *rd, a.bvand(&b))?,
                    DpKind::Orr => state.set_reg(&eff, *rd, a.bvor(&b))?,
                    DpKind::Add => state.set_reg(&eff, *rd, a.bvadd(&b))?,
                    DpKind::Sub => state.set_reg(&eff, *rd, a.bvsub(&b))?,
                    DpKind::Sbcs => {
                        let (v, f) = exec_sbcs(&a, &b, &state.flags.c);
                        state.set_flags(&eff, f);
                        state.set_reg(&eff, *rd, v)?;
                    }
                }
            }
            T2Op::ShiftImm { kind, rd, rm, imm } => {
                let a = state.get_reg(*rm)?;
                let s = k32(*imm as i64);
                let v = match kind {
                    ShiftKind::Lsl => a.bvshl(&s),
                    ShiftKind::Lsr => a.bvlshr(&s),
                    ShiftKind::Asr => a.bvashr(&s),
                };
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::ShiftReg { kind, rd, rn, rm } => {
                let a = state.get_reg(*rn)?;
                // ARM register shifts use the low byte of Rm; amounts >= 32
                // saturate (0 for LSL/LSR, sign-fill for ASR) — exactly the
                // SMT bvshl/bvlshr/bvashr semantics once masked to 8 bits.
                let s = state.get_reg(*rm)?.bvand(k32(0xFF));
                let v = match kind {
                    ShiftKind::Lsl => a.bvshl(&s),
                    ShiftKind::Lsr => a.bvlshr(&s),
                    ShiftKind::Asr => a.bvashr(&s),
                };
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::Mul { rd, rn, rm } => {
                let v = state.get_reg(*rn)?.bvmul(&state.get_reg(*rm)?);
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::Mla { rd, rn, rm, ra } => {
                let v = state
                    .get_reg(*ra)?
                    .bvadd(state.get_reg(*rn)?.bvmul(&state.get_reg(*rm)?));
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::Umull { rdlo, rdhi, rn, rm } => {
                let full = state
                    .get_reg(*rn)?
                    .zero_ext(32)
                    .bvmul(state.get_reg(*rm)?.zero_ext(32));
                let lo = full.extract(31, 0);
                let hi = full.extract(63, 32);
                state.set_reg(&eff, *rdlo, lo)?;
                state.set_reg(&eff, *rdhi, hi)?;
            }
            T2Op::Clz { rd, rm } => {
                let v = clz32(&state.get_reg(*rm)?);
                state.set_reg(&eff, *rd, v)?;
            }
            T2Op::Rbit { rd, rm } => {
                let v = rbit32(&state.get_reg(*rm)?);
                state.set_reg(&eff, *rd, v)?;
            }
        }

        if fallthrough {
            merge(&mut incoming, next, g);
        }
    }

    if !it_queue.is_empty() {
        return Err(ExpansionError::Internal(
            "IT block extends past the end of the sequence".into(),
        ));
    }
    Ok(())
}

// ===========================================================================
// WASM references and the per-pseudo-op contract
// ===========================================================================

/// What the validated result looks like.
enum RefResult {
    Word(BV),
    Pair(I64Pair),
}

/// WASM reference semantics for the covered i64 pseudo-op surface.
fn wasm_reference(op: &WasmOp, a: &I64Pair, b: &I64Pair) -> Option<RefResult> {
    use WasmOp::*;
    let word = |bv: BV| Some(RefResult::Word(bv));
    let pair = |p: I64Pair| Some(RefResult::Pair(p));
    match op {
        I64Mul => pair(i64_mul_schoolbook(a, b)),
        I64Shl => pair(i64_shl(a, &shift_amount64(b))),
        I64ShrU => pair(i64_shr_u(a, &shift_amount64(b))),
        I64ShrS => pair(i64_shr_s(a, &shift_amount64(b))),
        I64Rotl => pair(i64_rotl(a, &shift_amount64(b))),
        I64Rotr => pair(i64_rotr(a, &shift_amount64(b))),
        I64Eq => word(bool_to_i32(&a.eq_pair(b))),
        I64Ne => word(bool_to_i32(&a.eq_pair(b).not())),
        I64LtU => word(bool_to_i32(&i64_lt_u(a, b))),
        I64LtS => word(bool_to_i32(&i64_lt_s(a, b))),
        I64GtU => word(bool_to_i32(&i64_lt_u(b, a))),
        I64GtS => word(bool_to_i32(&i64_lt_s(b, a))),
        I64LeU => word(bool_to_i32(&i64_lt_u(b, a).not())),
        I64LeS => word(bool_to_i32(&i64_lt_s(b, a).not())),
        I64GeU => word(bool_to_i32(&i64_lt_u(a, b).not())),
        I64GeS => word(bool_to_i32(&i64_lt_s(a, b).not())),
        I64Eqz => word(bool_to_i32(&Bool::and(&[
            &a.lo.eq(k32(0)),
            &a.hi.eq(k32(0)),
        ]))),
        // Bit-counting ops produce an i64 whose low limb is the count.
        I64Clz => pair(I64Pair {
            lo: a
                .hi
                .eq(k32(0))
                .ite(clz32(&a.lo).bvadd(k32(32)), clz32(&a.hi)),
            hi: k32(0),
        }),
        I64Ctz => pair(I64Pair {
            lo: a
                .lo
                .eq(k32(0))
                .ite(ctz32(&a.hi).bvadd(k32(32)), ctz32(&a.lo)),
            hi: k32(0),
        }),
        // Two-link chain: the sequence is checked against the HAKMEM fold
        // (structural, fast); the HAKMEM fold is separately PROVED equal to
        // the bit-sum popcount for all inputs (see `popcnt32_hakmem`).
        I64Popcnt => pair(I64Pair {
            lo: popcnt32_hakmem(&a.lo).bvadd(popcnt32_hakmem(&a.hi)),
            hi: k32(0),
        }),
        _ => None,
    }
}

/// Where the sequence's inputs and result live, derived from the pseudo-op's
/// register fields (the contract the selector relies on).
struct Contract {
    /// (lo, hi) registers holding operand `a`.
    a: (u8, u8),
    /// (lo, hi) registers holding operand `b`. `hi: None` when the pseudo-op
    /// only consumes the low limb (rotate amounts).
    b: Option<(u8, Option<u8>)>,
    /// Result location: single register or (lo, hi) pair.
    result: ContractResult,
}

enum ContractResult {
    Word(u8),
    Pair(u8, u8),
}

fn ri(r: &Reg) -> u8 {
    crate::validator_pattern::reg_index(r) as u8
}

/// Derive the register contract from the pseudo-op. Returns `None` for
/// pseudo-ops outside the covered surface (i64 div/rem — held out).
fn contract_of(pseudo: &ArmOp) -> Option<Contract> {
    match pseudo {
        ArmOp::I64Mul {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        } => Some(Contract {
            a: (ri(rn_lo), ri(rn_hi)),
            b: Some((ri(rm_lo), Some(ri(rm_hi)))),
            result: ContractResult::Pair(ri(rd_lo), ri(rd_hi)),
        }),
        ArmOp::I64Shl {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        }
        | ArmOp::I64ShrU {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        }
        | ArmOp::I64ShrS {
            rd_lo,
            rd_hi,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
        } => Some(Contract {
            a: (ri(rn_lo), ri(rn_hi)),
            // rm_hi is a scratch register in the expansion; the amount's
            // high limb is semantically dead (WASM masks mod 64), so the
            // contract still seeds it — the expansion may clobber it freely.
            b: Some((ri(rm_lo), Some(ri(rm_hi)))),
            result: ContractResult::Pair(ri(rd_lo), ri(rd_hi)),
        }),
        ArmOp::I64Rotl {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            shift,
        }
        | ArmOp::I64Rotr {
            rdlo,
            rdhi,
            rnlo,
            rnhi,
            shift,
        } => Some(Contract {
            a: (ri(rnlo), ri(rnhi)),
            b: Some((ri(shift), None)),
            result: ContractResult::Pair(ri(rdlo), ri(rdhi)),
        }),
        ArmOp::I64SetCond {
            rd,
            rn_lo,
            rn_hi,
            rm_lo,
            rm_hi,
            ..
        } => Some(Contract {
            a: (ri(rn_lo), ri(rn_hi)),
            b: Some((ri(rm_lo), Some(ri(rm_hi)))),
            result: ContractResult::Word(ri(rd)),
        }),
        ArmOp::I64SetCondZ { rd, rn_lo, rn_hi } => Some(Contract {
            a: (ri(rn_lo), ri(rn_hi)),
            b: None,
            result: ContractResult::Word(ri(rd)),
        }),
        // The bit-counting expansions leave the count in `rd` and clear the
        // high limb IN PLACE in `rnhi` — the result pair is (rd, rnhi).
        ArmOp::I64Clz { rd, rnlo, rnhi }
        | ArmOp::I64Ctz { rd, rnlo, rnhi }
        | ArmOp::I64Popcnt { rd, rnlo, rnhi } => Some(Contract {
            a: (ri(rnlo), ri(rnhi)),
            b: None,
            result: ContractResult::Pair(ri(rd), ri(rnhi)),
        }),
        _ => None,
    }
}

// ===========================================================================
// The validation entry point
// ===========================================================================

/// Validate that the encoder's emitted `code` for `pseudo` implements `wasm`.
///
/// `code` must be the literal bytes the shipped Thumb-2 encoder produced for
/// `pseudo` (`ArmEncoder::encode`), so the artifact being certified is the
/// binary's actual instruction sequence. Returns an [`ExpansionWitness`]
/// (with a certificate-checked `Unsat`) or a loud error — including a
/// concrete counterexample when the sequence is wrong.
pub fn validate_expansion(
    wasm: &WasmOp,
    pseudo: &ArmOp,
    code: &[u8],
) -> Result<ExpansionWitness, ExpansionError> {
    let label = format!("{wasm:?}");

    let contract = contract_of(pseudo)
        .ok_or_else(|| ExpansionError::Unsupported(format!("pseudo-op {pseudo:?}")))?;

    let instrs = decode_thumb2(code)?;

    // Symbolic operands (limb pairs, exactly the ARM register-pair layout).
    let a = I64Pair {
        lo: sym32("a_lo"),
        hi: sym32("a_hi"),
    };
    let b = I64Pair {
        lo: sym32("b_lo"),
        hi: sym32("b_hi"),
    };

    let reference = wasm_reference(wasm, &a, &b)
        .ok_or_else(|| ExpansionError::Unsupported(format!("wasm op {wasm:?}")))?;

    // Seed the machine per the contract and execute the emitted sequence.
    let mut state = MachineState::new();
    let g_true = Bool::from_bool(true);
    state.set_reg(&g_true, contract.a.0, a.lo.clone())?;
    state.set_reg(&g_true, contract.a.1, a.hi.clone())?;
    if let Some((blo, bhi)) = &contract.b {
        state.set_reg(&g_true, *blo, b.lo.clone())?;
        if let Some(bhi) = bhi {
            state.set_reg(&g_true, *bhi, b.hi.clone())?;
        }
    }
    execute(&instrs, &mut state)?;

    // Assert ¬(wasm == sequence); unsat ⇒ equivalent for all inputs.
    let differ = match (&reference, &contract.result) {
        (RefResult::Word(w), ContractResult::Word(rd)) => w.eq(&state.get_reg(*rd)?).not(),
        (RefResult::Pair(w), ContractResult::Pair(rd_lo, rd_hi)) => {
            let got = I64Pair {
                lo: state.get_reg(*rd_lo)?,
                hi: state.get_reg(*rd_hi)?,
            };
            w.eq_pair(&got).not()
        }
        _ => {
            return Err(ExpansionError::Internal(format!(
                "result-shape mismatch for {label}"
            )));
        }
    };

    let mut solver = new_solver();
    solver.assert(&differ);
    match solver.check() {
        CheckOutcome::Unsat => Ok(ExpansionWitness {
            wasm_op_label: label,
            instr_count: instrs.len(),
            byte_len: code.len(),
            solver_result: SolverResultKind::Unsat,
        }),
        CheckOutcome::Sat => {
            let mut parts = Vec::new();
            for (name, bv) in [
                ("a_lo", &a.lo),
                ("a_hi", &a.hi),
                ("b_lo", &b.lo),
                ("b_hi", &b.hi),
            ] {
                if let Some(v) = solver.value(bv) {
                    parts.push(format!("{name}={v:#x}"));
                }
            }
            let description = if parts.is_empty() {
                "no model available".to_string()
            } else {
                parts.join(", ")
            };
            Err(ExpansionError::Counterexample {
                wasm_op_label: label,
                description,
            })
        }
        CheckOutcome::Unknown(reason) => {
            Err(ExpansionError::SolverUnknown(format!("{label}: {reason}")))
        }
    }
}

/// The covered `(WasmOp, pseudo ArmOp)` surface with the canonical
/// selector-shaped register assignment: operand `a` in (R0, R1), operand `b`
/// / amount in (R2, R3), result in R0 / (R0, R1). Callers (the `synth
/// verify` driver and the oracle tests) encode each pseudo-op through the
/// shipped `ArmEncoder` and feed the bytes to [`validate_expansion`].
pub fn covered_i64_pseudo_selections() -> Vec<(WasmOp, ArmOp)> {
    use synth_synthesis::rules::Condition;
    let mut v: Vec<(WasmOp, ArmOp)> = Vec::new();

    v.push((
        WasmOp::I64Mul,
        ArmOp::I64Mul {
            rd_lo: Reg::R0,
            rd_hi: Reg::R1,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        },
    ));

    let setcond = |cond: Condition| ArmOp::I64SetCond {
        rd: Reg::R0,
        rn_lo: Reg::R0,
        rn_hi: Reg::R1,
        rm_lo: Reg::R2,
        rm_hi: Reg::R3,
        cond,
    };
    v.push((WasmOp::I64Eq, setcond(Condition::EQ)));
    v.push((WasmOp::I64Ne, setcond(Condition::NE)));
    v.push((WasmOp::I64LtS, setcond(Condition::LT)));
    v.push((WasmOp::I64LeS, setcond(Condition::LE)));
    v.push((WasmOp::I64GtS, setcond(Condition::GT)));
    v.push((WasmOp::I64GeS, setcond(Condition::GE)));
    v.push((WasmOp::I64LtU, setcond(Condition::LO)));
    v.push((WasmOp::I64LeU, setcond(Condition::LS)));
    v.push((WasmOp::I64GtU, setcond(Condition::HI)));
    v.push((WasmOp::I64GeU, setcond(Condition::HS)));

    v.push((
        WasmOp::I64Eqz,
        ArmOp::I64SetCondZ {
            rd: Reg::R0,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
        },
    ));

    for (op, mk) in [
        (
            WasmOp::I64Shl,
            (|| ArmOp::I64Shl {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
                rm_lo: Reg::R2,
                rm_hi: Reg::R3,
            }) as fn() -> ArmOp,
        ),
        (WasmOp::I64ShrU, || ArmOp::I64ShrU {
            rd_lo: Reg::R0,
            rd_hi: Reg::R1,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        }),
        (WasmOp::I64ShrS, || ArmOp::I64ShrS {
            rd_lo: Reg::R0,
            rd_hi: Reg::R1,
            rn_lo: Reg::R0,
            rn_hi: Reg::R1,
            rm_lo: Reg::R2,
            rm_hi: Reg::R3,
        }),
    ] {
        v.push((op, mk()));
    }

    v.push((
        WasmOp::I64Rotl,
        ArmOp::I64Rotl {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            shift: Reg::R2,
        },
    ));
    v.push((
        WasmOp::I64Rotr,
        ArmOp::I64Rotr {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            shift: Reg::R2,
        },
    ));

    for (op, mk) in [
        (
            WasmOp::I64Clz,
            (|| ArmOp::I64Clz {
                rd: Reg::R0,
                rnlo: Reg::R0,
                rnhi: Reg::R1,
            }) as fn() -> ArmOp,
        ),
        (WasmOp::I64Ctz, || ArmOp::I64Ctz {
            rd: Reg::R0,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
        }),
        (WasmOp::I64Popcnt, || ArmOp::I64Popcnt {
            rd: Reg::R0,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
        }),
    ] {
        v.push((op, mk()));
    }

    v
}

// ===========================================================================
// Unit tests (encoder-independent: decoder + executor mechanics + red
// shapes built from literal bytes). The green-on-shipped-encoder oracle
// lives in `synth-backend/tests/i64_expansion_certification.rs`, where the
// real `ArmEncoder` is available.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::with_verification_context;

    fn halfwords(hws: &[u16]) -> Vec<u8> {
        let mut b = Vec::new();
        for hw in hws {
            b.extend_from_slice(&hw.to_le_bytes());
        }
        b
    }

    /// The bit-count references agree with native 64-bit truths on the
    /// joined value — pins the hand-rolled ite chains.
    #[test]
    fn bitcount_references_sanity() {
        with_verification_context(|| {
            // clz32(1) == 31, clz32(0) == 32, ctz32(8) == 3, popcnt(0xF0F) == 8
            for (v, clz, ctz, pop) in [
                (0u32, 32i64, 32i64, 0i64),
                (1, 31, 0, 1),
                (8, 28, 3, 1),
                (0x8000_0000, 0, 31, 1),
                (0xF0F, 20, 0, 8),
                (0xFFFF_FFFF, 0, 0, 32),
            ] {
                let x = k32(v as i64);
                let mut s = new_solver();
                let bad = Bool::or(&[
                    &clz32(&x).eq(k32(clz)).not(),
                    &ctz32(&x).eq(k32(ctz)).not(),
                    &popcnt32(&x).eq(k32(pop)).not(),
                ]);
                s.assert(&bad);
                assert_eq!(s.check(), CheckOutcome::Unsat, "bitcount refs for {v:#x}");
            }
        });
    }

    /// The schoolbook mul reference agrees with Rust's `u64` wrapping
    /// multiply on an edge-heavy concrete grid (the solver evaluates the
    /// formula on constants; Rust's `wrapping_mul` is the independent
    /// truth). This pins the reference that the symbolic i64.mul query is
    /// discharged against — the full symbolic schoolbook↔bvmul identity is
    /// past the bit-blasting budget (see `i64_mul_schoolbook`).
    #[test]
    fn schoolbook_mul_matches_u64_mul() {
        with_verification_context(|| {
            let grid: &[u64] = &[
                0,
                1,
                2,
                3,
                0x7FFF_FFFF,
                0x8000_0000,
                0xFFFF_FFFF,
                0x1_0000_0000,
                0xDEAD_BEEF_CAFE_F00D,
                0x8000_0000_0000_0000,
                0xFFFF_FFFF_FFFF_FFFF,
                0x0000_0001_0000_0001,
            ];
            for &x in grid {
                for &y in grid {
                    let truth = x.wrapping_mul(y);
                    let a = I64Pair {
                        lo: k32((x & 0xFFFF_FFFF) as i64),
                        hi: k32((x >> 32) as i64),
                    };
                    let b = I64Pair {
                        lo: k32((y & 0xFFFF_FFFF) as i64),
                        hi: k32((y >> 32) as i64),
                    };
                    let got = i64_mul_schoolbook(&a, &b);
                    let want = I64Pair {
                        lo: k32((truth & 0xFFFF_FFFF) as i64),
                        hi: k32((truth >> 32) as i64),
                    };
                    let mut s = new_solver();
                    s.assert(&got.eq_pair(&want).not());
                    assert_eq!(
                        s.check(),
                        CheckOutcome::Unsat,
                        "schoolbook mul wrong for {x:#x} * {y:#x}"
                    );
                }
            }
        });
    }

    /// rbit32 followed by clz32 equals ctz32 — the independence argument for
    /// the Ctz validation (the ARM side computes CLZ(RBIT(x))).
    #[test]
    fn rbit_clz_is_ctz() {
        with_verification_context(|| {
            let x = sym32("x");
            let mut s = new_solver();
            s.assert(&clz32(&rbit32(&x)).eq(ctz32(&x)).not());
            assert_eq!(s.check(), CheckOutcome::Unsat);
        });
    }

    /// Link 1 of the popcnt proof chain: the HAKMEM fold equals the bit-sum
    /// popcount for ALL 2^32 inputs — proved symbolically. Link 2 (the
    /// emitted sequence equals the HAKMEM fold per word, summed) is the
    /// `validate_expansion` query the certification oracle runs against the
    /// shipped encoder. Together: sequence == popcount.
    #[test]
    fn popcnt_hakmem_formula_is_popcnt() {
        with_verification_context(|| {
            let w = sym32("w");
            let mut s = new_solver();
            s.assert(&popcnt32_hakmem(&w).eq(popcnt32(&w)).not());
            assert_eq!(
                s.check(),
                CheckOutcome::Unsat,
                "HAKMEM fold must equal bit-sum popcount for all inputs"
            );
        });
    }

    /// Decoder rejects instructions outside the subset loudly.
    #[test]
    fn decoder_rejects_unknown_loudly() {
        // 0xDE00 is a permanently-undefined 16-bit encoding (cc=0xE).
        let r = decode_thumb2(&halfwords(&[0xDE00]));
        assert!(matches!(r, Err(ExpansionError::Decode { .. })), "{r:?}");
        // UDF.W (F7F0 A000) — 32-bit, unmodeled.
        let r = decode_thumb2(&halfwords(&[0xF7F0, 0xA000]));
        assert!(matches!(r, Err(ExpansionError::Decode { .. })), "{r:?}");
    }

    /// Backward branches (loops — the div/rem cores) are rejected loudly,
    /// never silently accepted: the held-out surface cannot green-wash.
    #[test]
    fn backward_branch_is_held_out_loudly() {
        with_verification_context(|| {
            // CMP R0, #0 ; BNE -4 (backward) — a minimal loop shape.
            let code = halfwords(&[0x2800, 0xD1FC]);
            let pseudo = ArmOp::I64SetCondZ {
                rd: Reg::R0,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
            };
            let r = validate_expansion(&WasmOp::I64Eqz, &pseudo, &code);
            match r {
                Err(ExpansionError::Decode { reason, .. }) => {
                    assert!(reason.contains("backward branch"), "{reason}");
                }
                other => panic!("expected backward-branch decode error, got {other:?}"),
            }
        });
    }

    /// i64 div/rem pseudo-ops are outside the covered surface (held out).
    #[test]
    fn div_rem_pseudo_ops_are_unsupported() {
        let pseudo = ArmOp::I64DivU {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rnlo: Reg::R0,
            rnhi: Reg::R1,
            rmlo: Reg::R2,
            rmhi: Reg::R3,
            elide_zero_guard: false,
        };
        let r = validate_expansion(&WasmOp::I64DivU, &pseudo, &[]);
        assert!(matches!(r, Err(ExpansionError::Unsupported(_))), "{r:?}");
    }

    /// A hand-built minimal I64SetCondZ sequence certifies: the executor's
    /// ORR/CMP/ITE/MOV modeling is exercised without the encoder.
    /// (ORR.W R0, R0, R1; CMP R0, #0; ITE EQ; MOV R0,#1; MOV R0,#0.)
    #[test]
    fn hand_built_eqz_sequence_certifies() {
        with_verification_context(|| {
            let code = halfwords(&[
                0xEA40, 0x0001, // ORR.W R0, R0, R1
                0x2800, // CMP R0, #0
                0xBF0C, // ITE EQ
                0x2001, // MOV R0, #1
                0x2000, // MOV R0, #0
            ]);
            let pseudo = ArmOp::I64SetCondZ {
                rd: Reg::R0,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
            };
            let w = validate_expansion(&WasmOp::I64Eqz, &pseudo, &code)
                .expect("eqz sequence must certify");
            assert_eq!(w.solver_result, SolverResultKind::Unsat);
            assert_eq!(w.instr_count, 5);
        });
    }

    /// The same sequence with the ITE polarity flipped (ITE NE) is rejected
    /// with a counterexample — the executor's IT modeling is not vacuous.
    #[test]
    fn hand_built_eqz_wrong_polarity_rejected() {
        with_verification_context(|| {
            let code = halfwords(&[
                0xEA40, 0x0001, // ORR.W R0, R0, R1
                0x2800, // CMP R0, #0
                0xBF14, // ITE NE (firstcond=1, mask=0x4)
                0x2001, // MOV R0, #1
                0x2000, // MOV R0, #0
            ]);
            let pseudo = ArmOp::I64SetCondZ {
                rd: Reg::R0,
                rn_lo: Reg::R0,
                rn_hi: Reg::R1,
            };
            match validate_expansion(&WasmOp::I64Eqz, &pseudo, &code) {
                Err(ExpansionError::Counterexample { .. }) => {}
                other => panic!("expected Counterexample, got {other:?}"),
            }
        });
    }
}
