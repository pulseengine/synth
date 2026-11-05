//! #498 / #242 (VCR-ORACLE-001), #1206 — estimator↔encoder agreement oracle.
//!
//! The optimized ARM path (`synth_synthesis::optimizer_bridge::ir_to_arm`)
//! resolves branch displacements by summing a hand-maintained *byte-size
//! estimator* (`estimate_arm_byte_size`) over the instruction stream, and the
//! post-allocation passes in `liveness.rs` reconstruct branch targets and
//! freeze span sizes with the same estimator. It is a mirror of the Thumb-2
//! encoder (`synth_backend::ArmEncoder::encode`), kept by hand only because
//! synth-synthesis cannot depend on synth-backend. When the mirror drifts, a
//! branch spanning the drifting op lands on the wrong instruction:
//! under-estimate → short, over-estimate → long.
//!
//! ## #1206: why the old oracle was green over a live miscompile
//!
//! The old oracle was a hand-written table of ~90 representative cases and
//! asserted exact agreement "for EVERY case". Its `SetCond` case used `rd: r0`
//! and its `Cmp`-immediate case `rn: R1`. On the default optimized path a
//! loop condition allocated to R8 is `ite; mov.w r8,#1; mov.w r8,#0; cmp.w
//! r8,#0` — 10 + 4 bytes that the estimator sized 6 + 2 — so every `br_if`
//! back-edge over it landed 6 bytes short, after the loop's increment, and the
//! loop never terminated (#1206). The table was right about every row it had;
//! its rows were a sample, and the defect lived in the operand classes it did
//! not sample.
//!
//! ## What this oracle asserts now
//!
//! `domain()` generates every `OnPath` variant across its operand classes:
//! all thirteen allocatable registers R0–R12 (plus SP where an op takes a base
//! or frame operand, and LR/PC where it is a link operand) in every position
//! for ops with up to three register operands; low/high representatives
//! (R0, R7, R8, R12) in every position for the multi-register i64 expansions;
//! every immediate-width class (imm3 / imm8 / imm12 / imm16 / wide / negative)
//! for immediates; every scaled-offset class for loads and stores; every shift
//! amount 0..=32; register-offset addressing with and without an immediate;
//! every condition; near and far branch displacements. The estimator must equal
//! the real encoder's byte length for EVERY op in that domain the encoder
//! accepts — no allowlist, no exception table. Ops the encoder REFUSES are
//! not compared (they cannot ship) but are counted, and each variant must
//! compare a non-zero number of ops, so a domain that the encoder rejects
//! wholesale cannot pass vacuously.
//!
//! The #1206 audit, run with this domain against `main`'s estimator and
//! encoder before the fix, found more than #1206's two sizes. Every row was
//! fixed in the estimator:
//!
//! | op / operand class                                   | estimator | encoder   |
//! |------------------------------------------------------|-----------|-----------|
//! | `SetCond` high rd                                    | 6         | 10        |
//! | `Cmp #imm` high rn; low rn with imm < 0 or > 255     | 2         | 4         |
//! | `I64SetCond` high rd                                 | 12        | 16        |
//! | `I64SetCondZ` high rd                                | 12        | 18        |
//! | `I64Extend32S` with rdlo == rnlo                     | 6         | 4         |
//! | `Asr`/`Lsr` high reg, or shift 0 / 32                | 2         | 4         |
//! | `Lsl` high reg; `Ror` always                         | 2         | 4         |
//! | `Add`/`Sub` low regs with imm > 7; `Sub` imm; SP     | 2         | 4         |
//! | `Ldr`/`Str` register offset with a high offset reg   | 2         | 4         |
//! | any load/store, register offset PLUS an immediate    | 2 or 4    | 8, 12, 16 |
//! | `Ldrb`/`Strb`/`Ldrh`/`Strh` low regs, short offset   | 4         | 2         |
//! | `MemorySize` (reads R10)                             | 2         | 4         |
//! | `Push`/`Pop` with any of R8–R12                      | 2         | 4         |
//! | `Cmn` shifted-register operand                       | 4         | 2 (NOP)   |
//!
//! The last row was an encoder defect, not an estimator one: the 16-bit
//! "encoding" was a NOP (the #1272/#615 silent-NOP class). It is now refused.
//! An every-op census of the optimized path's FINAL Thumb streams (spec
//! suite + repro corpus, cortex-m3/m4/m4f/m7/m7dp) found these rows live on
//! shipped code: `SetCond`/`Cmp` high (#1206), `I64SetCond` high rd,
//! `MemorySize`, and — outside every branch span — `Push`/`Pop` and the
//! `sub sp, sp, #frame` adjust. The only MIS-LANDED branches it found were
//! the #1206 class; a `memory.size` inside a loop is a second one, added to
//! the execution differential.
//!
//! Operand classes the encoder accepts but encodes WRONGLY are outside what a
//! length oracle can see: `Add`/`Sub` with a shifted-register operand fall back
//! to `ADD/SUB rd, rn, #0`, and a negative `Add`/`Sub` immediate with low
//! registers takes the 16-bit `#imm3` form with an overflowing field. Neither
//! is constructed by any emitter today (measured: `i32.add x, -1` materializes
//! the constant); both are reported on #1206, not fixed here.

use std::collections::BTreeMap;
use synth_backend::ArmEncoder;
use synth_synthesis::{
    ArmOp, Condition, MemAddr, Operand2, Reg, ShiftType, estimate_arm_byte_size,
};

const LOW_HIGH: [Reg; 13] = [
    Reg::R0,
    Reg::R1,
    Reg::R2,
    Reg::R3,
    Reg::R4,
    Reg::R5,
    Reg::R6,
    Reg::R7,
    Reg::R8,
    Reg::R9,
    Reg::R10,
    Reg::R11,
    Reg::R12,
];
/// Low/high boundary representatives, for ops with four or more register
/// operands (the full 13^6 product is 4.8M ops per i64 variant).
const REPS: [Reg; 4] = [Reg::R0, Reg::R7, Reg::R8, Reg::R12];
const CONDS: [Condition; 10] = [
    Condition::EQ,
    Condition::NE,
    Condition::LT,
    Condition::LE,
    Condition::GT,
    Condition::GE,
    Condition::LO,
    Condition::LS,
    Condition::HI,
    Condition::HS,
];
/// Every immediate-width class an encoder split tests: imm3 (0..=7), imm8,
/// imm12, imm16, wider, ThumbExpandImm-shaped, and negatives.
const IMMS: [i32; 31] = [
    0,
    1,
    2,
    3,
    7,
    8,
    31,
    32,
    100,
    255,
    256,
    257,
    0x3FC,
    1020,
    1023,
    1024,
    4095,
    4096,
    0xFF00,
    0xFFFF,
    0x10000,
    0x12345,
    0x00FF_00FF,
    0x7FFF_FFFF,
    -1,
    -2,
    -8,
    -255,
    -256,
    -4096,
    i32::MIN,
];
/// Load/store offsets: every alignment (1/2/4) at each scaled-imm5 boundary
/// (byte 31, half 62, word 124) and beyond, imm8/imm12 edges, negatives.
const OFFSETS: [i32; 22] = [
    0, 1, 2, 3, 4, 31, 62, 64, 124, 126, 128, 252, 256, 1020, 1024, 4095, 4096, -1, -4, -255, -256,
    -257,
];

fn with_sp(regs: &[Reg]) -> Vec<Reg> {
    let mut v = regs.to_vec();
    v.push(Reg::SP);
    v
}

fn operand2s() -> Vec<Operand2> {
    let mut v: Vec<Operand2> = with_sp(&LOW_HIGH).into_iter().map(Operand2::Reg).collect();
    v.extend(IMMS.iter().map(|&i| Operand2::Imm(i)));
    for rm in REPS {
        for shift in [ShiftType::LSL, ShiftType::ASR] {
            for amount in [0u32, 1, 31] {
                v.push(Operand2::RegShift { rm, shift, amount });
            }
        }
    }
    v
}

fn addrs() -> Vec<MemAddr> {
    let mut v = Vec::new();
    for base in with_sp(&LOW_HIGH) {
        for offset in OFFSETS {
            v.push(MemAddr {
                base,
                offset,
                offset_reg: None,
            });
        }
    }
    for base in REPS {
        for off_reg in REPS {
            for offset in [0, 4, -4, 255, 4096, 0x12345] {
                v.push(MemAddr {
                    base,
                    offset,
                    offset_reg: Some(off_reg),
                });
            }
        }
    }
    v
}

/// The sweep domain: every `OnPath` variant across its operand classes.
fn domain() -> Vec<ArmOp> {
    use ArmOp::*;
    let mut ops = Vec::new();
    let op2s = operand2s();
    let rd_rn = with_sp(&LOW_HIGH);
    type Op2Ctor = fn(Reg, Reg, Operand2) -> ArmOp;
    let op2_ctors: [Op2Ctor; 9] = [
        |rd, rn, op2| Add { rd, rn, op2 },
        |rd, rn, op2| Sub { rd, rn, op2 },
        |rd, rn, op2| Adds { rd, rn, op2 },
        |rd, rn, op2| Subs { rd, rn, op2 },
        |rd, rn, op2| Adc { rd, rn, op2 },
        |rd, rn, op2| Sbc { rd, rn, op2 },
        |rd, rn, op2| And { rd, rn, op2 },
        |rd, rn, op2| Orr { rd, rn, op2 },
        |rd, rn, op2| Eor { rd, rn, op2 },
    ];
    for mk in op2_ctors {
        for &rd in &rd_rn {
            for &rn in &rd_rn {
                for op2 in &op2s {
                    ops.push(mk(rd, rn, op2.clone()));
                }
            }
        }
    }
    for &rn in &rd_rn {
        for op2 in &op2s {
            ops.push(Cmp {
                rn,
                op2: op2.clone(),
            });
            ops.push(Cmn {
                rn,
                op2: op2.clone(),
            });
        }
    }
    for rd in [LOW_HIGH.as_slice(), &[Reg::SP, Reg::LR]].concat() {
        for op2 in &op2s {
            ops.push(Mov {
                rd,
                op2: op2.clone(),
            });
        }
    }
    type R3Ctor = fn(Reg, Reg, Reg) -> ArmOp;
    let r3_ctors: [R3Ctor; 7] = [
        |rd, rn, rm| Mul { rd, rn, rm },
        |rd, rn, rm| Sdiv { rd, rn, rm },
        |rd, rn, rm| Udiv { rd, rn, rm },
        |rd, rn, rm| AsrReg { rd, rn, rm },
        |rd, rn, rm| LslReg { rd, rn, rm },
        |rd, rn, rm| LsrReg { rd, rn, rm },
        |rd, rn, rm| RorReg { rd, rn, rm },
    ];
    for mk in r3_ctors {
        for rd in LOW_HIGH {
            for rn in LOW_HIGH {
                for rm in LOW_HIGH {
                    ops.push(mk(rd, rn, rm));
                }
            }
        }
    }
    for rd in REPS {
        for rn in REPS {
            for rm in REPS {
                for ra in REPS {
                    ops.push(Mls { rd, rn, rm, ra });
                }
            }
        }
    }
    for rd in LOW_HIGH {
        for rn in LOW_HIGH {
            for shift in 0..=32u32 {
                ops.push(Asr { rd, rn, shift });
                ops.push(Lsl { rd, rn, shift });
                ops.push(Lsr { rd, rn, shift });
                ops.push(Ror { rd, rn, shift });
            }
            for imm in IMMS {
                ops.push(Rsb {
                    rd,
                    rn,
                    imm: imm as u32,
                });
            }
        }
    }
    type R2Ctor = fn(Reg, Reg) -> ArmOp;
    let r2_ctors: [R2Ctor; 7] = [
        |rd, rm| Clz { rd, rm },
        |rd, rm| Rbit { rd, rm },
        |rd, rm| Popcnt { rd, rm },
        |rd, rm| Sxtb { rd, rm },
        |rd, rm| Sxth { rd, rm },
        |rd, rm| Uxtb { rd, rm },
        |rd, rm| Uxth { rd, rm },
    ];
    for mk in r2_ctors {
        for rd in LOW_HIGH {
            for rm in LOW_HIGH {
                ops.push(mk(rd, rm));
            }
        }
    }
    for rd in LOW_HIGH {
        for imm16 in [0u16, 1, 255, 256, 0xFFFF] {
            ops.push(Movw { rd, imm16 });
            ops.push(Movt { rd, imm16 });
        }
        for page_log2 in [0u32, 1, 16, 31] {
            ops.push(MemorySize { rd, page_log2 });
        }
    }
    type MemCtor = fn(Reg, MemAddr) -> ArmOp;
    let mem_ctors: [MemCtor; 8] = [
        |rd, addr| Ldr { rd, addr },
        |rd, addr| Str { rd, addr },
        |rd, addr| Ldrb { rd, addr },
        |rd, addr| Ldrh { rd, addr },
        |rd, addr| Ldrsb { rd, addr },
        |rd, addr| Ldrsh { rd, addr },
        |rd, addr| Strb { rd, addr },
        |rd, addr| Strh { rd, addr },
    ];
    let addrs = addrs();
    for mk in mem_ctors {
        for rd in LOW_HIGH {
            for addr in &addrs {
                ops.push(mk(rd, addr.clone()));
            }
        }
    }
    // Every register subset of R0-R12 up to 4 registers, plus every 7th mask
    // beyond, each with and without the link register.
    for mask in 0u32..(1 << 13) {
        if mask.count_ones() > 4 && mask % 7 != 0 {
            continue;
        }
        let regs: Vec<Reg> = LOW_HIGH
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, r)| *r)
            .collect();
        ops.push(Push { regs: regs.clone() });
        ops.push(Pop { regs: regs.clone() });
        ops.push(Push {
            regs: [regs.as_slice(), &[Reg::LR]].concat(),
        });
        ops.push(Pop {
            regs: [regs.as_slice(), &[Reg::PC]].concat(),
        });
    }
    for offset in [
        -2000i32,
        -1026,
        -1024,
        -256,
        -130,
        -128,
        -2,
        0,
        2,
        126,
        128,
        254,
        256,
        1022,
        1024,
        5000,
        1 << 20,
    ] {
        ops.push(BOffset { offset });
        for cond in CONDS {
            ops.push(BCondOffset { cond, offset });
        }
    }
    for rm in [LOW_HIGH.as_slice(), &[Reg::LR]].concat() {
        ops.push(Bx { rm });
    }
    ops.push(Bl {
        label: "func_1".to_string(),
    });
    for imm in [0u8, 1, 255] {
        ops.push(Udf { imm });
    }
    for rd in LOW_HIGH {
        for cond in CONDS {
            ops.push(SetCond { rd, cond });
            for rm in LOW_HIGH {
                ops.push(SelectMove { rd, rm, cond });
            }
        }
    }
    for a in REPS {
        for b in REPS {
            for c in REPS {
                ops.push(I64SetCondZ {
                    rd: a,
                    rn_lo: b,
                    rn_hi: c,
                });
                ops.push(I64Clz {
                    rd: a,
                    rnlo: b,
                    rnhi: c,
                });
                ops.push(I64Ctz {
                    rd: a,
                    rnlo: b,
                    rnhi: c,
                });
                ops.push(I64Popcnt {
                    rd: a,
                    rnlo: b,
                    rnhi: c,
                });
                ops.push(I64Extend8S {
                    rdlo: a,
                    rdhi: b,
                    rnlo: c,
                });
                ops.push(I64Extend16S {
                    rdlo: a,
                    rdhi: b,
                    rnlo: c,
                });
                ops.push(I64Extend32S {
                    rdlo: a,
                    rdhi: b,
                    rnlo: c,
                });
                for d in REPS {
                    for e in REPS {
                        for cond in CONDS {
                            ops.push(I64SetCond {
                                rd: a,
                                rn_lo: b,
                                rn_hi: c,
                                rm_lo: d,
                                rm_hi: e,
                                cond,
                            });
                        }
                        ops.push(I64Rotl {
                            rdlo: a,
                            rdhi: b,
                            rnlo: c,
                            rnhi: d,
                            shift: e,
                        });
                        ops.push(I64Rotr {
                            rdlo: a,
                            rdhi: b,
                            rnlo: c,
                            rnhi: d,
                            shift: e,
                        });
                        for f in REPS {
                            ops.push(I64Mul {
                                rd_lo: a,
                                rd_hi: b,
                                rn_lo: c,
                                rn_hi: d,
                                rm_lo: e,
                                rm_hi: f,
                            });
                            ops.push(I64Shl {
                                rd_lo: a,
                                rd_hi: b,
                                rn_lo: c,
                                rn_hi: d,
                                rm_lo: e,
                                rm_hi: f,
                            });
                            ops.push(I64ShrU {
                                rd_lo: a,
                                rd_hi: b,
                                rn_lo: c,
                                rn_hi: d,
                                rm_lo: e,
                                rm_hi: f,
                            });
                            ops.push(I64ShrS {
                                rd_lo: a,
                                rd_hi: b,
                                rn_lo: c,
                                rn_hi: d,
                                rm_lo: e,
                                rm_hi: f,
                            });
                            for z in [false, true] {
                                ops.push(I64DivU {
                                    rdlo: a,
                                    rdhi: b,
                                    rnlo: c,
                                    rnhi: d,
                                    rmlo: e,
                                    rmhi: f,
                                    elide_zero_guard: z,
                                });
                                ops.push(I64RemU {
                                    rdlo: a,
                                    rdhi: b,
                                    rnlo: c,
                                    rnhi: d,
                                    rmlo: e,
                                    rmhi: f,
                                    elide_zero_guard: z,
                                });
                                ops.push(I64RemS {
                                    rdlo: a,
                                    rdhi: b,
                                    rnlo: c,
                                    rnhi: d,
                                    rmlo: e,
                                    rmhi: f,
                                    elide_zero_guard: z,
                                });
                                for o in [false, true] {
                                    ops.push(I64DivS {
                                        rdlo: a,
                                        rdhi: b,
                                        rnlo: c,
                                        rnhi: d,
                                        rmlo: e,
                                        rmhi: f,
                                        elide_zero_guard: z,
                                        elide_overflow_guard: o,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    ops
}

fn variant_name(op: &ArmOp) -> String {
    format!("{op:?}")
        .chars()
        .take_while(|c| c.is_alphanumeric())
        .collect()
}

/// Every `ArmOp` variant, classified as emitted by the optimized path
/// (`OnPath`) or not (`OffPath`). NO wildcard: a newly-added `ArmOp` variant
/// will fail to compile here until it is *consciously classified* — the
/// tripwire that puts a new op in front of a human instead of letting it default
/// to the estimator's `_ => 2`.
///
/// What this guarantees and what it does NOT:
/// - It DOES force every new `ArmOp` variant to be classified OnPath/OffPath.
/// - `every_on_path_variant_is_swept` checks that `ON_PATH_VARIANTS` and the
///   variants `domain()` generates agree in BOTH directions, and the main test
///   asserts `coverage(op) == OnPath` for every generated op. A variant newly
///   classified `OnPath` here but added to neither the list nor `domain()`
///   still passes: naming it in `ON_PATH_VARIANTS` is a manual step, after
///   which a missing domain reds.
/// - It cannot catch an existing `OffPath` op later being wired into the
///   optimized path (the classification is a claim). That residual is what
///   the compile-time branch-landing check in `arm_backend.rs`
///   (`validate_estimated_branch_landings`, #1206) covers: it sizes every
///   shipped estimator-resolved branch span with the REAL encoder and refuses
///   the compile on a mis-landing, whatever op caused it.
///
/// So: a compile-time prompt to classify, backed by an execution-free check
/// on every compiled function for what the classification gets wrong.
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
        | I64RemS { .. }
        // #1206 audit, MEASURED (an every-op census of the optimized path's
        // FINAL Thumb streams over the spec suite + repro corpus, five
        // targets): the immediate shifts reach the final stream through the
        // post-allocation imm-shift fold (`fold_immediate_shifts`), and
        // `MemorySize` / `Push` / `Pop` are emitted there too. They were filed
        // OffPath below while the estimator sized them at `_ => 2`; `Ror` is
        // classified with its siblings (the estimator is exact for it).
        | Lsl { .. }
        | Lsr { .. }
        | Ror { .. }
        | MemorySize { .. }
        | Push { .. }
        | Pop { .. } => OnPath,

        // NOT emitted by ir_to_arm:
        //  - Mvn / Umull / Mla: direct-selector-only (#209/#257).
        //  - sym-loads (--native-pointer-abi), MemoryGrow, Label/Nop/B/Bcc/Bhs/
        //    Blo/Blx (path uses the resolved BOffset/BCondOffset forms), pseudo
        //    Local*/Global*/Select/Call*/BrTable (lowered to primitives upstream).
        //  - i64 BINOPS (Add/Sub/And/Or/Xor/Eq..GeU/Const/Ldr/Str/ExtendI32*/
        //    I32WrapI64): lowered to 32-bit op pairs upstream, never appear as
        //    I64* in arm_instrs (which is why the estimator lists only the
        //    SURVIVING i64 ops above).
        //  - all F32*/F64* scalar VFP (dropped at the decoder today, #369) and
        //    all Mve* vector ops (not on the scalar integer path).
        Mvn { .. }
        | Umull { .. }
        | Mla { .. }
        | MovwSym { .. }
        | MovtSym { .. }
        | LdrSym { .. }
        | MemoryGrow { .. }
        | Label { .. }
        | Nop
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
        | MveSqrtF32 { .. }
        // RQ-67-VFPREACH (#1267): emitted by the DIRECT selector's wide-VFP
        // rung (`select_with_stack`), not by `ir_to_arm`, so it never flows
        // through the optimized path's `byte_offsets` estimator this oracle
        // compares against. OffPath for the same reason the direct-path i64
        // ops above are — and, like them, this is a hand-asserted claim the
        // file's own doc says it cannot prove exhaustively.
        | VPushCalleeSavedVfp
        | VPopCalleeSavedVfp => OffPath,
    }
}

/// The estimator must equal the real encoder's byte length for EVERY op in
/// the sweep domain the encoder accepts. No allowlist: a genuine new
/// divergence is fixed in the estimator (or the encoder), never tolerated.
#[test]
fn estimator_encoder_agreement() {
    let enc = ArmEncoder::new_thumb2();
    // variant -> (compared, refused by the encoder)
    let mut per_variant: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    let mut drift: BTreeMap<(String, usize, usize), (usize, String)> = BTreeMap::new();

    for op in domain() {
        assert_eq!(
            coverage(&op),
            Coverage::OnPath,
            "{op:?}: sweep domain contains an OffPath op — remove it or reclassify"
        );
        let name = variant_name(&op);
        let entry = per_variant.entry(name.clone()).or_default();
        let Ok(bytes) = enc.encode(&op) else {
            entry.1 += 1;
            continue;
        };
        entry.0 += 1;
        let est = estimate_arm_byte_size(&op);
        if est != bytes.len() {
            let d = drift
                .entry((name, est, bytes.len()))
                .or_insert((0, format!("{op:?}")));
            d.0 += 1;
        }
    }

    let vacuous: Vec<&String> = per_variant
        .iter()
        .filter(|(_, (compared, _))| *compared == 0)
        .map(|(v, _)| v)
        .collect();
    assert!(
        vacuous.is_empty(),
        "variants the encoder refused for EVERY op in the domain (nothing compared): {vacuous:?}"
    );

    assert!(
        drift.is_empty(),
        "estimator↔encoder drift (fix the estimator, never allowlist):\n{}",
        drift
            .iter()
            .map(|((v, est, real), (n, ex))| format!(
                "  {v}: estimator {est} != encoder {real} on {n} op(s), e.g. {ex}"
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Every variant `coverage()` classifies `OnPath` must have an operand domain
/// in `domain()`. The old hand-written case table could not enforce this: a
/// variant classified `OnPath` with no case passed vacuously.
#[test]
fn every_on_path_variant_is_swept() {
    let swept: std::collections::BTreeSet<String> = domain().iter().map(variant_name).collect();
    // One instance of every variant `coverage()` names, in declaration order.
    // `coverage()` is a no-wildcard match, so a new `ArmOp` variant fails to
    // compile there; this list is where it must then be named so its
    // classification is checked against the domain.
    let on_path: Vec<String> = ON_PATH_VARIANTS.iter().map(|s| s.to_string()).collect();
    let missing: Vec<&String> = on_path.iter().filter(|v| !swept.contains(*v)).collect();
    assert!(
        missing.is_empty(),
        "OnPath variants with no sweep domain: {missing:?}"
    );
    let unlisted: Vec<&String> = swept.iter().filter(|v| !on_path.contains(v)).collect();
    assert!(
        unlisted.is_empty(),
        "swept variants missing from ON_PATH_VARIANTS: {unlisted:?}"
    );
}

/// The `OnPath` variants, by name. Kept equal to `coverage()`'s `OnPath` arm
/// by `every_on_path_variant_is_swept` (both directions) and by the
/// `coverage(&op) == OnPath` assertion over the whole domain.
const ON_PATH_VARIANTS: [&str; 70] = [
    "Add",
    "Sub",
    "Adds",
    "Subs",
    "Adc",
    "Sbc",
    "Mul",
    "Mls",
    "Sdiv",
    "Udiv",
    "And",
    "Orr",
    "Eor",
    "Asr",
    "AsrReg",
    "LslReg",
    "LsrReg",
    "RorReg",
    "Rsb",
    "Clz",
    "Rbit",
    "Popcnt",
    "Sxtb",
    "Sxth",
    "Uxtb",
    "Uxth",
    "Mov",
    "Movw",
    "Movt",
    "Cmp",
    "Cmn",
    "Ldr",
    "Str",
    "Ldrb",
    "Ldrh",
    "Ldrsb",
    "Ldrsh",
    "Strb",
    "Strh",
    "BOffset",
    "BCondOffset",
    "Bx",
    "Bl",
    "Udf",
    "SetCond",
    "SelectMove",
    "I64SetCond",
    "I64SetCondZ",
    "I64Mul",
    "I64Shl",
    "I64ShrU",
    "I64ShrS",
    "I64Rotl",
    "I64Rotr",
    "I64Clz",
    "I64Ctz",
    "I64Popcnt",
    "I64Extend8S",
    "I64Extend16S",
    "I64Extend32S",
    "I64DivU",
    "I64RemU",
    "I64DivS",
    "I64RemS",
    "Lsl",
    "Lsr",
    "Ror",
    "MemorySize",
    "Push",
    "Pop",
];

/// #1206, named: the two sizes behind the hanging back-edge. A loop condition
/// allocated to R8 is `ite; mov.w r8,#1; mov.w r8,#0` then `cmp.w r8,#0`.
#[test]
fn high_register_setcond_and_cmp_imm_1206() {
    let enc = ArmEncoder::new_thumb2();
    for (op, want) in [
        (
            ArmOp::SetCond {
                rd: Reg::R8,
                cond: Condition::LO,
            },
            10,
        ),
        (
            ArmOp::Cmp {
                rn: Reg::R8,
                op2: Operand2::Imm(0),
            },
            4,
        ),
        (
            ArmOp::SetCond {
                rd: Reg::R7,
                cond: Condition::LO,
            },
            6,
        ),
        (
            ArmOp::Cmp {
                rn: Reg::R7,
                op2: Operand2::Imm(0),
            },
            2,
        ),
    ] {
        let real = enc.encode(&op).expect("encodable").len();
        assert_eq!(real, want, "{op:?}: encoder length moved");
        assert_eq!(estimate_arm_byte_size(&op), want, "{op:?}: estimator");
    }
}
