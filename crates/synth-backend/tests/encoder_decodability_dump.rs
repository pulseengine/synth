//! Encoder decodability sweep — dump mode.
//!
//! Systematically encodes ArmOp values across register/immediate/offset/
//! condition ranges and prints `<debug>\t<hex>` lines for an external
//! disassembler oracle (capstone) to validate. This is the differential
//! extension issue #82 flagged as out-of-scope for the panic-freedom fuzz
//! target: `Ok(bytes)` from the encoder must be *decodable* — an Err is fine,
//! undecodable bytes are not (#330: `f5e0 0109`, dp-modified-imm op=1111).
//!
//! Run: `cargo test -p synth-backend --test encoder_decodability_dump -- --nocapture`
//! then validate the dump with scripts/repro/check_decodability.py.

use synth_backend::ArmEncoder;
use synth_core::target::FPUPrecision;
use synth_synthesis::{ArmOp, Condition, MemAddr, Operand2, Reg, ShiftType};

const REGS: &[Reg] = &[
    Reg::R0,
    Reg::R1,
    Reg::R2,
    Reg::R3,
    Reg::R4,
    Reg::R7,
    Reg::R8,
    Reg::R12,
    Reg::SP,
    Reg::LR,
];

const IMMS: &[i32] = &[
    0,
    1,
    4,
    9,
    0x24,
    0x25,
    0x80,
    0xC8,
    0xFF,
    0x100,
    0x101,
    0x404,
    0x500,
    0x7FF,
    0x800,
    0x809,
    0xFFF,
    0x1000,
    0x1234,
    0xFFFF,
    0x10000,
    0x00890000,
    0x12345678,
    i32::MAX,
    i32::MIN,
    -1,
    -4,
    -9,
    -0x24,
    -0x100,
    -0x404,
    -0x1000,
];

const CONDS: &[Condition] = &[
    Condition::EQ,
    Condition::NE,
    Condition::HS,
    Condition::LO,
    Condition::HI,
    Condition::LS,
    Condition::GE,
    Condition::LT,
    Condition::GT,
    Condition::LE,
];

fn dump(enc: &ArmEncoder, tag: &str, op: &ArmOp) {
    if let Ok(bytes) = enc.encode(op) {
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        println!("SWEEP\t{tag}\t{op:?}\t{hex}");
    }
}

#[test]
fn dump_encodings_for_decodability_oracle() {
    for (tag, enc) in [
        ("thumb2", ArmEncoder::new_thumb2()),
        (
            "thumb2_fpu",
            ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Single)),
        ),
    ] {
        let e = &enc;
        // Data-processing: imm + reg + shifted-reg forms.
        for &rd in REGS {
            for &rn in REGS {
                for &imm in IMMS {
                    for op in [
                        ArmOp::Add {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Sub {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Adds {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Subs {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Adc {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Sbc {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::And {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Orr {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Eor {
                            rd,
                            rn,
                            op2: Operand2::Imm(imm),
                        },
                        ArmOp::Rsb {
                            rd,
                            rn,
                            imm: imm as u32,
                        },
                    ] {
                        dump(e, tag, &op);
                    }
                }
                for op in [
                    ArmOp::Add {
                        rd,
                        rn,
                        op2: Operand2::Reg(Reg::R5),
                    },
                    ArmOp::Sub {
                        rd,
                        rn,
                        op2: Operand2::Reg(Reg::R5),
                    },
                    ArmOp::Adc {
                        rd,
                        rn,
                        op2: Operand2::Reg(Reg::R5),
                    },
                    ArmOp::Sbc {
                        rd,
                        rn,
                        op2: Operand2::Reg(Reg::R5),
                    },
                ] {
                    dump(e, tag, &op);
                }
                for shift in [
                    ShiftType::LSL,
                    ShiftType::LSR,
                    ShiftType::ASR,
                    ShiftType::ROR,
                ] {
                    for amount in [0u32, 1, 2, 4, 16, 31, 32, 33] {
                        dump(
                            e,
                            tag,
                            &ArmOp::Add {
                                rd,
                                rn,
                                op2: Operand2::RegShift {
                                    rm: Reg::R5,
                                    shift,
                                    amount,
                                },
                            },
                        );
                    }
                }
            }
            // Mov/Mvn/Movw/Movt/Cmp/Cmn.
            for &imm in IMMS {
                dump(
                    e,
                    tag,
                    &ArmOp::Mov {
                        rd,
                        op2: Operand2::Imm(imm),
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::Mvn {
                        rd,
                        op2: Operand2::Imm(imm),
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::Cmp {
                        rn: rd,
                        op2: Operand2::Imm(imm),
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::Cmn {
                        rn: rd,
                        op2: Operand2::Imm(imm),
                    },
                );
            }
            for imm16 in [0u16, 1, 9, 0x809, 0x1234, 0x8000, 0xFFFF] {
                dump(e, tag, &ArmOp::Movw { rd, imm16 });
                dump(e, tag, &ArmOp::Movt { rd, imm16 });
            }
            for addend in [
                0i32,
                1,
                4,
                9,
                0x24,
                0x809,
                0xFFFF,
                0x10000,
                -1,
                -4,
                i32::MIN,
            ] {
                dump(
                    e,
                    tag,
                    &ArmOp::MovwSym {
                        rd,
                        symbol: "__synth_wasm_data".into(),
                        addend,
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::MovtSym {
                        rd,
                        symbol: "__synth_wasm_data".into(),
                        addend,
                    },
                );
            }
            // Shifts by immediate.
            for shift in [0u32, 1, 4, 16, 31, 32, 33, 63, 64] {
                dump(
                    e,
                    tag,
                    &ArmOp::Lsl {
                        rd,
                        rn: Reg::R5,
                        shift,
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::Lsr {
                        rd,
                        rn: Reg::R5,
                        shift,
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::Asr {
                        rd,
                        rn: Reg::R5,
                        shift,
                    },
                );
                dump(
                    e,
                    tag,
                    &ArmOp::Ror {
                        rd,
                        rn: Reg::R5,
                        shift,
                    },
                );
            }
            for &cond in CONDS {
                dump(e, tag, &ArmOp::SetCond { rd, cond });
                dump(
                    e,
                    tag,
                    &ArmOp::SelectMove {
                        rd,
                        rm: Reg::R5,
                        cond,
                    },
                );
            }
        }
        // Loads/stores across offset range, all widths, all addressing modes.
        for &base in REGS {
            for &rt in &[Reg::R0, Reg::R1, Reg::R7, Reg::R8, Reg::R12] {
                for &off in IMMS {
                    for mk in [
                        MemAddr::imm(base, off),
                        MemAddr::reg_imm(base, Reg::R6, off),
                    ] {
                        dump(
                            e,
                            tag,
                            &ArmOp::Ldr {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Str {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Ldrb {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Strb {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Ldrh {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Strh {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Ldrsb {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                        dump(
                            e,
                            tag,
                            &ArmOp::Ldrsh {
                                rd: rt,
                                addr: mk.clone(),
                            },
                        );
                    }
                }
            }
        }
        // Branches with numeric offsets (the #202 family).
        for off in [
            -0x100000i32,
            -0x10000,
            -2048,
            -1025,
            -1024,
            -129,
            -128,
            -1,
            0,
            1,
            127,
            128,
            1022,
            1023,
            2048,
            0x10000,
            0xFFFFF,
        ] {
            dump(e, tag, &ArmOp::BOffset { offset: off });
            for &cond in CONDS {
                dump(e, tag, &ArmOp::BCondOffset { cond, offset: off });
            }
        }
        // Multiplies / divides / bit ops / extends.
        for &rd in &[Reg::R0, Reg::R4, Reg::R8] {
            for &rn in &[Reg::R1, Reg::R7] {
                for &rm in &[Reg::R2, Reg::R8] {
                    dump(e, tag, &ArmOp::Mul { rd, rn, rm });
                    dump(e, tag, &ArmOp::Sdiv { rd, rn, rm });
                    dump(e, tag, &ArmOp::Udiv { rd, rn, rm });
                    dump(
                        e,
                        tag,
                        &ArmOp::Mls {
                            rd,
                            rn,
                            rm,
                            ra: Reg::R3,
                        },
                    );
                    dump(
                        e,
                        tag,
                        &ArmOp::Mla {
                            rd,
                            rn,
                            rm,
                            ra: Reg::R3,
                        },
                    );
                    dump(
                        e,
                        tag,
                        &ArmOp::Umull {
                            rdlo: rd,
                            rdhi: rn,
                            rn: rm,
                            rm: Reg::R3,
                        },
                    );
                }
            }
            dump(e, tag, &ArmOp::Clz { rd, rm: Reg::R5 });
            dump(e, tag, &ArmOp::Rbit { rd, rm: Reg::R5 });
            dump(e, tag, &ArmOp::Sxtb { rd, rm: Reg::R5 });
            dump(e, tag, &ArmOp::Sxth { rd, rm: Reg::R5 });
            dump(
                e,
                tag,
                &ArmOp::LslReg {
                    rd,
                    rn: Reg::R5,
                    rm: Reg::R6,
                },
            );
            dump(
                e,
                tag,
                &ArmOp::LsrReg {
                    rd,
                    rn: Reg::R5,
                    rm: Reg::R6,
                },
            );
            dump(
                e,
                tag,
                &ArmOp::AsrReg {
                    rd,
                    rn: Reg::R5,
                    rm: Reg::R6,
                },
            );
            dump(
                e,
                tag,
                &ArmOp::RorReg {
                    rd,
                    rn: Reg::R5,
                    rm: Reg::R6,
                },
            );
        }
        // i64 composite sequences (multi-instruction emissions).
        for &cond in CONDS {
            dump(
                e,
                tag,
                &ArmOp::I64SetCond {
                    rd: Reg::R0,
                    rn_lo: Reg::R2,
                    rn_hi: Reg::R3,
                    rm_lo: Reg::R4,
                    rm_hi: Reg::R5,
                    cond,
                },
            );
        }
        dump(
            e,
            tag,
            &ArmOp::I64SetCondZ {
                rd: Reg::R0,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
            },
        );
        for op in [
            ArmOp::I64Mul {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            ArmOp::I64Shl {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            ArmOp::I64ShrS {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            ArmOp::I64ShrU {
                rd_lo: Reg::R0,
                rd_hi: Reg::R1,
                rn_lo: Reg::R2,
                rn_hi: Reg::R3,
                rm_lo: Reg::R4,
                rm_hi: Reg::R5,
            },
            ArmOp::Select {
                rd: Reg::R0,
                rval1: Reg::R1,
                rval2: Reg::R2,
                rcond: Reg::R3,
            },
            ArmOp::Bx { rm: Reg::LR },
            ArmOp::Blx { rm: Reg::R3 },
            ArmOp::Nop,
            ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
            },
            ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
            },
        ] {
            dump(e, tag, &op);
        }
        for imm in [0u8, 1, 2, 255] {
            dump(e, tag, &ArmOp::Udf { imm });
        }
    }
}
