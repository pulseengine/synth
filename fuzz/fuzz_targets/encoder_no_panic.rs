//! Fuzz target: ARM encoder must never panic.
//!
//! Run with: `cargo +nightly fuzz run encoder_no_panic -- -max_total_time=60`
//!
//! ## What this catches
//!
//! `ArmEncoder::encode(&ArmOp)` is called on every instruction synth emits.
//! Its only legitimate outcomes are:
//!   * `Ok(Vec<u8>)` — bytes for the instruction
//!   * `Err(synth_core::Error)` — typed error
//!
//! Anything else (panic, integer overflow under arithmetic_overflow=panic,
//! out-of-bounds array index) is a crash. This harness drives randomly-
//! parametrised but well-typed `ArmOp` values across every encoding mode
//! (ARM32, Thumb-2, Thumb-2+VFP) and asserts panic-freedom.
//!
//! Out of scope: differential check vs. a reference disassembler (issue #82
//! lists this as a future extension; capstone is not currently a dep).

#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::fuzz_target;
use synth_backend::ArmEncoder;
use synth_core::target::FPUPrecision;
use synth_synthesis::{ArmOp, Condition, MemAddr, Operand2, Reg, ShiftType};

#[derive(Arbitrary, Debug, Clone, Copy)]
enum ArbReg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    SP,
    LR,
    PC,
}

impl ArbReg {
    fn into_reg(self) -> Reg {
        match self {
            Self::R0 => Reg::R0,
            Self::R1 => Reg::R1,
            Self::R2 => Reg::R2,
            Self::R3 => Reg::R3,
            Self::R4 => Reg::R4,
            Self::R5 => Reg::R5,
            Self::R6 => Reg::R6,
            Self::R7 => Reg::R7,
            Self::R8 => Reg::R8,
            Self::R9 => Reg::R9,
            Self::R10 => Reg::R10,
            Self::R11 => Reg::R11,
            Self::R12 => Reg::R12,
            Self::SP => Reg::SP,
            Self::LR => Reg::LR,
            Self::PC => Reg::PC,
        }
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
#[allow(clippy::upper_case_acronyms)] // ARM shift mnemonics
enum ArbShift {
    LSL,
    LSR,
    ASR,
    ROR,
}

impl ArbShift {
    fn into_st(self) -> ShiftType {
        match self {
            Self::LSL => ShiftType::LSL,
            Self::LSR => ShiftType::LSR,
            Self::ASR => ShiftType::ASR,
            Self::ROR => ShiftType::ROR,
        }
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
#[allow(clippy::upper_case_acronyms)] // ARM condition-code mnemonics
enum ArbCond {
    EQ,
    NE,
    LT,
    LE,
    GT,
    GE,
    LO,
    LS,
    HI,
    HS,
}

impl ArbCond {
    fn into_cond(self) -> Condition {
        match self {
            Self::EQ => Condition::EQ,
            Self::NE => Condition::NE,
            Self::LT => Condition::LT,
            Self::LE => Condition::LE,
            Self::GT => Condition::GT,
            Self::GE => Condition::GE,
            Self::LO => Condition::LO,
            Self::LS => Condition::LS,
            Self::HI => Condition::HI,
            Self::HS => Condition::HS,
        }
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum ArbOperand2 {
    Imm(i32),
    Reg(ArbReg),
    RegShift(ArbReg, ArbShift, u32),
}

impl ArbOperand2 {
    fn into_op2(self) -> Operand2 {
        match self {
            Self::Imm(i) => Operand2::Imm(i),
            Self::Reg(r) => Operand2::Reg(r.into_reg()),
            Self::RegShift(rm, st, amt) => Operand2::RegShift {
                rm: rm.into_reg(),
                shift: st.into_st(),
                amount: amt,
            },
        }
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
struct ArbMem {
    base: ArbReg,
    offset: i32,
    offset_reg: Option<ArbReg>,
}

impl ArbMem {
    fn into_addr(self) -> MemAddr {
        MemAddr {
            base: self.base.into_reg(),
            offset: self.offset,
            offset_reg: self.offset_reg.map(|r| r.into_reg()),
        }
    }
}

/// Curated set of `ArmOp` shapes that exercise the most encoder corners.
///
/// We deliberately enumerate the encoder-rich variants (data-processing
/// with all three Operand2 flavours, loads/stores with all three MemAddr
/// flavours, immediate-shifts with arbitrary shift amounts including
/// "0" and ">31", branch ops, etc.). Variants encoded with simple passthrough
/// (e.g. Nop) are present too but are weighted lower by frequency in the
/// `Arbitrary` derive.
#[derive(Arbitrary, Debug)]
enum FuzzInst {
    Add(ArbReg, ArbReg, ArbOperand2),
    Sub(ArbReg, ArbReg, ArbOperand2),
    Adds(ArbReg, ArbReg, ArbOperand2),
    Adc(ArbReg, ArbReg, ArbOperand2),
    Subs(ArbReg, ArbReg, ArbOperand2),
    Sbc(ArbReg, ArbReg, ArbOperand2),
    Mul(ArbReg, ArbReg, ArbReg),
    And(ArbReg, ArbReg, ArbOperand2),
    Orr(ArbReg, ArbReg, ArbOperand2),
    Eor(ArbReg, ArbReg, ArbOperand2),
    Lsl(ArbReg, ArbReg, u32),
    Lsr(ArbReg, ArbReg, u32),
    Asr(ArbReg, ArbReg, u32),
    Ror(ArbReg, ArbReg, u32),
    Mov(ArbReg, ArbOperand2),
    Mvn(ArbReg, ArbOperand2),
    Movw(ArbReg, u16),
    Movt(ArbReg, u16),
    Cmp(ArbReg, ArbOperand2),
    Cmn(ArbReg, ArbOperand2),
    Ldr(ArbReg, ArbMem),
    Str(ArbReg, ArbMem),
    Ldrb(ArbReg, ArbMem),
    Ldrh(ArbReg, ArbMem),
    Strb(ArbReg, ArbMem),
    Strh(ArbReg, ArbMem),
    Clz(ArbReg, ArbReg),
    Rbit(ArbReg, ArbReg),
    Sxtb(ArbReg, ArbReg),
    Sxth(ArbReg, ArbReg),
    Bx(ArbReg),
    BCondOffset(ArbCond, i32),
    BOffset(i32),
    Nop,
    Udf(u8),
}

impl FuzzInst {
    fn into_op(self) -> ArmOp {
        match self {
            Self::Add(rd, rn, op2) => ArmOp::Add {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Sub(rd, rn, op2) => ArmOp::Sub {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Adds(rd, rn, op2) => ArmOp::Adds {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Adc(rd, rn, op2) => ArmOp::Adc {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Subs(rd, rn, op2) => ArmOp::Subs {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Sbc(rd, rn, op2) => ArmOp::Sbc {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Mul(rd, rn, rm) => ArmOp::Mul {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                rm: rm.into_reg(),
            },
            Self::And(rd, rn, op2) => ArmOp::And {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Orr(rd, rn, op2) => ArmOp::Orr {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Eor(rd, rn, op2) => ArmOp::Eor {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Lsl(rd, rn, shift) => ArmOp::Lsl {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                shift,
            },
            Self::Lsr(rd, rn, shift) => ArmOp::Lsr {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                shift,
            },
            Self::Asr(rd, rn, shift) => ArmOp::Asr {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                shift,
            },
            Self::Ror(rd, rn, shift) => ArmOp::Ror {
                rd: rd.into_reg(),
                rn: rn.into_reg(),
                shift,
            },
            Self::Mov(rd, op2) => ArmOp::Mov {
                rd: rd.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Mvn(rd, op2) => ArmOp::Mvn {
                rd: rd.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Movw(rd, imm16) => ArmOp::Movw {
                rd: rd.into_reg(),
                imm16,
            },
            Self::Movt(rd, imm16) => ArmOp::Movt {
                rd: rd.into_reg(),
                imm16,
            },
            Self::Cmp(rn, op2) => ArmOp::Cmp {
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Cmn(rn, op2) => ArmOp::Cmn {
                rn: rn.into_reg(),
                op2: op2.into_op2(),
            },
            Self::Ldr(rd, addr) => ArmOp::Ldr {
                rd: rd.into_reg(),
                addr: addr.into_addr(),
            },
            Self::Str(rd, addr) => ArmOp::Str {
                rd: rd.into_reg(),
                addr: addr.into_addr(),
            },
            Self::Ldrb(rd, addr) => ArmOp::Ldrb {
                rd: rd.into_reg(),
                addr: addr.into_addr(),
            },
            Self::Ldrh(rd, addr) => ArmOp::Ldrh {
                rd: rd.into_reg(),
                addr: addr.into_addr(),
            },
            Self::Strb(rd, addr) => ArmOp::Strb {
                rd: rd.into_reg(),
                addr: addr.into_addr(),
            },
            Self::Strh(rd, addr) => ArmOp::Strh {
                rd: rd.into_reg(),
                addr: addr.into_addr(),
            },
            Self::Clz(rd, rm) => ArmOp::Clz {
                rd: rd.into_reg(),
                rm: rm.into_reg(),
            },
            Self::Rbit(rd, rm) => ArmOp::Rbit {
                rd: rd.into_reg(),
                rm: rm.into_reg(),
            },
            Self::Sxtb(rd, rm) => ArmOp::Sxtb {
                rd: rd.into_reg(),
                rm: rm.into_reg(),
            },
            Self::Sxth(rd, rm) => ArmOp::Sxth {
                rd: rd.into_reg(),
                rm: rm.into_reg(),
            },
            Self::Bx(rm) => ArmOp::Bx { rm: rm.into_reg() },
            Self::BCondOffset(cond, offset) => ArmOp::BCondOffset {
                cond: cond.into_cond(),
                offset,
            },
            Self::BOffset(offset) => ArmOp::BOffset { offset },
            Self::Nop => ArmOp::Nop,
            Self::Udf(imm) => ArmOp::Udf { imm },
        }
    }
}

fuzz_target!(|raw: &[u8]| {
    let mut u = Unstructured::new(raw);
    let inst = match FuzzInst::arbitrary(&mut u) {
        Ok(v) => v,
        Err(_) => return,
    };
    let op = inst.into_op();

    // Three encoder modes — exercise each. The encoder must return
    // either Ok(bytes) or Err(_) on every input; a panic is a crash.
    for encoder in [
        ArmEncoder::new_arm32(),
        ArmEncoder::new_thumb2(),
        ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Single)),
        ArmEncoder::new_thumb2_with_fpu(Some(FPUPrecision::Double)),
    ] {
        let _ = encoder.encode(&op);
    }
});
