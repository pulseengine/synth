//! The x86-64 encoder: one function per instruction form.
//!
//! Where x86 offers two encodings for one instruction, the encoder adopts
//! LLVM's canonical choice, so `llvm-mc -show-encoding` over the printed AT&T
//! text ([`crate::inst::Inst::att`]) reproduces the bytes exactly. That is the
//! E1 oracle (`tests/encoding_llvm_mc.rs`); the E2/E3 decode oracle
//! (`tests/encoding_iced.rs`) runs inside the required `Test` check.
//!
//! Every instruction's length is a pure function of the instruction: there is
//! no branch relaxation, so there is no size estimator that could drift from
//! the encoder (VCR-X86-001 cost 4).

use crate::inst::{Inst, Reg};

/// REX prefix for a register-to-register form: `0100 W R X B`. Emitted only
/// when some bit is set — `40` alone would change no 32-bit register operand,
/// and LLVM omits it.
fn rex_rr(w: bool, reg: Reg, rm: Reg) -> Option<u8> {
    let r = (reg.num() >> 3) & 1;
    let b = (rm.num() >> 3) & 1;
    let byte = 0x40 | (u8::from(w) << 3) | (r << 2) | b;
    (byte != 0x40).then_some(byte)
}

/// ModRM for a register-direct operand pair: `mod = 11`.
fn modrm_rr(reg: Reg, rm: Reg) -> u8 {
    0xC0 | ((reg.num() & 7) << 3) | (rm.num() & 7)
}

/// `op r/m32, r32` with `rm` the destination and `reg` the source.
fn op_rm32_r32(out: &mut Vec<u8>, opcode: u8, dst: Reg, src: Reg) {
    if let Some(rex) = rex_rr(false, src, dst) {
        out.push(rex);
    }
    out.push(opcode);
    out.push(modrm_rr(src, dst));
}

/// Append the encoding of `inst` to `out`; returns its length.
pub fn encode_into(inst: &Inst, out: &mut Vec<u8>) -> usize {
    let start = out.len();
    match *inst {
        // MOV r/m32, r32 — LLVM's MOV32rr.
        Inst::MovRR32 { dst, src } => op_rm32_r32(out, 0x89, dst, src),
        // ADD r/m32, r32 — LLVM's ADD32rr.
        Inst::AddRR32 { dst, src } => op_rm32_r32(out, 0x01, dst, src),
        // RET (near).
        Inst::Ret => out.push(0xC3),
    }
    out.len() - start
}

/// The encoding of one instruction.
pub fn encode(inst: &Inst) -> Vec<u8> {
    let mut v = Vec::new();
    encode_into(inst, &mut v);
    v
}

/// Encode a sequence: the bytes, and each instruction's length in order (the
/// decode oracle requires every decoded length to equal the reported one).
pub fn encode_all(insts: &[Inst]) -> (Vec<u8>, Vec<usize>) {
    let mut bytes = Vec::new();
    let lens = insts.iter().map(|i| encode_into(i, &mut bytes)).collect();
    (bytes, lens)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Structural properties only. The byte VALUES are checked against LLVM
    /// and iced-x86 in the integration tests, never against literals here.
    #[test]
    fn rex_appears_exactly_when_a_high_register_is_named() {
        for &d in &Reg::ALL {
            for &s in &Reg::ALL {
                let b = encode(&Inst::AddRR32 { dst: d, src: s });
                let high = d.num() >= 8 || s.num() >= 8;
                assert_eq!(b.len(), if high { 3 } else { 2 }, "{d:?} {s:?}");
                assert_eq!(b[0] & 0xF0 == 0x40, high, "{d:?} {s:?}");
            }
        }
        assert_eq!(encode(&Inst::Ret).len(), 1);
    }

    #[test]
    fn encode_all_reports_each_length() {
        let insts = [
            Inst::MovRR32 {
                dst: Reg::Rax,
                src: Reg::R9,
            },
            Inst::Ret,
        ];
        let (bytes, lens) = encode_all(&insts);
        assert_eq!(lens, vec![3, 1]);
        assert_eq!(bytes.len(), 4);
    }
}
