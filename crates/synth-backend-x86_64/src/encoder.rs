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

use crate::inst::{AluOp, Cond, Ext, Inst, Reg, ShiftOp, Size};

/// Emit `[REX] opcode... ModRM(11, reg, rm)`.
///
/// The REX prefix is `0100 W R X B`: `R` extends the ModRM reg field, `B` the
/// r/m field. It is emitted only when a bit is set or when `force` asks for a
/// bare `40` — LLVM omits a REX that changes nothing. `force` is for the byte
/// registers `spl, bpl, sil, dil`, which are `ah, ch, dh, bh` without a REX.
fn rex_op_modrm(out: &mut Vec<u8>, w: bool, force: bool, opcode: &[u8], reg: u8, rm: u8) {
    let rex = 0x40 | (u8::from(w) << 3) | (((reg >> 3) & 1) << 2) | ((rm >> 3) & 1);
    if rex != 0x40 || force {
        out.push(rex);
    }
    out.extend_from_slice(opcode);
    out.push(0xC0 | ((reg & 7) << 3) | (rm & 7));
}

/// A byte-register operand that needs a REX prefix to mean the low byte.
fn byte_needs_rex(r: Reg) -> bool {
    (4..8).contains(&r.num())
}

fn w(size: Size) -> bool {
    size == Size::Q
}

/// The opcode of `op r/m, r` (the `MR` direction LLVM prefers for register
/// operands).
fn alu_opcode(op: AluOp) -> u8 {
    match op {
        AluOp::Add => 0x01,
        AluOp::Or => 0x09,
        AluOp::And => 0x21,
        AluOp::Sub => 0x29,
        AluOp::Xor => 0x31,
        AluOp::Cmp => 0x39,
        AluOp::Test => 0x85,
        AluOp::Mov => 0x89,
    }
}

/// The `/n` opcode extension of a `D3` shift.
fn shift_ext(op: ShiftOp) -> u8 {
    match op {
        ShiftOp::Rol => 0,
        ShiftOp::Ror => 1,
        ShiftOp::Shl => 4,
        ShiftOp::Shr => 5,
        ShiftOp::Sar => 7,
    }
}

/// The 4-bit condition number of `0F 9x` / `0F 4x`.
fn cond_num(c: Cond) -> u8 {
    match c {
        Cond::B => 0x2,
        Cond::Ae => 0x3,
        Cond::E => 0x4,
        Cond::Ne => 0x5,
        Cond::Be => 0x6,
        Cond::A => 0x7,
        Cond::L => 0xC,
        Cond::Ge => 0xD,
        Cond::Le => 0xE,
        Cond::G => 0xF,
    }
}

/// `[REX.B] B8+r`, the register in the opcode byte.
fn op_plus_reg(out: &mut Vec<u8>, w: bool, opcode: u8, r: Reg) {
    let rex = 0x40 | (u8::from(w) << 3) | ((r.num() >> 3) & 1);
    if rex != 0x40 {
        out.push(rex);
    }
    out.push(opcode | (r.num() & 7));
}

/// Append the encoding of `inst` to `out`; returns its length.
pub fn encode_into(inst: &Inst, out: &mut Vec<u8>) -> usize {
    let start = out.len();
    match *inst {
        // op r/m, r — LLVM's ADD32rr/ADD64rr and siblings.
        Inst::Alu { op, size, dst, src } => {
            rex_op_modrm(out, w(size), false, &[alu_opcode(op)], src.num(), dst.num());
        }
        // IMUL r, r/m.
        Inst::Imul { size, dst, src } => {
            rex_op_modrm(out, w(size), false, &[0x0F, 0xAF], dst.num(), src.num());
        }
        // D3 /n — shift r/m by cl.
        Inst::ShiftCl { op, size, dst } => {
            rex_op_modrm(out, w(size), false, &[0xD3], shift_ext(op), dst.num());
        }
        // SETcc r/m8, reg field 0.
        Inst::SetCc { cond, dst } => {
            let opcode = [0x0F, 0x90 | cond_num(cond)];
            rex_op_modrm(out, false, byte_needs_rex(dst), &opcode, 0, dst.num());
        }
        // CMOVcc r, r/m.
        Inst::Cmov {
            cond,
            size,
            dst,
            src,
        } => {
            let opcode = [0x0F, 0x40 | cond_num(cond)];
            rex_op_modrm(out, w(size), false, &opcode, dst.num(), src.num());
        }
        // MOVZX / MOVSX / MOVSXD r, r/m.
        Inst::Movx { ext, dst, src } => {
            let opcode: &[u8] = match ext {
                Ext::ZxBL => &[0x0F, 0xB6],
                Ext::SxBL | Ext::SxBQ => &[0x0F, 0xBE],
                Ext::SxWL | Ext::SxWQ => &[0x0F, 0xBF],
                Ext::SxLQ => &[0x63],
            };
            let force = ext.src_is_byte() && byte_needs_rex(src);
            rex_op_modrm(out, w(ext.dst_size()), force, opcode, dst.num(), src.num());
        }
        // MOV r32, imm32.
        Inst::MovImm32 { dst, imm } => {
            op_plus_reg(out, false, 0xB8, dst);
            out.extend_from_slice(&imm.to_le_bytes());
        }
        // MOV r/m64, imm32 (sign-extended).
        Inst::MovImmSx { dst, imm } => {
            rex_op_modrm(out, true, false, &[0xC7], 0, dst.num());
            out.extend_from_slice(&imm.to_le_bytes());
        }
        // MOV r64, imm64.
        Inst::MovAbs { dst, imm } => {
            op_plus_reg(out, true, 0xB8, dst);
            out.extend_from_slice(&imm.to_le_bytes());
        }
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
                let b = encode(&Inst::Alu {
                    op: AluOp::Add,
                    size: Size::L,
                    dst: d,
                    src: s,
                });
                let high = d.num() >= 8 || s.num() >= 8;
                assert_eq!(b.len(), if high { 3 } else { 2 }, "{d:?} {s:?}");
                assert_eq!(b[0] & 0xF0 == 0x40, high, "{d:?} {s:?}");
                // 64-bit: always a REX, with W set.
                let q = encode(&Inst::Alu {
                    op: AluOp::Add,
                    size: Size::Q,
                    dst: d,
                    src: s,
                });
                assert_eq!(q.len(), 3);
                assert_eq!(q[0] & 0xF8, 0x48, "{d:?} {s:?}");
            }
        }
        assert_eq!(encode(&Inst::Ret).len(), 1);
    }

    /// `sil`/`dil`/`spl`/`bpl` carry a REX even with no extension bit, in both
    /// forms that name a byte register.
    #[test]
    fn low_byte_registers_force_a_rex() {
        for &r in &Reg::ALL {
            let set = encode(&Inst::SetCc {
                cond: Cond::E,
                dst: r,
            });
            let zx = encode(&Inst::Movx {
                ext: Ext::ZxBL,
                dst: Reg::Rax,
                src: r,
            });
            let rex = r.num() >= 4;
            assert_eq!(set.len(), if rex { 4 } else { 3 }, "{r:?}");
            assert_eq!(zx.len(), if rex { 4 } else { 3 }, "{r:?}");
            // A word source needs no forced prefix.
            let sw = encode(&Inst::Movx {
                ext: Ext::SxWL,
                dst: Reg::Rax,
                src: r,
            });
            assert_eq!(sw.len(), if r.num() >= 8 { 4 } else { 3 }, "{r:?}");
        }
    }

    #[test]
    fn immediates_have_their_field_width() {
        assert_eq!(
            encode(&Inst::MovImm32 {
                dst: Reg::Rax,
                imm: 1
            })
            .len(),
            5
        );
        assert_eq!(
            encode(&Inst::MovImm32 {
                dst: Reg::R11,
                imm: 1
            })
            .len(),
            6
        );
        assert_eq!(
            encode(&Inst::MovImmSx {
                dst: Reg::Rax,
                imm: -1
            })
            .len(),
            7
        );
        assert_eq!(
            encode(&Inst::MovAbs {
                dst: Reg::R11,
                imm: 1
            })
            .len(),
            10
        );
    }

    #[test]
    fn encode_all_reports_each_length() {
        let insts = [Inst::mov32(Reg::Rax, Reg::R9), Inst::Ret];
        let (bytes, lens) = encode_all(&insts);
        assert_eq!(lens, vec![3, 1]);
        assert_eq!(bytes.len(), 4);
    }
}
