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

use crate::inst::{AluOp, Cond, Ext, ImmOp, Inst, Mem, Reg, ShiftOp, Size};

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

/// Emit `[REX] opcode... ModRM SIB? disp?` for the memory operand
/// `disp(%base)`, the register operand in the ModRM reg field.
///
/// LLVM's canonical displacement width: none when the displacement is zero
/// (except with `rbp`/`r13` as the base, whose mod=00 encoding means
/// "no base"), 8 bits when it fits, else 32. A base of `rsp`/`r12` takes the
/// SIB byte `24` (no index, base in the SIB).
fn rex_op_mem(out: &mut Vec<u8>, w: bool, opcode: &[u8], reg: u8, mem: Mem) {
    let base = mem.base.num();
    let rex = 0x40 | (u8::from(w) << 3) | (((reg >> 3) & 1) << 2) | ((base >> 3) & 1);
    if rex != 0x40 {
        out.push(rex);
    }
    out.extend_from_slice(opcode);
    let disp8 = i8::try_from(mem.disp).ok();
    let mode: u8 = if mem.disp == 0 && base & 7 != 5 {
        0
    } else if disp8.is_some() {
        1
    } else {
        2
    };
    out.push((mode << 6) | ((reg & 7) << 3) | (base & 7));
    if base & 7 == 4 {
        out.push(0x24);
    }
    match (mode, disp8) {
        (0, _) => {}
        (1, Some(d)) => out.push(d as u8),
        _ => out.extend_from_slice(&mem.disp.to_le_bytes()),
    }
}

/// The `/n` opcode extension of `83`/`81`; the accumulator short form is
/// `(n << 3) | 5`.
fn imm_ext(op: ImmOp) -> u8 {
    match op {
        ImmOp::Add => 0,
        ImmOp::Or => 1,
        ImmOp::And => 4,
        ImmOp::Sub => 5,
        ImmOp::Xor => 6,
        ImmOp::Cmp => 7,
    }
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
        // MOV r, r/m.
        Inst::Load { size, dst, mem } => rex_op_mem(out, w(size), &[0x8B], dst.num(), mem),
        // MOV r/m, r.
        Inst::Store { size, src, mem } => rex_op_mem(out, w(size), &[0x89], src.num(), mem),
        // op r/m, imm: LLVM takes the sign-extended 8-bit form when the
        // immediate fits, else the accumulator short form for rax, else
        // `81 /n id`.
        Inst::AluImm { op, size, dst, imm } => {
            let n = imm_ext(op);
            if let Ok(i) = i8::try_from(imm) {
                rex_op_modrm(out, w(size), false, &[0x83], n, dst.num());
                out.push(i as u8);
            } else if dst == Reg::Rax {
                if w(size) {
                    out.push(0x48);
                }
                out.push((n << 3) | 5);
                out.extend_from_slice(&imm.to_le_bytes());
            } else {
                rex_op_modrm(out, w(size), false, &[0x81], n, dst.num());
                out.extend_from_slice(&imm.to_le_bytes());
            }
        }
        // PUSH r64 / POP r64: 64-bit by default, no REX.W.
        Inst::Push { reg } => op_plus_reg(out, false, 0x50, reg),
        Inst::Pop { reg } => op_plus_reg(out, false, 0x58, reg),
        // CDQ / CQO.
        Inst::Cdq { size } => {
            if w(size) {
                out.push(0x48);
            }
            out.push(0x99);
        }
        // DIV / IDIV r/m.
        Inst::Div { signed, size, src } => {
            rex_op_modrm(
                out,
                w(size),
                false,
                &[0xF7],
                6 | u8::from(signed),
                src.num(),
            );
        }
        // BSF / BSR r, r/m. NEVER with an F3 prefix: that is tzcnt/lzcnt.
        Inst::BitScan {
            reverse,
            size,
            dst,
            src,
        } => {
            let opcode = [0x0F, 0xBC | u8::from(reverse)];
            rex_op_modrm(out, w(size), false, &opcode, dst.num(), src.num());
        }
        // Jcc rel32.
        Inst::Jcc { cond, rel } => {
            out.extend_from_slice(&[0x0F, 0x80 | cond_num(cond)]);
            out.extend_from_slice(&rel.to_le_bytes());
        }
        // UD2.
        Inst::Ud2 => out.extend_from_slice(&[0x0F, 0x0B]),
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

    /// Structure only: the displacement width follows the value, `rsp`/`r12`
    /// add a SIB byte, and `rbp`/`r13` never use the no-displacement mode.
    #[test]
    fn memory_operands_pick_the_shortest_displacement() {
        let len = |base, disp| {
            encode(&Inst::Load {
                size: Size::L,
                dst: Reg::Rax,
                mem: Mem { base, disp },
            })
            .len()
        };
        for &base in &Reg::ALL {
            let rex = usize::from(base.num() >= 8);
            let sib = usize::from(base.num() & 7 == 4);
            let zero = if base.num() & 7 == 5 { 1 } else { 0 };
            assert_eq!(len(base, 0), 2 + rex + sib + zero, "{base:?}");
            for d in [1, 127, -128] {
                assert_eq!(len(base, d), 3 + rex + sib, "{base:?} {d}");
            }
            for d in [128, -129, i32::MAX, i32::MIN] {
                assert_eq!(len(base, d), 6 + rex + sib, "{base:?} {d}");
            }
        }
    }

    /// A branch is 6 bytes whatever its displacement; the trap is 2.
    #[test]
    fn branches_have_one_length() {
        for rel in [0, 2, 127, 128, -1, i32::MAX, i32::MIN] {
            for cond in Cond::ALL {
                assert_eq!(encode(&Inst::Jcc { cond, rel }).len(), 6);
            }
        }
        assert_eq!(encode(&Inst::Ud2).len(), 2);
    }

    #[test]
    fn encode_all_reports_each_length() {
        let insts = [Inst::mov32(Reg::Rax, Reg::R9), Inst::Ret];
        let (bytes, lens) = encode_all(&insts);
        assert_eq!(lens, vec![3, 1]);
        assert_eq!(bytes.len(), 4);
    }
}
