//! The E1/E2 population: the whole operand space of every instruction FORM the
//! x86-64 encoder has. Shared by `encoding_llvm_mc.rs` (E1) and
//! `encoding_iced.rs` (E2), so the two oracles read the same enumeration.
//!
//! Registers: all 16 (16 x 16 for two-register forms), at each operand size.
//! Conditions: all ten the instruction type has. Immediates: boundary values
//! of each immediate field.

use synth_backend_x86_64::inst::{AluOp, Cond, Ext, ImmOp, Inst, Mem, Reg, ShiftOp, Size};

/// `movl $imm32`.
pub const IMM32: [u32; 8] = [
    0,
    1,
    0x7F,
    0x80,
    0x7FFF_FFFF,
    0x8000_0000,
    0xDEAD_BEEF,
    0xFFFF_FFFF,
];

/// `movq $imm32` (sign-extended).
pub const IMM_SX: [i32; 8] = [0, 1, 0x7F, -1, -128, -129, i32::MAX, i32::MIN];

/// `movabsq $imm64`.
pub const IMM64: [u64; 8] = [
    1,
    0x8000_0000,
    0x1_0000_0000,
    0x1122_3344_5566_7788,
    0x7FFF_FFFF_FFFF_FFFF,
    0x8000_0000_0000_0000,
    0xFFFF_FFFF_7FFF_FFFF,
    u64::MAX,
];

/// `op $imm, r`: both sides of the 8-bit boundary (where the encoding changes
/// from `83 ib` to `81 id` or the accumulator short form) and both ends.
pub const IMM_ALU: [i32; 10] = [
    0,
    1,
    0x7F,
    0x80,
    -1,
    -128,
    -129,
    0x1234_5678,
    i32::MAX,
    i32::MIN,
];

/// Memory displacements: zero (no displacement byte, except with `rbp`/`r13`),
/// both sides of the 8-bit boundary, and both ends.
pub const DISP: [i32; 9] = [0, 8, -8, 0x7F, -0x80, 0x80, -0x81, i32::MAX, i32::MIN];

/// `jCC rel32` displacements (relative to the end of the instruction).
pub const REL: [i32; 8] = [0, 2, 0x7F, 0x80, 0x1234_5678, -6, -0x80, i32::MAX - 6];

/// The forms `llvm-mc -show-encoding` prints with a FIXUP instead of bytes:
/// the branches, `jCC` and (lane X5) `jmp`. E1 assembles these to an object
/// and reads `.text` back. (Unused by the iced test, which shares this
/// module.)
#[allow(dead_code)]
pub fn is_branch(i: &Inst) -> bool {
    matches!(i, Inst::Jcc { .. } | Inst::Jmp { .. })
}

/// The number of forms [`all_forms`] must enumerate, as a literal.
/// Lanes X1-X2 (11,969): Alu 8 x 2 x 256; Imul 2 x 256; ShiftCl 5 x 2 x 16;
/// SetCc 10 x 16; Cmov 10 x 2 x 256; Movx 6 x 256; three immediate moves,
/// 16 x 8 each; ret.
/// Lanes X3-X4 (12,339): Load and Store 2 x (2 sizes x 16 registers x 16
/// bases x 9 displacements) = 9,216 — every base, so the `rsp`/`r12` (SIB)
/// and `rbp`/`r13` (forced displacement) special cases are in it; AluImm
/// 6 x 2 x 16 x 10 = 1,920; Push and Pop 2 x 16; Cdq 2; Div 2 x 2 x 16;
/// BitScan 2 x 2 x 256; Jcc 10 x 8; ud2.
/// Lane X5 (8): `jmp rel32` at the 8 displacements of [`REL`].
pub const FORM_COUNT: usize = 11_969 + 9_216 + 1_920 + 32 + 2 + 64 + 1_024 + 80 + 1 + 8;

pub fn all_forms() -> Vec<Inst> {
    let mut v = Vec::new();
    for &dst in &Reg::ALL {
        for &src in &Reg::ALL {
            for size in Size::ALL {
                for op in AluOp::ALL {
                    v.push(Inst::Alu { op, size, dst, src });
                }
                v.push(Inst::Imul { size, dst, src });
                for cond in Cond::ALL {
                    v.push(Inst::Cmov {
                        cond,
                        size,
                        dst,
                        src,
                    });
                }
            }
            for ext in Ext::ALL {
                v.push(Inst::Movx { ext, dst, src });
            }
        }
        for size in Size::ALL {
            for op in ShiftOp::ALL {
                v.push(Inst::ShiftCl { op, size, dst });
            }
        }
        for cond in Cond::ALL {
            v.push(Inst::SetCc { cond, dst });
        }
        for imm in IMM32 {
            v.push(Inst::MovImm32 { dst, imm });
        }
        for imm in IMM_SX {
            v.push(Inst::MovImmSx { dst, imm });
        }
        for imm in IMM64 {
            v.push(Inst::MovAbs { dst, imm });
        }
    }
    // Lanes X3-X4.
    for &r in &Reg::ALL {
        for &base in &Reg::ALL {
            for size in Size::ALL {
                for disp in DISP {
                    let mem = Mem { base, disp };
                    v.push(Inst::Load { size, dst: r, mem });
                    v.push(Inst::Store { size, src: r, mem });
                }
                for reverse in [false, true] {
                    v.push(Inst::BitScan {
                        reverse,
                        size,
                        dst: r,
                        src: base,
                    });
                }
            }
        }
        for size in Size::ALL {
            for op in ImmOp::ALL {
                for imm in IMM_ALU {
                    v.push(Inst::AluImm {
                        op,
                        size,
                        dst: r,
                        imm,
                    });
                }
            }
            for signed in [false, true] {
                v.push(Inst::Div {
                    signed,
                    size,
                    src: r,
                });
            }
        }
        v.push(Inst::Push { reg: r });
        v.push(Inst::Pop { reg: r });
    }
    for size in Size::ALL {
        v.push(Inst::Cdq { size });
    }
    for cond in Cond::ALL {
        for rel in REL {
            v.push(Inst::Jcc { cond, rel });
        }
    }
    for rel in REL {
        v.push(Inst::Jmp { rel });
    }
    v.push(Inst::Ud2);
    v.push(Inst::Ret);
    v
}
