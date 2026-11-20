//! The E1/E2 population: the whole operand space of every instruction FORM the
//! x86-64 encoder has. Shared by `encoding_llvm_mc.rs` (E1) and
//! `encoding_iced.rs` (E2), so the two oracles read the same enumeration.
//!
//! Registers: all 16 (16 x 16 for two-register forms), at each operand size.
//! Conditions: all ten the instruction type has. Immediates: boundary values
//! of each immediate field.

use synth_backend_x86_64::inst::{AluOp, Cond, Ext, Inst, Reg, ShiftOp, Size};

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

/// The number of forms [`all_forms`] must enumerate, as a literal:
/// Alu 8 x 2 x 256 + Imul 2 x 256 + ShiftCl 5 x 2 x 16 + SetCc 10 x 16 +
/// Cmov 10 x 2 x 256 + Movx 6 x 256 + three immediate moves 16 x 8 each + ret.
pub const FORM_COUNT: usize = 11_969;

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
    v.push(Inst::Ret);
    v
}
