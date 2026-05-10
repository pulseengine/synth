//! WASM → RV32 instruction selector — skeleton.
//!
//! Today this only supports a small handful of i32 patterns sufficient for
//! "hello-world" smoke testing. The full lowering (matching feature parity
//! with the ARM selector in `synth-synthesis::instruction_selector`) is the
//! Track B2 deliverable.
//!
//! Why a skeleton selector here and not in `synth-synthesis`?
//! `synth-synthesis::instruction_selector` is currently 10 KLoC of ARM-specific
//! lowering; carving out a parallel `select_riscv` there is a separate refactor.
//! Until that's done, RISC-V's selector lives here so it can grow alongside
//! the encoder and ELF builder. The selector module will move once it
//! achieves feature parity (target: end of B2).

use crate::register::Reg;
use crate::riscv_op::RiscVOp;
use synth_core::wasm_op::WasmOp;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SelectorError {
    #[error("unsupported wasm op for RV32 skeleton: {0:?}")]
    Unsupported(WasmOp),

    #[error("invalid program — stack underflow at op {0:?}")]
    StackUnderflow(WasmOp),

    #[error("immediate {value} too large for {context}")]
    ImmediateTooLarge { value: i64, context: &'static str },
}

/// Output of the skeleton selector.
pub struct RiscVSelection {
    pub ops: Vec<RiscVOp>,
}

/// Lower a flat sequence of WASM ops to RV32 ops using a tiny stack-based
/// selector. This handles only:
///   - `local.get N` (params 0..3 map to a0..a3)
///   - `local.set N` for the same
///   - `i32.const`
///   - `i32.add`, `i32.sub`, `i32.mul`
///   - `i32.and`, `i32.or`, `i32.xor`
///   - `i32.eqz`
///   - `return`
///
/// Anything else returns `SelectorError::Unsupported`. The full selector
/// (with control flow, loads/stores, comparisons, division, i64) is B2.
pub fn select_simple(
    wasm_ops: &[WasmOp],
    num_params: u32,
) -> Result<RiscVSelection, SelectorError> {
    let mut out = Vec::new();

    // Virtual stack: each entry is the RV32 register holding that wasm value.
    // We use a0..a7 as both arg-in and short-lived temporaries here.
    // (Real selector will use a vreg allocator.)
    let mut vstack: Vec<Reg> = Vec::new();

    // Argument registers a0..a7 (capped at 8 — anything beyond would spill).
    let arg_regs: Vec<Reg> = Reg::arg_regs(num_params as usize);

    // Tracks the next free temporary register. For the skeleton we do
    // round-robin among t0..t6 — the real allocator will be smarter.
    let temps = [Reg::T0, Reg::T1, Reg::T2, Reg::T3, Reg::T4, Reg::T5];
    let mut next_temp = 0usize;
    let mut alloc_temp = || {
        let r = temps[next_temp % temps.len()];
        next_temp += 1;
        r
    };

    for op in wasm_ops {
        match op {
            WasmOp::LocalGet(idx) => {
                let src = if (*idx as usize) < arg_regs.len() {
                    arg_regs[*idx as usize]
                } else {
                    return Err(SelectorError::Unsupported(op.clone()));
                };
                let dst = alloc_temp();
                // mv dst, src  (= addi dst, src, 0)
                out.push(RiscVOp::Addi {
                    rd: dst,
                    rs1: src,
                    imm: 0,
                });
                vstack.push(dst);
            }
            WasmOp::LocalSet(idx) => {
                let src = vstack
                    .pop()
                    .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
                let dst = if (*idx as usize) < arg_regs.len() {
                    arg_regs[*idx as usize]
                } else {
                    return Err(SelectorError::Unsupported(op.clone()));
                };
                out.push(RiscVOp::Addi {
                    rd: dst,
                    rs1: src,
                    imm: 0,
                });
            }
            WasmOp::I32Const(v) => {
                let dst = alloc_temp();
                emit_load_imm(&mut out, dst, *v);
                vstack.push(dst);
            }
            WasmOp::I32Add => emit_binop(&mut out, &mut vstack, op, |rd, rs1, rs2| RiscVOp::Add {
                rd,
                rs1,
                rs2,
            })?,
            WasmOp::I32Sub => emit_binop(&mut out, &mut vstack, op, |rd, rs1, rs2| RiscVOp::Sub {
                rd,
                rs1,
                rs2,
            })?,
            WasmOp::I32Mul => emit_binop(&mut out, &mut vstack, op, |rd, rs1, rs2| RiscVOp::Mul {
                rd,
                rs1,
                rs2,
            })?,
            WasmOp::I32And => emit_binop(&mut out, &mut vstack, op, |rd, rs1, rs2| RiscVOp::And {
                rd,
                rs1,
                rs2,
            })?,
            WasmOp::I32Or => emit_binop(&mut out, &mut vstack, op, |rd, rs1, rs2| RiscVOp::Or {
                rd,
                rs1,
                rs2,
            })?,
            WasmOp::I32Xor => emit_binop(&mut out, &mut vstack, op, |rd, rs1, rs2| RiscVOp::Xor {
                rd,
                rs1,
                rs2,
            })?,
            WasmOp::I32Eqz => {
                // sltiu rd, src, 1  → rd = (src == 0) ? 1 : 0
                let src = vstack
                    .pop()
                    .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
                let dst = alloc_temp();
                out.push(RiscVOp::Sltiu {
                    rd: dst,
                    rs1: src,
                    imm: 1,
                });
                vstack.push(dst);
            }
            WasmOp::Return | WasmOp::End => {
                // Move top-of-stack to a0 if it isn't already, then return.
                if let Some(&top) = vstack.last()
                    && top != Reg::A0
                {
                    out.push(RiscVOp::Addi {
                        rd: Reg::A0,
                        rs1: top,
                        imm: 0,
                    });
                }
                out.push(RiscVOp::Jalr {
                    rd: Reg::ZERO,
                    rs1: Reg::RA,
                    imm: 0,
                });
                return Ok(RiscVSelection { ops: out });
            }
            other => return Err(SelectorError::Unsupported(other.clone())),
        }
    }

    // No explicit Return/End → emit one
    if let Some(&top) = vstack.last()
        && top != Reg::A0
    {
        out.push(RiscVOp::Addi {
            rd: Reg::A0,
            rs1: top,
            imm: 0,
        });
    }
    out.push(RiscVOp::Jalr {
        rd: Reg::ZERO,
        rs1: Reg::RA,
        imm: 0,
    });
    Ok(RiscVSelection { ops: out })
}

fn emit_binop<F>(
    out: &mut Vec<RiscVOp>,
    vstack: &mut Vec<Reg>,
    op: &WasmOp,
    build: F,
) -> Result<(), SelectorError>
where
    F: FnOnce(Reg, Reg, Reg) -> RiscVOp,
{
    let rs2 = vstack
        .pop()
        .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
    let rs1 = vstack
        .pop()
        .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
    let rd = rs1; // overwrite the first source — temporary aliasing is fine for skeleton
    out.push(build(rd, rs1, rs2));
    vstack.push(rd);
    Ok(())
}

/// Materialize a 32-bit immediate into `rd` using `lui + addi` when needed.
fn emit_load_imm(out: &mut Vec<RiscVOp>, rd: Reg, value: i32) {
    if (-2048..=2047).contains(&value) {
        // Single addi from zero.
        out.push(RiscVOp::Addi {
            rd,
            rs1: Reg::ZERO,
            imm: value,
        });
        return;
    }
    // lui rd, hi20; addi rd, rd, lo12  (with carry from lo12 sign extension)
    let value_u = value as u32;
    let lo12 = (value_u & 0xFFF) as i32;
    // If lo12 sign-extends negative, bump hi20 by 1 to compensate.
    let lo12_signed = if lo12 >= 0x800 { lo12 - 0x1000 } else { lo12 };
    let hi20 = (value_u.wrapping_sub(lo12_signed as u32)) >> 12;
    out.push(RiscVOp::Lui {
        rd,
        imm20: hi20 & 0xFFFFF,
    });
    if lo12_signed != 0 {
        out.push(RiscVOp::Addi {
            rd,
            rs1: rd,
            imm: lo12_signed,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_two_params() {
        // (param i32 i32) → local.get 0, local.get 1, i32.add, end
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let sel = select_simple(&ops, 2).unwrap();

        // Expect:
        //   addi t0, a0, 0       (LocalGet 0)
        //   addi t1, a1, 0       (LocalGet 1)
        //   add  t0, t0, t1       (I32Add)
        //   addi a0, t0, 0        (End: move result to a0)
        //   jalr zero, 0(ra)      (return)
        assert!(matches!(
            sel.ops[0],
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::A0,
                imm: 0
            }
        ));
        assert!(matches!(
            sel.ops[1],
            RiscVOp::Addi {
                rd: Reg::T1,
                rs1: Reg::A1,
                imm: 0
            }
        ));
        assert!(matches!(
            sel.ops[2],
            RiscVOp::Add {
                rd: Reg::T0,
                rs1: Reg::T0,
                rs2: Reg::T1
            }
        ));
        // Last op is the return.
        assert!(matches!(
            sel.ops.last().unwrap(),
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0
            }
        ));
    }

    #[test]
    fn const_then_eqz() {
        // i32.const 0, i32.eqz, end  → returns 1
        let ops = vec![WasmOp::I32Const(0), WasmOp::I32Eqz, WasmOp::End];
        let sel = select_simple(&ops, 0).unwrap();
        // First instruction is `addi rd, zero, 0` (small immediate → no LUI)
        assert!(matches!(
            sel.ops[0],
            RiscVOp::Addi {
                rs1: Reg::ZERO,
                imm: 0,
                ..
            }
        ));
        // The Eqz is sltiu rd, src, 1
        assert!(matches!(sel.ops[1], RiscVOp::Sltiu { imm: 1, .. }));
    }

    #[test]
    fn large_constant_uses_lui_addi() {
        // i32.const 0x12345678
        let ops = vec![WasmOp::I32Const(0x12345678), WasmOp::End];
        let sel = select_simple(&ops, 0).unwrap();
        // First should be LUI (high 20 bits = 0x12345 since lo12=0x678 doesn't sign-extend)
        match &sel.ops[0] {
            RiscVOp::Lui { imm20, .. } => assert_eq!(*imm20, 0x12345),
            other => panic!("expected Lui, got {:?}", other),
        }
        match &sel.ops[1] {
            RiscVOp::Addi { imm, .. } => assert_eq!(*imm, 0x678),
            other => panic!("expected Addi, got {:?}", other),
        }
    }

    #[test]
    fn negative_lo12_carry() {
        // i32.const 0x12345FFF — lo12 sign-extends as -1, so hi20 must bump by 1
        let ops = vec![WasmOp::I32Const(0x12345FFFu32 as i32), WasmOp::End];
        let sel = select_simple(&ops, 0).unwrap();
        match &sel.ops[0] {
            RiscVOp::Lui { imm20, .. } => assert_eq!(*imm20, 0x12346, "hi20 must compensate"),
            other => panic!("expected Lui, got {:?}", other),
        }
        match &sel.ops[1] {
            RiscVOp::Addi { imm, .. } => assert_eq!(*imm, -1),
            other => panic!("expected Addi -1, got {:?}", other),
        }
    }

    #[test]
    fn unsupported_op_errors() {
        let ops = vec![WasmOp::F32Const(1.0), WasmOp::End];
        let r = select_simple(&ops, 0);
        assert!(matches!(r, Err(SelectorError::Unsupported(_))));
    }
}
