//! The x86-64 instruction selector — lane X1 (RQ-91-X86SKEL, #1741).
//!
//! LOWERED: `local.get` of a parameter, `i32.add`, `return` and the function's
//! final `end`, in a LEAF function of at most six i32 parameters and zero or
//! one i32 result. Parameters are read-only here (no `local.set`/`tee`), so a
//! parameter's value never leaves its SysV argument register.
//!
//! EVERYTHING ELSE IS DECLINED BY NAME: [`SelectError::Unsupported`] carries
//! the op itself, so the message says which op, never "unsupported op". A
//! decline is an `Err`, never a partial body: the caller ships no object.
//!
//! REGISTER CONTRACT (SysV AMD64):
//! - parameter `i` lives in `edi, esi, edx, ecx, r8d, r9d` (the 32-bit view:
//!   the upper half of an i32 argument register is undefined, so it is never
//!   read — every op here uses the 32-bit operand size);
//! - temporaries are `eax, r10d, r11d`: caller-saved and no argument register,
//!   so a temporary can never overwrite a parameter that is still to be read;
//! - the result is in `eax`;
//! - NOTHING writes `rbx, rbp, rsp, r12–r15`, and nothing is ever stored below
//!   `rsp` (there is no store at all): no prologue, no frame, no red zone.
//!
//! A value stack deeper than the three temporaries declines loudly
//! ([`SelectError::OutOfTemporaries`]); it is never spilled in this lane.

use synth_core::WasmOp;

use crate::inst::{Inst, Reg};

/// SysV AMD64 integer argument registers, in order.
pub const ARG_REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

/// The temporaries, in allocation order. `Rax` first so a single-value result
/// usually needs no final move.
pub const TEMP_REGS: [Reg; 3] = [Reg::Rax, Reg::R10, Reg::R11];

/// The registers SysV AMD64 requires a function to preserve. No instruction
/// the selector emits may write one (checked in this module's tests and, on
/// real execution, by the oracle's callee-saved canaries).
pub const CALLEE_SAVED: [Reg; 7] = [
    Reg::Rbx,
    Reg::Rbp,
    Reg::Rsp,
    Reg::R12,
    Reg::R13,
    Reg::R14,
    Reg::R15,
];

/// Why a function was not lowered. Every variant names its cause.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum SelectError {
    /// The op has no x86-64 lowering in this lane.
    #[error(
        "x86_64: unsupported wasm op {0:?} (lane X1 lowers only local.get of a parameter, i32.add, return and end)"
    )]
    Unsupported(WasmOp),
    /// `local.get` of a non-parameter local (locals and frames are lane X3).
    #[error(
        "x86_64: local.get {index} reads a non-parameter local; locals are not lowered yet (function has {params} parameter(s))"
    )]
    NonParamLocal { index: u32, params: u32 },
    /// More than six parameters: the seventh would be stack-passed.
    #[error(
        "x86_64: {0} parameters; SysV passes the 7th and later on the stack, which is not lowered"
    )]
    TooManyParams(u32),
    /// More than one result.
    #[error("x86_64: {0} results; multi-value results are not lowered")]
    MultiValue(u32),
    /// The value stack outgrew the temporaries.
    #[error("x86_64: the value stack needs more than {} temporaries; spilling is not lowered", TEMP_REGS.len())]
    OutOfTemporaries,
    /// An op follows `return` before the function's final `end` (dead code
    /// is not lowered in this lane).
    #[error("x86_64: {0:?} follows `return`; unreachable code is not lowered")]
    AfterReturn(WasmOp),
    /// The op stream did not end in exactly one final `end`.
    #[error("x86_64: the function body does not end in its final `end`")]
    NoFinalEnd,
    /// A malformed body (the stack shape at an op is not what a validated
    /// module produces). Never reached from validated input.
    #[error("x86_64: malformed body: {0}")]
    Malformed(String),
}

/// One value on the wasm operand stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    /// Parameter `i`, still in its argument register.
    Param(u32),
    /// A temporary register.
    Temp(Reg),
}

struct Sel {
    out: Vec<Inst>,
    stack: Vec<Val>,
    free: Vec<Reg>,
}

impl Sel {
    fn reg(v: Val) -> Reg {
        match v {
            Val::Param(i) => ARG_REGS[i as usize],
            Val::Temp(r) => r,
        }
    }

    fn pop(&mut self, at: &WasmOp) -> Result<Val, SelectError> {
        self.stack
            .pop()
            .ok_or_else(|| SelectError::Malformed(format!("{at:?} pops an empty stack")))
    }

    fn release(&mut self, v: Val) {
        if let Val::Temp(r) = v {
            self.free.push(r);
            // Keep allocation deterministic: lowest-listed temporary first.
            self.free
                .sort_by_key(|r| std::cmp::Reverse(TEMP_REGS.iter().position(|t| t == r)));
        }
    }

    fn alloc(&mut self) -> Result<Reg, SelectError> {
        self.free.pop().ok_or(SelectError::OutOfTemporaries)
    }

    fn i32_add(&mut self, op: &WasmOp) -> Result<(), SelectError> {
        let b = self.pop(op)?;
        let a = self.pop(op)?;
        let dst = match (a, b) {
            // a is a temporary: add into it.
            (Val::Temp(t), _) => {
                self.out.push(Inst::AddRR32 {
                    dst: t,
                    src: Self::reg(b),
                });
                self.release(b);
                t
            }
            // i32.add commutes: add a into b's temporary.
            (_, Val::Temp(t)) => {
                self.out.push(Inst::AddRR32 {
                    dst: t,
                    src: Self::reg(a),
                });
                t
            }
            // Both are parameters: copy a into a fresh temporary first, so no
            // argument register is ever written.
            _ => {
                let t = self.alloc()?;
                self.out.push(Inst::MovRR32 {
                    dst: t,
                    src: Self::reg(a),
                });
                self.out.push(Inst::AddRR32 {
                    dst: t,
                    src: Self::reg(b),
                });
                t
            }
        };
        self.stack.push(Val::Temp(dst));
        Ok(())
    }

    /// Move the result (if any) into `eax` and return.
    fn ret(&mut self, results: u32, op: &WasmOp) -> Result<(), SelectError> {
        if results == 1 {
            let v = self.pop(op)?;
            if v != Val::Temp(Reg::Rax) {
                self.out.push(Inst::MovRR32 {
                    dst: Reg::Rax,
                    src: Self::reg(v),
                });
            }
        }
        self.out.push(Inst::Ret);
        Ok(())
    }
}

/// Lower one function body.
///
/// `num_params` and `num_results` are the function's declared signature; the
/// caller has already checked that every parameter and result is `i32`
/// ([`crate::backend`] reads the exact types from the module).
pub fn select(ops: &[WasmOp], num_params: u32, num_results: u32) -> Result<Vec<Inst>, SelectError> {
    if num_params > ARG_REGS.len() as u32 {
        return Err(SelectError::TooManyParams(num_params));
    }
    if num_results > 1 {
        return Err(SelectError::MultiValue(num_results));
    }
    let mut s = Sel {
        out: Vec::new(),
        stack: Vec::new(),
        free: TEMP_REGS.iter().rev().copied().collect(),
    };
    let mut returned = false;
    let mut ended = false;
    for op in ops {
        if ended {
            return Err(SelectError::Malformed(format!(
                "{op:?} follows the function's final `end`"
            )));
        }
        if returned && !matches!(op, WasmOp::End) {
            return Err(SelectError::AfterReturn(op.clone()));
        }
        match op {
            WasmOp::LocalGet(i) => {
                if *i >= num_params {
                    return Err(SelectError::NonParamLocal {
                        index: *i,
                        params: num_params,
                    });
                }
                s.stack.push(Val::Param(*i));
            }
            WasmOp::I32Add => s.i32_add(op)?,
            WasmOp::Return => {
                s.ret(num_results, op)?;
                returned = true;
            }
            // Only the function's own `end` reaches here: `block`, `loop` and
            // `if` are declined, so no other frame can be open.
            WasmOp::End => {
                if !returned {
                    if s.stack.len() as u32 != num_results {
                        return Err(SelectError::Malformed(format!(
                            "{} value(s) on the stack at the final `end`, {} result(s) declared",
                            s.stack.len(),
                            num_results
                        )));
                    }
                    s.ret(num_results, op)?;
                }
                ended = true;
            }
            other => return Err(SelectError::Unsupported(other.clone())),
        }
    }
    if !ended {
        return Err(SelectError::NoFinalEnd);
    }
    Ok(s.out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use WasmOp::*;

    fn writes_no_callee_saved(insts: &[Inst]) {
        for i in insts {
            if let Some(r) = i.writes() {
                assert!(!CALLEE_SAVED.contains(&r), "{i} writes {r:?}");
                assert!(!ARG_REGS.contains(&r), "{i} writes argument register {r:?}");
            }
        }
    }

    #[test]
    fn add_of_two_params_copies_then_adds() {
        let v = select(&[LocalGet(0), LocalGet(1), I32Add, End], 2, 1).unwrap();
        assert_eq!(
            v,
            vec![
                Inst::MovRR32 {
                    dst: Reg::Rax,
                    src: Reg::Rdi
                },
                Inst::AddRR32 {
                    dst: Reg::Rax,
                    src: Reg::Rsi
                },
                Inst::Ret
            ]
        );
        writes_no_callee_saved(&v);
    }

    #[test]
    fn identity_moves_the_param_into_eax() {
        let v = select(&[LocalGet(0), End], 1, 1).unwrap();
        assert_eq!(
            v,
            vec![
                Inst::MovRR32 {
                    dst: Reg::Rax,
                    src: Reg::Rdi
                },
                Inst::Ret
            ]
        );
    }

    #[test]
    fn deep_stacks_use_every_temporary_then_decline() {
        // (p0+p1) + (p2+p3) + (p4+p5): two temporaries live at once.
        let ops = [
            LocalGet(0),
            LocalGet(1),
            I32Add,
            LocalGet(2),
            LocalGet(3),
            I32Add,
            I32Add,
            LocalGet(4),
            LocalGet(5),
            I32Add,
            I32Add,
            End,
        ];
        let v = select(&ops, 6, 1).unwrap();
        writes_no_callee_saved(&v);
        // Four pairwise sums live at once need four temporaries: declined.
        let mut deep = Vec::new();
        for _ in 0..4 {
            deep.extend([LocalGet(0), LocalGet(1), I32Add]);
        }
        deep.extend([I32Add, I32Add, I32Add, End]);
        assert_eq!(select(&deep, 2, 1), Err(SelectError::OutOfTemporaries));
    }

    #[test]
    fn return_then_end_and_nothing_else() {
        let v = select(&[LocalGet(1), Return, End], 2, 1).unwrap();
        assert_eq!(v.last(), Some(&Inst::Ret));
        assert_eq!(v.iter().filter(|i| **i == Inst::Ret).count(), 1);
        assert_eq!(
            select(&[LocalGet(1), Return, LocalGet(0), End], 2, 1),
            Err(SelectError::AfterReturn(LocalGet(0)))
        );
    }

    #[test]
    fn declines_name_their_cause() {
        assert_eq!(
            select(&[LocalGet(0), LocalGet(1), I32Sub, End], 2, 1),
            Err(SelectError::Unsupported(I32Sub))
        );
        let e = select(&[LocalGet(0), LocalGet(1), I32Sub, End], 2, 1).unwrap_err();
        assert!(e.to_string().contains("I32Sub"), "{e}");
        assert_eq!(
            select(&[LocalGet(2), End], 2, 1),
            Err(SelectError::NonParamLocal {
                index: 2,
                params: 2
            })
        );
        assert_eq!(
            select(&[LocalGet(0), End], 7, 1),
            Err(SelectError::TooManyParams(7))
        );
        assert_eq!(select(&[End], 0, 2), Err(SelectError::MultiValue(2)));
        assert_eq!(select(&[LocalGet(0)], 1, 1), Err(SelectError::NoFinalEnd));
        for op in [LocalSet(0), LocalTee(0), Call(0), Nop, Drop, I32Const(1)] {
            let e = select(&[op.clone(), End], 1, 0).unwrap_err();
            assert_eq!(e, SelectError::Unsupported(op));
        }
    }
}
