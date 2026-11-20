//! The x86-64 instruction selector — lanes X1 and X2 (RQ-91-X86SKEL,
//! RQ-91-X86ALU, #1741).
//!
//! LOWERED: straight-line integer code in a LEAF function of at most six
//! i32/i64 parameters and zero or one i32/i64 result — `local.get` of a
//! parameter, `i32.const`/`i64.const`, the ops of the rule table
//! ([`crate::rules::RULES`]: add, sub, mul, and, or, xor, the shifts and
//! rotates, the compares and `eqz`, the extensions and `wrap`), `select`,
//! `drop`, `nop`, `return` and the function's final `end`. Parameters are
//! read-only here (no `local.set`/`tee`), so a parameter's value never leaves
//! its SysV argument register.
//!
//! EVERYTHING ELSE IS DECLINED BY NAME: [`SelectError::Unsupported`] carries
//! the op itself, so the message says which op, never "unsupported op". A
//! decline is an `Err`, never a partial body: the caller ships no object.
//! `div`/`rem` are declined on purpose: x86 `div`/`idiv` FAULT where wasm
//! traps or returns a value, so they wait for their guards (lane X4).
//!
//! REGISTER CONTRACT (SysV AMD64):
//! - parameter `i` lives in `rdi, rsi, rdx, rcx, r8, r9`. The upper half of
//!   an i32 argument register is undefined, so an i32 is only ever read at the
//!   32-bit operand size;
//! - temporaries are `rax, r10, r11`: caller-saved and no argument register,
//!   so a temporary can never overwrite a parameter that is still to be read;
//! - an i32 value's bits 63:32 are UNSPECIFIED wherever it lives (that is what
//!   makes `i32.wrap_i64` free); every consumer of an i32 uses the 32-bit
//!   operand size, and `i64.extend_i32_u` re-zeroes with a 32-bit `mov`;
//! - a variable shift needs its count in `cl`. With at most three parameters
//!   `rcx` is free and is simply written. With four or more it holds
//!   parameter 3: the count is used in place when it IS parameter 3, and
//!   otherwise `rcx` is saved to a temporary around the shift and restored
//!   (all 64 bits). That is the only write to an argument register;
//! - the result is in `eax`/`rax`;
//! - NOTHING writes `rbx, rbp, rsp, r12–r15`, and nothing is ever stored below
//!   `rsp` (there is no store at all): no prologue, no frame, no red zone;
//! - no value is kept in EFLAGS across a wasm op: a compare materialises 0/1
//!   (`cmp; setCC; movzbl`) and `select` tests its condition itself.
//!
//! NEEDING A FOURTH TEMPORARY declines loudly
//! ([`SelectError::OutOfTemporaries`]); nothing is spilled in this lane. The
//! limit is temporaries in use at once, not stack depth: a parameter on the
//! stack takes none, and the `rcx` save around a shift takes one.

use synth_core::WasmOp;

use crate::inst::{AluOp, Cond, Ext, Inst, Reg, ShiftOp, Size};
use crate::rules::{Lowering, Rule, rule_for};

pub use crate::rules::Ty;

/// SysV AMD64 integer argument registers, in order.
pub const ARG_REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

/// The temporaries, in allocation order. `Rax` first so a single-value result
/// usually needs no final move.
pub const TEMP_REGS: [Reg; 3] = [Reg::Rax, Reg::R10, Reg::R11];

/// The index of the parameter that arrives in `rcx`, the shift-count register.
const RCX_PARAM: u32 = 3;

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
        "x86_64: unsupported wasm op {0:?} (lanes X1-X2 lower straight-line i32/i64 integer code only: const, local.get of a parameter, add/sub/mul/and/or/xor, shifts and rotates, compares, extensions, select, drop, return)"
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
    /// A fourth temporary was needed.
    #[error("x86_64: the function needs more than {} temporaries at once (computed values on the stack, plus one to save rcx around a shift when rcx holds parameter 3); spilling is not lowered", TEMP_REGS.len())]
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

/// Where a value on the wasm operand stack lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Loc {
    /// Parameter `i`, still in its argument register.
    Param(u32),
    /// A temporary register.
    Temp(Reg),
}

/// One value on the wasm operand stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Val {
    loc: Loc,
    ty: Ty,
}

fn size_of(ty: Ty) -> Size {
    match ty {
        Ty::I32 => Size::L,
        Ty::I64 => Size::Q,
    }
}

fn reg_of(v: Val) -> Reg {
    match v.loc {
        Loc::Param(i) => ARG_REGS[i as usize],
        Loc::Temp(r) => r,
    }
}

fn mov(size: Size, dst: Reg, src: Reg) -> Inst {
    Inst::Alu {
        op: AluOp::Mov,
        size,
        dst,
        src,
    }
}

struct Sel<'a> {
    params: &'a [Ty],
    out: Vec<Inst>,
    stack: Vec<Val>,
    free: Vec<Reg>,
}

impl Sel<'_> {
    /// Pop a value of type `ty`.
    fn pop(&mut self, at: &WasmOp, ty: Ty) -> Result<Val, SelectError> {
        let v = self.pop_any(at)?;
        if v.ty != ty {
            return Err(SelectError::Malformed(format!(
                "{at:?} pops a {:?} where it needs a {ty:?}",
                v.ty
            )));
        }
        Ok(v)
    }

    fn pop_any(&mut self, at: &WasmOp) -> Result<Val, SelectError> {
        self.stack
            .pop()
            .ok_or_else(|| SelectError::Malformed(format!("{at:?} pops an empty stack")))
    }

    fn push(&mut self, r: Reg, ty: Ty) {
        self.stack.push(Val {
            loc: Loc::Temp(r),
            ty,
        });
    }

    fn release(&mut self, v: Val) {
        if let Loc::Temp(r) = v.loc {
            self.release_reg(r);
        }
    }

    fn release_reg(&mut self, r: Reg) {
        self.free.push(r);
        // Keep allocation deterministic: lowest-listed temporary first.
        self.free
            .sort_by_key(|r| std::cmp::Reverse(TEMP_REGS.iter().position(|t| t == r)));
    }

    fn alloc(&mut self) -> Result<Reg, SelectError> {
        self.free.pop().ok_or(SelectError::OutOfTemporaries)
    }

    /// The temporary holding `v`: its own, or a fresh one it is copied into
    /// (so no argument register is ever the destination of an operation).
    /// `mov` leaves EFLAGS alone.
    fn temp_for(&mut self, v: Val) -> Result<Reg, SelectError> {
        match v.loc {
            Loc::Temp(t) => Ok(t),
            Loc::Param(_) => {
                let t = self.alloc()?;
                self.out.push(mov(size_of(v.ty), t, reg_of(v)));
                Ok(t)
            }
        }
    }

    /// The temporary a result that only DEPENDS on `a` and `b` (through
    /// EFLAGS) is written to: one of theirs, else a fresh one. The other
    /// operand's temporary is released.
    fn result_temp(&mut self, a: Val, b: Option<Val>) -> Result<Reg, SelectError> {
        match (a.loc, b.map(|b| b.loc)) {
            (Loc::Temp(t), other) => {
                if let Some(Loc::Temp(u)) = other {
                    self.release_reg(u);
                }
                Ok(t)
            }
            (Loc::Param(_), Some(Loc::Temp(t))) => Ok(t),
            (Loc::Param(_), Some(Loc::Param(_)) | None) => self.alloc(),
        }
    }

    /// `setCC t; movzbl t, t` and push the i32 0/1.
    fn materialise(&mut self, cond: Cond, t: Reg) {
        self.out.push(Inst::SetCc { cond, dst: t });
        self.out.push(Inst::Movx {
            ext: Ext::ZxBL,
            dst: t,
            src: t,
        });
        self.push(t, Ty::I32);
    }

    /// `a OP b` for a two-address instruction built by `make(dst, src)`.
    fn two_address(
        &mut self,
        at: &WasmOp,
        ty: Ty,
        commutes: bool,
        make: impl Fn(Reg, Reg) -> Inst,
    ) -> Result<(), SelectError> {
        let b = self.pop(at, ty)?;
        let a = self.pop(at, ty)?;
        let dst = match (a.loc, b.loc) {
            // The op commutes and only b has a temporary: compute into it.
            (Loc::Param(_), Loc::Temp(t)) if commutes => {
                self.out.push(make(t, reg_of(a)));
                self.push(t, ty);
                return Ok(());
            }
            (Loc::Temp(_), Loc::Temp(_) | Loc::Param(_))
            | (Loc::Param(_), Loc::Temp(_) | Loc::Param(_)) => self.temp_for(a)?,
        };
        self.out.push(make(dst, reg_of(b)));
        self.release(b);
        self.push(dst, ty);
        Ok(())
    }

    /// `a SHIFT b`, the count in `cl` (see the module doc for `rcx`).
    fn shift(&mut self, at: &WasmOp, ty: Ty, op: ShiftOp) -> Result<(), SelectError> {
        let b = self.pop(at, ty)?;
        let a = self.pop(at, ty)?;
        let dst = self.temp_for(a)?;
        let shift = Inst::ShiftCl {
            op,
            size: size_of(ty),
            dst,
        };
        let rcx_holds_a_param = self.params.len() as u32 > RCX_PARAM;
        if b.loc == Loc::Param(RCX_PARAM) {
            // The count is parameter 3: it is already in cl.
            self.out.push(shift);
        } else if !rcx_holds_a_param {
            self.out.push(Inst::mov32(Reg::Rcx, reg_of(b)));
            self.out.push(shift);
        } else {
            // rcx is parameter 3 and must survive: save all 64 bits.
            let save = self.alloc()?;
            self.out.push(mov(Size::Q, save, Reg::Rcx));
            self.out.push(Inst::mov32(Reg::Rcx, reg_of(b)));
            self.out.push(shift);
            self.out.push(mov(Size::Q, Reg::Rcx, save));
            self.release_reg(save);
        }
        self.release(b);
        self.push(dst, ty);
        Ok(())
    }

    /// One row of the rule table.
    fn apply(&mut self, at: &WasmOp, rule: &Rule) -> Result<(), SelectError> {
        let ty = rule.ty;
        let size = size_of(ty);
        match rule.lower {
            Lowering::Alu { op, commutes } => self.two_address(at, ty, commutes, |dst, src| {
                Inst::Alu { op, size, dst, src }
            }),
            Lowering::Mul => {
                self.two_address(at, ty, true, |dst, src| Inst::Imul { size, dst, src })
            }
            Lowering::Shift(op) => self.shift(at, ty, op),
            Lowering::Compare(cond) => {
                let b = self.pop(at, ty)?;
                let a = self.pop(at, ty)?;
                self.out.push(Inst::Alu {
                    op: AluOp::Cmp,
                    size,
                    dst: reg_of(a),
                    src: reg_of(b),
                });
                let t = self.result_temp(a, Some(b))?;
                self.materialise(cond, t);
                Ok(())
            }
            Lowering::Eqz => {
                let a = self.pop(at, ty)?;
                self.out.push(Inst::Alu {
                    op: AluOp::Test,
                    size,
                    dst: reg_of(a),
                    src: reg_of(a),
                });
                let t = self.result_temp(a, None)?;
                self.materialise(Cond::E, t);
                Ok(())
            }
            Lowering::Extend { ext, to } => {
                let a = self.pop(at, ty)?;
                let t = self.result_temp(a, None)?;
                self.out.push(Inst::Movx {
                    ext,
                    dst: t,
                    src: reg_of(a),
                });
                self.push(t, to);
                Ok(())
            }
            Lowering::ZeroExtend => {
                let a = self.pop(at, ty)?;
                let t = self.result_temp(a, None)?;
                self.out.push(Inst::mov32(t, reg_of(a)));
                self.push(t, Ty::I64);
                Ok(())
            }
            Lowering::Wrap => {
                let a = self.pop(at, ty)?;
                self.stack.push(Val {
                    loc: a.loc,
                    ty: Ty::I32,
                });
                Ok(())
            }
        }
    }

    /// `select`: `a` if the condition is nonzero, else `b`.
    fn select(&mut self, at: &WasmOp) -> Result<(), SelectError> {
        let c = self.pop(at, Ty::I32)?;
        let b = self.pop_any(at)?;
        let a = self.pop(at, b.ty)?;
        self.out.push(Inst::Alu {
            op: AluOp::Test,
            size: Size::L,
            dst: reg_of(c),
            src: reg_of(c),
        });
        // The condition is in EFLAGS now; its temporary may hold a's copy.
        self.release(c);
        let dst = self.temp_for(a)?;
        self.out.push(Inst::Cmov {
            cond: Cond::E,
            size: size_of(a.ty),
            dst,
            src: reg_of(b),
        });
        self.release(b);
        self.push(dst, a.ty);
        Ok(())
    }

    fn constant(&mut self, ty: Ty, bits: u64) -> Result<(), SelectError> {
        let dst = self.alloc()?;
        self.out.push(if let Ok(imm) = u32::try_from(bits) {
            // Also every i32: a 32-bit move zero-extends.
            Inst::MovImm32 { dst, imm }
        } else if let Ok(imm) = i32::try_from(bits as i64) {
            Inst::MovImmSx { dst, imm }
        } else {
            Inst::MovAbs { dst, imm: bits }
        });
        self.push(dst, ty);
        Ok(())
    }

    /// Move the result (if any) into `eax`/`rax` and return.
    fn ret(&mut self, results: &[Ty], op: &WasmOp) -> Result<(), SelectError> {
        if let Some(&ty) = results.first() {
            let v = self.pop(op, ty)?;
            if v.loc != Loc::Temp(Reg::Rax) {
                self.out.push(mov(size_of(ty), Reg::Rax, reg_of(v)));
            }
        }
        self.out.push(Inst::Ret);
        Ok(())
    }
}

/// Lower one function body.
///
/// `params` and `results` are the function's declared signature; the caller
/// has already checked that every parameter and result is `i32` or `i64`
/// ([`crate::backend`] reads the exact types from the module).
pub fn select(ops: &[WasmOp], params: &[Ty], results: &[Ty]) -> Result<Vec<Inst>, SelectError> {
    if params.len() > ARG_REGS.len() {
        return Err(SelectError::TooManyParams(params.len() as u32));
    }
    if results.len() > 1 {
        return Err(SelectError::MultiValue(results.len() as u32));
    }
    let mut s = Sel {
        params,
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
                let Some(&ty) = params.get(*i as usize) else {
                    return Err(SelectError::NonParamLocal {
                        index: *i,
                        params: params.len() as u32,
                    });
                };
                s.stack.push(Val {
                    loc: Loc::Param(*i),
                    ty,
                });
            }
            WasmOp::I32Const(v) => s.constant(Ty::I32, u64::from(*v as u32))?,
            WasmOp::I64Const(v) => s.constant(Ty::I64, *v as u64)?,
            WasmOp::Select => s.select(op)?,
            WasmOp::Drop => {
                let v = s.pop_any(op)?;
                s.release(v);
            }
            WasmOp::Nop => {}
            WasmOp::Return => {
                s.ret(results, op)?;
                returned = true;
            }
            // Only the function's own `end` reaches here: `block`, `loop` and
            // `if` are declined, so no other frame can be open.
            WasmOp::End => {
                if !returned {
                    if s.stack.len() != results.len() {
                        return Err(SelectError::Malformed(format!(
                            "{} value(s) on the stack at the final `end`, {} result(s) declared",
                            s.stack.len(),
                            results.len()
                        )));
                    }
                    s.ret(results, op)?;
                }
                ended = true;
            }
            other => match rule_for(other) {
                Some(rule) => s.apply(other, rule)?,
                None => return Err(SelectError::Unsupported(other.clone())),
            },
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
    use Ty::{I32, I64};
    use WasmOp::*;

    /// No callee-saved register is written, and the only argument register
    /// ever written is `rcx`, as a shift count.
    fn check_writes(insts: &[Inst]) {
        for i in insts {
            if let Some(r) = i.writes() {
                assert!(!CALLEE_SAVED.contains(&r), "{i} writes {r:?}");
                assert!(
                    !ARG_REGS.contains(&r) || r == Reg::Rcx,
                    "{i} writes argument register {r:?}"
                );
            }
        }
    }

    fn att(insts: &[Inst]) -> Vec<String> {
        insts.iter().map(Inst::att).collect()
    }

    fn sel(ops: &[WasmOp], params: &[Ty], results: &[Ty]) -> Vec<String> {
        let v = select(ops, params, results).unwrap();
        check_writes(&v);
        att(&v)
    }

    #[test]
    fn add_of_two_params_copies_then_adds() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I32Add, End],
                &[I32, I32],
                &[I32]
            ),
            ["movl %edi, %eax", "addl %esi, %eax", "retq"]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64Add, End],
                &[I64, I64],
                &[I64]
            ),
            ["movq %rdi, %rax", "addq %rsi, %rax", "retq"]
        );
    }

    #[test]
    fn identity_moves_the_param_at_its_own_width() {
        assert_eq!(
            sel(&[LocalGet(0), End], &[I32], &[I32]),
            ["movl %edi, %eax", "retq"]
        );
        assert_eq!(
            sel(&[LocalGet(1), End], &[I32, I64], &[I64]),
            ["movq %rsi, %rax", "retq"]
        );
    }

    /// `a - b` with only `b` in a temporary must NOT compute `b - a` into it.
    #[test]
    fn a_non_commutative_op_never_lands_in_the_right_operands_temporary() {
        let ops = [LocalGet(0), LocalGet(1), I32Const(0), I32Add, I32Sub, End];
        assert_eq!(
            sel(&ops, &[I32, I32], &[I32]),
            [
                "movl $0x0, %eax",
                "addl %esi, %eax",
                "movl %edi, %r10d",
                "subl %eax, %r10d",
                "movl %r10d, %eax",
                "retq"
            ]
        );
        // The commutative twin does.
        let ops = [LocalGet(0), LocalGet(1), I32Const(0), I32Add, I32Xor, End];
        assert_eq!(
            sel(&ops, &[I32, I32], &[I32]),
            [
                "movl $0x0, %eax",
                "addl %esi, %eax",
                "xorl %edi, %eax",
                "retq"
            ]
        );
    }

    #[test]
    fn a_compare_is_cmp_setcc_movzbl_in_wasm_operand_order() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I32LtU, End],
                &[I32, I32],
                &[I32]
            ),
            ["cmpl %esi, %edi", "setb %al", "movzbl %al, %eax", "retq"]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64GeS, End],
                &[I64, I64],
                &[I32]
            ),
            ["cmpq %rsi, %rdi", "setge %al", "movzbl %al, %eax", "retq"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64Eqz, End], &[I64], &[I32]),
            ["testq %rdi, %rdi", "sete %al", "movzbl %al, %eax", "retq"]
        );
    }

    /// With at most three parameters `rcx` is free: the count is moved in.
    #[test]
    fn a_shift_moves_its_count_into_cl_when_rcx_is_free() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I32Shl, End],
                &[I32, I32],
                &[I32]
            ),
            [
                "movl %edi, %eax",
                "movl %esi, %ecx",
                "shll %cl, %eax",
                "retq"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64Rotr, End],
                &[I64, I64],
                &[I64]
            ),
            [
                "movq %rdi, %rax",
                "movl %esi, %ecx",
                "rorq %cl, %rax",
                "retq"
            ]
        );
    }

    /// With four or more parameters `rcx` IS parameter 3: used in place when
    /// it is the count, otherwise saved and restored around the shift.
    #[test]
    fn a_shift_preserves_rcx_when_it_holds_parameter_3() {
        let p4 = [I32, I32, I32, I32];
        assert_eq!(
            sel(&[LocalGet(0), LocalGet(3), I32ShrU, End], &p4, &[I32]),
            ["movl %edi, %eax", "shrl %cl, %eax", "retq"]
        );
        assert_eq!(
            sel(&[LocalGet(0), LocalGet(1), I32ShrS, End], &p4, &[I32]),
            [
                "movl %edi, %eax",
                "movq %rcx, %r10",
                "movl %esi, %ecx",
                "sarl %cl, %eax",
                "movq %r10, %rcx",
                "retq"
            ]
        );
        // The shifted value is parameter 3 itself: copied out before cl is
        // overwritten.
        assert_eq!(
            sel(&[LocalGet(3), LocalGet(0), I32Rotl, End], &p4, &[I32]),
            [
                "movl %ecx, %eax",
                "movq %rcx, %r10",
                "movl %edi, %ecx",
                "roll %cl, %eax",
                "movq %r10, %rcx",
                "retq"
            ]
        );
    }

    #[test]
    fn select_tests_the_condition_then_cmoves_the_else_value() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), LocalGet(2), Select, End],
                &[I32, I32, I32],
                &[I32]
            ),
            [
                "testl %edx, %edx",
                "movl %edi, %eax",
                "cmovel %esi, %eax",
                "retq"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), LocalGet(2), Select, End],
                &[I64, I64, I32],
                &[I64]
            ),
            [
                "testl %edx, %edx",
                "movq %rdi, %rax",
                "cmoveq %rsi, %rax",
                "retq"
            ]
        );
    }

    #[test]
    fn constants_pick_the_shortest_correct_move() {
        assert_eq!(
            sel(&[I32Const(-1), End], &[], &[I32]),
            ["movl $0xffffffff, %eax", "retq"]
        );
        assert_eq!(
            sel(&[I64Const(0xFFFF_FFFF), End], &[], &[I64]),
            ["movl $0xffffffff, %eax", "retq"]
        );
        assert_eq!(
            sel(&[I64Const(-1), End], &[], &[I64]),
            ["movq $0xffffffffffffffff, %rax", "retq"]
        );
        assert_eq!(
            sel(&[I64Const(i64::from(i32::MIN)), End], &[], &[I64]),
            ["movq $0xffffffff80000000, %rax", "retq"]
        );
        assert_eq!(
            sel(&[I64Const(0x1_0000_0000), End], &[], &[I64]),
            ["movabsq $0x100000000, %rax", "retq"]
        );
        assert_eq!(
            sel(&[I64Const(i64::MIN), End], &[], &[I64]),
            ["movabsq $0x8000000000000000, %rax", "retq"]
        );
    }

    #[test]
    fn conversions() {
        // wrap is free; the i32 result is read at 32 bits.
        assert_eq!(
            sel(&[LocalGet(0), I32WrapI64, End], &[I64], &[I32]),
            ["movl %edi, %eax", "retq"]
        );
        // extend_u re-zeroes even after a wrap of the same register.
        assert_eq!(
            sel(
                &[LocalGet(0), I32WrapI64, I64ExtendI32U, End],
                &[I64],
                &[I64]
            ),
            ["movl %edi, %eax", "retq"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64ExtendI32S, End], &[I32], &[I64]),
            ["movslq %edi, %rax", "retq"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I32Extend8S, End], &[I32], &[I32]),
            ["movsbl %dil, %eax", "retq"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64Extend16S, End], &[I64], &[I64]),
            ["movswq %di, %rax", "retq"]
        );
    }

    #[test]
    fn drop_frees_its_temporary_and_nop_emits_nothing() {
        assert_eq!(
            sel(&[I32Const(1), Drop, Nop, I32Const(2), End], &[], &[I32]),
            ["movl $0x1, %eax", "movl $0x2, %eax", "retq"]
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
        sel(&ops, &[I32; 6], &[I32]);
        // Four pairwise sums live at once need four temporaries: declined.
        let mut deep = Vec::new();
        for _ in 0..4 {
            deep.extend([LocalGet(0), LocalGet(1), I32Add]);
        }
        deep.extend([I32Add, I32Add, I32Add, End]);
        assert_eq!(
            select(&deep, &[I32, I32], &[I32]),
            Err(SelectError::OutOfTemporaries)
        );
        // A shift that must save rcx with every temporary busy declines too.
        let ops = [
            I32Const(1),
            I32Const(2),
            LocalGet(0),
            I32Const(3),
            I32Shl,
            I32Add,
            I32Add,
            End,
        ];
        assert_eq!(
            select(&ops, &[I32; 4], &[I32]),
            Err(SelectError::OutOfTemporaries)
        );
    }

    #[test]
    fn return_then_end_and_nothing_else() {
        let v = select(&[LocalGet(1), Return, End], &[I32, I32], &[I32]).unwrap();
        assert_eq!(v.last(), Some(&Inst::Ret));
        assert_eq!(v.iter().filter(|i| **i == Inst::Ret).count(), 1);
        assert_eq!(
            select(
                &[LocalGet(1), Return, LocalGet(0), End],
                &[I32, I32],
                &[I32]
            ),
            Err(SelectError::AfterReturn(LocalGet(0)))
        );
    }

    #[test]
    fn declines_name_their_cause() {
        for op in [
            I32DivS, I32DivU, I32RemS, I32RemU, I64DivS, I64DivU, I64RemS, I64RemU, I32Clz, I32Ctz,
            I32Popcnt, I64Clz, I64Ctz, I64Popcnt,
        ] {
            let ops = [LocalGet(0), LocalGet(1), op.clone(), End];
            let e = select(&ops, &[I32, I32], &[I32]).unwrap_err();
            assert_eq!(e, SelectError::Unsupported(op.clone()));
            assert!(e.to_string().contains(&format!("{op:?}")), "{e}");
        }
        assert_eq!(
            select(&[LocalGet(2), End], &[I32, I32], &[I32]),
            Err(SelectError::NonParamLocal {
                index: 2,
                params: 2
            })
        );
        assert_eq!(
            select(&[LocalGet(0), End], &[I32; 7], &[I32]),
            Err(SelectError::TooManyParams(7))
        );
        assert_eq!(
            select(&[End], &[], &[I32, I32]),
            Err(SelectError::MultiValue(2))
        );
        assert_eq!(
            select(&[LocalGet(0)], &[I32], &[I32]),
            Err(SelectError::NoFinalEnd)
        );
        for op in [LocalSet(0), LocalTee(0), Call(0), Unreachable, Block] {
            let e = select(&[op.clone(), End], &[I32], &[]).unwrap_err();
            assert_eq!(e, SelectError::Unsupported(op));
        }
    }

    /// A type the stack does not hold is a malformed body, never a guess.
    #[test]
    fn a_mistyped_stack_is_malformed() {
        for (ops, params, results) in [
            (vec![LocalGet(0), LocalGet(1), I64Add, End], [I32, I64], I64),
            (vec![LocalGet(0), End], [I32, I32], I64),
            (
                vec![LocalGet(0), LocalGet(1), LocalGet(0), Select, End],
                [I32, I64],
                I32,
            ),
        ] {
            assert!(matches!(
                select(&ops, &params, &[results]),
                Err(SelectError::Malformed(_))
            ));
        }
    }
}
