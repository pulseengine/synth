//! The x86-64 instruction selector — lanes X1 to X4 (RQ-91-X86SKEL,
//! RQ-91-X86ALU, RQ-91-X86FRAME, #1741).
//!
//! LOWERED: straight-line integer code in a LEAF function of at most six
//! i32/i64 parameters, any i32/i64 locals that fit the frame limit, and zero
//! or one i32/i64 result — `local.get`/`local.set`/`local.tee`,
//! `i32.const`/`i64.const`, the ops of the rule table
//! ([`crate::rules::RULES`]: add, sub, mul, and, or, xor, the shifts and
//! rotates, the compares and `eqz`, the extensions and `wrap`, `div`/`rem`
//! with their trap guards, `clz`/`ctz`/`popcnt`), `select`, `drop`, `nop`,
//! `return` and the function's final `end`.
//!
//! EVERYTHING ELSE IS DECLINED BY NAME: [`SelectError::Unsupported`] carries
//! the op itself, so the message says which op, never "unsupported op". A
//! decline is an `Err`, never a partial body: the caller ships no object.
//!
//! THE FRAME (SysV AMD64), the same in every function:
//!
//! ```text
//!   pushq %rbp ; movq %rsp, %rbp ; subq $N, %rsp
//!   [rbp - 8*(i+1)]            local i (parameters first), 8 bytes each
//!   [rbp - 8*(locals+k+1)]     spill slot k
//!   movq %rbp, %rsp ; popq %rbp ; retq         on every return path
//! ```
//!
//! `N` is the slot bytes rounded up to 16, so `rsp` is 16-byte aligned for
//! the whole body. Nothing is ever stored below `rsp`: the red zone is not
//! used. A frame above [`FRAME_LIMIT`] bytes is DECLINED: it would need a
//! stack probe, which is not lowered.
//!
//! EVERY PARAMETER IS HOMED to its slot in the prologue, and every non-param
//! local's slot is zeroed there (all 8 bytes). `local.get` LOADS a copy into a
//! temporary and `local.set`/`local.tee` STORE, so a value already on the
//! operand stack can never change when its local is written later (the
//! parameter-aliasing class does not exist), and after the prologue no
//! argument register holds anything that is read again.
//!
//! REGISTER CONTRACT:
//! - temporaries are `rsi, rdi, r8, r9, r10, r11` ([`TEMP_REGS`]): each holds
//!   at most one operand-stack value;
//! - `rax, rcx, rdx` ([`SCRATCH_REGS`]) are never allocated: they are the
//!   fixed operands of the shifts (`cl`), of `div`/`idiv` (`rdx:rax`) and of
//!   the result (`rax`), and scratch inside one op's sequence;
//! - WHEN THE TEMPORARIES RUN OUT the deepest register-held value on the
//!   operand stack is stored to a spill slot (all 64 bits) and its register is
//!   reused; a spilled value is loaded back when it is popped. A spill is a
//!   `mov`, which leaves EFLAGS alone;
//! - an i32 value's bits 63:32 are UNSPECIFIED wherever it lives (that is what
//!   makes `i32.wrap_i64` free; the upper half of an i32 argument register is
//!   undefined in the ABI, and the execution oracle poisons it): every
//!   consumer of an i32 uses the 32-bit operand size, and `i64.extend_i32_u`
//!   re-zeroes with a 32-bit `mov`;
//! - the only callee-saved registers written are `rbp` and `rsp`, by the five
//!   frame instructions above; `rbx, r12–r15` are never written;
//! - no value is kept in EFLAGS across a wasm op.
//!
//! TRAPS are `ud2`, reached only through an explicit guard. `div`/`idiv`
//! raise #DE on a zero divisor and on `INT_MIN / -1`; neither is ever executed
//! with such operands: a zero divisor branches to a `ud2`, `div_s` branches to
//! a second `ud2` on `INT_MIN / -1`, and `rem_s` by -1 divides 0 instead of
//! the dividend (the remainder is 0 for every dividend). Branches are forward
//! `jCC rel32` over a fixed run of instructions whose length is read from the
//! encoder, so there is no label and no size estimate.

use synth_core::WasmOp;

use crate::encoder::encode;
use crate::inst::{AluOp, Cond, Ext, ImmOp, Inst, Mem, Reg, ShiftOp, Size};
use crate::rules::{Lowering, Rule, rule_for};

pub use crate::rules::Ty;

/// SysV AMD64 integer argument registers, in order.
pub const ARG_REGS: [Reg; 6] = [Reg::Rdi, Reg::Rsi, Reg::Rdx, Reg::Rcx, Reg::R8, Reg::R9];

/// The temporaries, in allocation order. All caller-saved; four of them are
/// argument registers, free once the prologue has homed the parameters.
pub const TEMP_REGS: [Reg; 6] = [Reg::Rsi, Reg::Rdi, Reg::R8, Reg::R9, Reg::R10, Reg::R11];

/// Never allocated: fixed operands (`cl`, `rdx:rax`, the result) and scratch.
pub const SCRATCH_REGS: [Reg; 3] = [Reg::Rax, Reg::Rcx, Reg::Rdx];

/// The registers SysV AMD64 requires a function to preserve. Only `rbp` and
/// `rsp` are written, by the frame instructions (checked in this module's
/// tests and, on real execution, by the oracle's callee-saved canaries).
pub const CALLEE_SAVED: [Reg; 7] = [
    Reg::Rbx,
    Reg::Rbp,
    Reg::Rsp,
    Reg::R12,
    Reg::R13,
    Reg::R14,
    Reg::R15,
];

/// The largest frame lowered, in bytes below `rbp`. One page: a larger frame
/// could step over a guard page without touching it, and no stack probe is
/// emitted.
pub const FRAME_LIMIT: u32 = 4096;

/// Why a function was not lowered. Every variant names its cause.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum SelectError {
    /// The op has no x86-64 lowering in this lane.
    #[error(
        "x86_64: unsupported wasm op {0:?} (lanes X1-X4 lower straight-line i32/i64 integer code only: const, local.get/set/tee, add/sub/mul/and/or/xor, shifts and rotates, compares, extensions, div/rem, clz/ctz/popcnt, select, drop, return)"
    )]
    Unsupported(WasmOp),
    /// More than six parameters: the seventh would be stack-passed.
    #[error(
        "x86_64: {0} parameters; SysV passes the 7th and later on the stack, which is not lowered"
    )]
    TooManyParams(u32),
    /// More than one result.
    #[error("x86_64: {0} results; multi-value results are not lowered")]
    MultiValue(u32),
    /// The locals and spill slots need more than [`FRAME_LIMIT`] bytes.
    #[error(
        "x86_64: the frame needs {0} bytes for locals and spilled values, above the {FRAME_LIMIT}-byte limit; a larger frame needs a stack probe, which is not lowered"
    )]
    FrameTooLarge(u64),
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
    /// A temporary register, owned by this value alone.
    Reg(Reg),
    /// Spill slot `k` of the frame.
    Spill(u32),
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

fn bits_of(ty: Ty) -> u32 {
    match ty {
        Ty::I32 => 32,
        Ty::I64 => 64,
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

/// `xorl %r, %r`: zero all 64 bits of `r`.
fn zero(r: Reg) -> Inst {
    Inst::Alu {
        op: AluOp::Xor,
        size: Size::L,
        dst: r,
        src: r,
    }
}

/// The shortest move of the constant `bits` into all 64 bits of `dst`.
fn const_inst(dst: Reg, bits: u64) -> Inst {
    if let Ok(imm) = u32::try_from(bits) {
        // Also every i32: a 32-bit move zero-extends.
        Inst::MovImm32 { dst, imm }
    } else if let Ok(imm) = i32::try_from(bits as i64) {
        Inst::MovImmSx { dst, imm }
    } else {
        Inst::MovAbs { dst, imm: bits }
    }
}

/// `jCC` over `skipped`, then `skipped`: the run executes only when `cond`
/// is FALSE. The displacement is the run's encoded length, read from the
/// encoder (an instruction's length is a pure function of the instruction).
fn skip_if(cond: Cond, skipped: Vec<Inst>) -> Vec<Inst> {
    let rel: usize = skipped.iter().map(|i| encode(i).len()).sum();
    let mut v = vec![Inst::Jcc {
        cond,
        rel: i32::try_from(rel).expect("a guard run is a few bytes"),
    }];
    v.extend(skipped);
    v
}

/// The frame slot `index` slots below `rbp` (slot 0 is `[rbp - 8]`).
fn slot(index: u64) -> Result<Mem, SelectError> {
    let bytes = (index + 1) * 8;
    if bytes > u64::from(FRAME_LIMIT) {
        return Err(SelectError::FrameTooLarge(bytes));
    }
    Ok(Mem {
        base: Reg::Rbp,
        disp: -(bytes as i32),
    })
}

struct Sel<'a> {
    /// Every local's type: the parameters, then the declared locals.
    locals: &'a [Ty],
    /// The body, without prologue (the frame size is known only at the end).
    out: Vec<Inst>,
    stack: Vec<Val>,
    free: Vec<Reg>,
    /// Spill slots that are free again, and how many were ever needed.
    free_spills: Vec<u32>,
    spills: u32,
}

impl Sel<'_> {
    fn spill_mem(&self, k: u32) -> Result<Mem, SelectError> {
        slot(self.locals.len() as u64 + u64::from(k))
    }

    fn local(&self, at: &WasmOp, index: u32) -> Result<(Ty, Mem), SelectError> {
        let Some(&ty) = self.locals.get(index as usize) else {
            return Err(SelectError::Malformed(format!(
                "{at:?} names local {index}; the function has {}",
                self.locals.len()
            )));
        };
        Ok((ty, slot(u64::from(index))?))
    }

    fn release(&mut self, r: Reg) {
        self.free.push(r);
        // Keep allocation deterministic: lowest-listed temporary first.
        self.free
            .sort_by_key(|r| std::cmp::Reverse(TEMP_REGS.iter().position(|t| t == r)));
    }

    /// A free temporary. When none is free, the DEEPEST register-held value on
    /// the operand stack is stored to a spill slot and its register returned.
    /// Operands already popped by the current op are not on the stack, so they
    /// are never the victim.
    fn alloc(&mut self) -> Result<Reg, SelectError> {
        if let Some(r) = self.free.pop() {
            return Ok(r);
        }
        let victim = self
            .stack
            .iter()
            .enumerate()
            .find_map(|(i, v)| match v.loc {
                Loc::Reg(r) => Some((i, r)),
                Loc::Spill(_) => None,
            });
        let Some((i, r)) = victim else {
            return Err(SelectError::Malformed(
                "one op holds every temporary and none is on the operand stack".into(),
            ));
        };
        let k = match self.free_spills.pop() {
            Some(k) => k,
            None => {
                self.spills += 1;
                self.spills - 1
            }
        };
        let mem = self.spill_mem(k)?;
        self.out.push(Inst::Store {
            size: Size::Q,
            src: r,
            mem,
        });
        self.stack[i].loc = Loc::Spill(k);
        Ok(r)
    }

    fn push(&mut self, r: Reg, ty: Ty) {
        self.stack.push(Val {
            loc: Loc::Reg(r),
            ty,
        });
    }

    fn pop_any(&mut self, at: &WasmOp) -> Result<Val, SelectError> {
        self.stack
            .pop()
            .ok_or_else(|| SelectError::Malformed(format!("{at:?} pops an empty stack")))
    }

    /// Pop a value of any type INTO A REGISTER the caller then owns: its own
    /// temporary, or a fresh one a spilled value is loaded back into.
    fn pop_reg_any(&mut self, at: &WasmOp) -> Result<(Reg, Ty), SelectError> {
        let v = self.pop_any(at)?;
        match v.loc {
            Loc::Reg(r) => Ok((r, v.ty)),
            Loc::Spill(k) => {
                let r = self.alloc()?;
                let mem = self.spill_mem(k)?;
                self.out.push(Inst::Load {
                    size: Size::Q,
                    dst: r,
                    mem,
                });
                self.free_spills.push(k);
                Ok((r, v.ty))
            }
        }
    }

    /// [`Self::pop_reg_any`], requiring type `ty`.
    fn pop_reg(&mut self, at: &WasmOp, ty: Ty) -> Result<Reg, SelectError> {
        let (r, got) = self.pop_reg_any(at)?;
        if got != ty {
            return Err(SelectError::Malformed(format!(
                "{at:?} pops a {got:?} where it needs a {ty:?}"
            )));
        }
        Ok(r)
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

    /// `a = a OP b` for a two-address instruction built by `make(dst, src)`.
    fn two_address(
        &mut self,
        at: &WasmOp,
        ty: Ty,
        make: impl Fn(Reg, Reg) -> Inst,
    ) -> Result<(), SelectError> {
        let b = self.pop_reg(at, ty)?;
        let a = self.pop_reg(at, ty)?;
        self.out.push(make(a, b));
        self.release(b);
        self.push(a, ty);
        Ok(())
    }

    /// `a / b` or `a % b` with wasm's traps (see the module doc).
    fn div(&mut self, at: &WasmOp, ty: Ty, signed: bool, rem: bool) -> Result<(), SelectError> {
        let size = size_of(ty);
        let b = self.pop_reg(at, ty)?;
        let a = self.pop_reg(at, ty)?;
        // A zero divisor traps.
        self.out.push(Inst::Alu {
            op: AluOp::Test,
            size,
            dst: b,
            src: b,
        });
        self.out.extend(skip_if(Cond::Ne, vec![Inst::Ud2]));
        self.out.push(mov(size, Reg::Rax, a));
        if signed {
            self.out.push(Inst::AluImm {
                op: ImmOp::Cmp,
                size,
                dst: b,
                imm: -1,
            });
            let divisor_is_minus_one = if rem {
                // x rem -1 is 0 for every x, and idiv would fault on
                // INT_MIN: divide 0 instead (0 rem -1 is 0, no fault).
                vec![zero(Reg::Rax)]
            } else {
                // x / -1 overflows exactly for x = INT_MIN: trap.
                let int_min = 1u64 << (bits_of(ty) - 1);
                let mut v = vec![
                    const_inst(Reg::Rdx, int_min),
                    Inst::Alu {
                        op: AluOp::Cmp,
                        size,
                        dst: Reg::Rax,
                        src: Reg::Rdx,
                    },
                ];
                v.extend(skip_if(Cond::Ne, vec![Inst::Ud2]));
                v
            };
            self.out.extend(skip_if(Cond::Ne, divisor_is_minus_one));
            self.out.push(Inst::Cdq { size });
        } else {
            self.out.push(zero(Reg::Rdx));
        }
        self.out.push(Inst::Div {
            signed,
            size,
            src: b,
        });
        let result = if rem { Reg::Rdx } else { Reg::Rax };
        self.out.push(mov(size, a, result));
        self.release(b);
        self.push(a, ty);
        Ok(())
    }

    /// `clz` (`reverse`) or `ctz`: the bit index from `bsr`/`bsf`, replaced
    /// for a zero input (ZF set, destination not a defined value) by a
    /// constant that gives the operand width.
    fn bit_scan(&mut self, at: &WasmOp, ty: Ty, reverse: bool) -> Result<(), SelectError> {
        let size = size_of(ty);
        let bits = bits_of(ty);
        let a = self.pop_reg(at, ty)?;
        // clz = (bits - 1) XOR index, so the zero-input stand-in is
        // 2 * bits - 1; ctz is the index itself.
        let for_zero = if reverse { 2 * bits - 1 } else { bits };
        self.out.push(Inst::MovImm32 {
            dst: Reg::Rcx,
            imm: for_zero,
        });
        self.out.push(Inst::BitScan {
            reverse,
            size,
            dst: a,
            src: a,
        });
        self.out.push(Inst::Cmov {
            cond: Cond::E,
            size,
            dst: a,
            src: Reg::Rcx,
        });
        if reverse {
            self.out.push(Inst::AluImm {
                op: ImmOp::Xor,
                size,
                dst: a,
                imm: bits as i32 - 1,
            });
        }
        self.push(a, ty);
        Ok(())
    }

    /// `popcnt` without the `popcnt` instruction: pairwise sums in 2-, 4- and
    /// 8-bit fields, then one multiply that adds the bytes into the top byte.
    fn popcnt(&mut self, at: &WasmOp, ty: Ty) -> Result<(), SelectError> {
        let size = size_of(ty);
        let x = self.pop_reg(at, ty)?;
        let (s, mask) = (Reg::Rax, Reg::Rdx);
        // The byte pattern `b` repeated over the operand width.
        let rep = |b: u8| match ty {
            Ty::I32 => u64::from(u32::from_le_bytes([b; 4])),
            Ty::I64 => u64::from_le_bytes([b; 8]),
        };
        let alu = |op: AluOp, dst: Reg, src: Reg| Inst::Alu { op, size, dst, src };
        let shr = |dst: Reg, n: u32| {
            [
                Inst::MovImm32 {
                    dst: Reg::Rcx,
                    imm: n,
                },
                Inst::ShiftCl {
                    op: ShiftOp::Shr,
                    size,
                    dst,
                },
            ]
        };
        // x -= (x >> 1) & 0x55..
        self.out.push(mov(size, s, x));
        self.out.extend(shr(s, 1));
        self.out.push(const_inst(mask, rep(0x55)));
        self.out.push(alu(AluOp::And, s, mask));
        self.out.push(alu(AluOp::Sub, x, s));
        // x = (x & 0x33..) + ((x >> 2) & 0x33..)
        self.out.push(mov(size, s, x));
        self.out.extend(shr(s, 2));
        self.out.push(const_inst(mask, rep(0x33)));
        self.out.push(alu(AluOp::And, s, mask));
        self.out.push(alu(AluOp::And, x, mask));
        self.out.push(alu(AluOp::Add, x, s));
        // x = (x + (x >> 4)) & 0x0f..
        self.out.push(mov(size, s, x));
        self.out.extend(shr(s, 4));
        self.out.push(alu(AluOp::Add, x, s));
        self.out.push(const_inst(mask, rep(0x0F)));
        self.out.push(alu(AluOp::And, x, mask));
        // x = (x * 0x01..) >> (bits - 8)
        self.out.push(const_inst(mask, rep(0x01)));
        self.out.push(Inst::Imul {
            size,
            dst: x,
            src: mask,
        });
        self.out.extend(shr(x, bits_of(ty) - 8));
        self.push(x, ty);
        Ok(())
    }

    /// One row of the rule table.
    fn apply(&mut self, at: &WasmOp, rule: &Rule) -> Result<(), SelectError> {
        let ty = rule.ty;
        let size = size_of(ty);
        match rule.lower {
            Lowering::Alu { op } => {
                self.two_address(at, ty, |dst, src| Inst::Alu { op, size, dst, src })
            }
            Lowering::Mul => self.two_address(at, ty, |dst, src| Inst::Imul { size, dst, src }),
            Lowering::Shift(op) => {
                let b = self.pop_reg(at, ty)?;
                let a = self.pop_reg(at, ty)?;
                // The count goes in cl; the CPU masks it to the width.
                self.out.push(Inst::mov32(Reg::Rcx, b));
                self.out.push(Inst::ShiftCl { op, size, dst: a });
                self.release(b);
                self.push(a, ty);
                Ok(())
            }
            Lowering::Compare(cond) => {
                let b = self.pop_reg(at, ty)?;
                let a = self.pop_reg(at, ty)?;
                self.out.push(Inst::Alu {
                    op: AluOp::Cmp,
                    size,
                    dst: a,
                    src: b,
                });
                self.release(b);
                self.materialise(cond, a);
                Ok(())
            }
            Lowering::Eqz => {
                let a = self.pop_reg(at, ty)?;
                self.out.push(Inst::Alu {
                    op: AluOp::Test,
                    size,
                    dst: a,
                    src: a,
                });
                self.materialise(Cond::E, a);
                Ok(())
            }
            Lowering::Extend { ext, to } => {
                let a = self.pop_reg(at, ty)?;
                self.out.push(Inst::Movx {
                    ext,
                    dst: a,
                    src: a,
                });
                self.push(a, to);
                Ok(())
            }
            Lowering::ZeroExtend => {
                let a = self.pop_reg(at, ty)?;
                self.out.push(Inst::mov32(a, a));
                self.push(a, Ty::I64);
                Ok(())
            }
            Lowering::Wrap => {
                // Retyped where it is, register or spill slot.
                let a = self.pop_any(at)?;
                if a.ty != ty {
                    return Err(SelectError::Malformed(format!(
                        "{at:?} pops a {:?} where it needs a {ty:?}",
                        a.ty
                    )));
                }
                self.stack.push(Val {
                    loc: a.loc,
                    ty: Ty::I32,
                });
                Ok(())
            }
            Lowering::Div { signed, rem } => self.div(at, ty, signed, rem),
            Lowering::Clz => self.bit_scan(at, ty, true),
            Lowering::Ctz => self.bit_scan(at, ty, false),
            Lowering::Popcnt => self.popcnt(at, ty),
        }
    }

    /// `select`: `a` if the condition is nonzero, else `b`.
    fn select(&mut self, at: &WasmOp) -> Result<(), SelectError> {
        let c = self.pop_reg(at, Ty::I32)?;
        let (b, ty) = self.pop_reg_any(at)?;
        let a = self.pop_reg(at, ty)?;
        // Every operand is in a register before the test: a spill reload is
        // a `mov`, but nothing may come between `test` and `cmov`.
        self.out.push(Inst::Alu {
            op: AluOp::Test,
            size: Size::L,
            dst: c,
            src: c,
        });
        self.out.push(Inst::Cmov {
            cond: Cond::E,
            size: size_of(ty),
            dst: a,
            src: b,
        });
        self.release(c);
        self.release(b);
        self.push(a, ty);
        Ok(())
    }

    /// Move the result (if any) into `eax`/`rax`, drop the frame and return.
    fn ret(&mut self, results: &[Ty], op: &WasmOp) -> Result<(), SelectError> {
        if let Some(&ty) = results.first() {
            let r = self.pop_reg(op, ty)?;
            self.out.push(mov(size_of(ty), Reg::Rax, r));
            self.release(r);
        }
        self.out.push(mov(Size::Q, Reg::Rsp, Reg::Rbp));
        self.out.push(Inst::Pop { reg: Reg::Rbp });
        self.out.push(Inst::Ret);
        Ok(())
    }
}

/// The prologue: the frame, every parameter stored to its slot, every other
/// local's slot zeroed (wasm locals start at zero; the stack does not).
fn prologue(params: &[Ty], locals: usize, frame: u32) -> Result<Vec<Inst>, SelectError> {
    let mut v = vec![
        Inst::Push { reg: Reg::Rbp },
        mov(Size::Q, Reg::Rbp, Reg::Rsp),
    ];
    if frame != 0 {
        v.push(Inst::AluImm {
            op: ImmOp::Sub,
            size: Size::Q,
            dst: Reg::Rsp,
            imm: frame as i32,
        });
    }
    for (i, &ty) in params.iter().enumerate() {
        v.push(Inst::Store {
            size: size_of(ty),
            src: ARG_REGS[i],
            mem: slot(i as u64)?,
        });
    }
    if locals > params.len() {
        v.push(zero(Reg::Rax));
        for i in params.len()..locals {
            // All 8 bytes, whatever the local's type.
            v.push(Inst::Store {
                size: Size::Q,
                src: Reg::Rax,
                mem: slot(i as u64)?,
            });
        }
    }
    Ok(v)
}

/// Lower one function body.
///
/// `params` and `results` are the function's declared signature and `locals`
/// its declared non-parameter locals, in index order; the caller has already
/// checked that every one of them is `i32` or `i64` ([`crate::backend`] reads
/// the exact types from the module).
pub fn select(
    ops: &[WasmOp],
    params: &[Ty],
    locals: &[Ty],
    results: &[Ty],
) -> Result<Vec<Inst>, SelectError> {
    if params.len() > ARG_REGS.len() {
        return Err(SelectError::TooManyParams(params.len() as u32));
    }
    if results.len() > 1 {
        return Err(SelectError::MultiValue(results.len() as u32));
    }
    let all_locals: Vec<Ty> = params.iter().chain(locals).copied().collect();
    if let Some(last) = all_locals.len().checked_sub(1) {
        slot(last as u64)?;
    }
    let mut s = Sel {
        locals: &all_locals,
        out: Vec::new(),
        stack: Vec::new(),
        free: TEMP_REGS.iter().rev().copied().collect(),
        free_spills: Vec::new(),
        spills: 0,
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
                let (ty, mem) = s.local(op, *i)?;
                let dst = s.alloc()?;
                s.out.push(Inst::Load {
                    size: size_of(ty),
                    dst,
                    mem,
                });
                s.push(dst, ty);
            }
            WasmOp::LocalSet(i) => {
                let (ty, mem) = s.local(op, *i)?;
                let src = s.pop_reg(op, ty)?;
                s.out.push(Inst::Store {
                    size: size_of(ty),
                    src,
                    mem,
                });
                s.release(src);
            }
            WasmOp::LocalTee(i) => {
                let (ty, mem) = s.local(op, *i)?;
                let src = s.pop_reg(op, ty)?;
                s.out.push(Inst::Store {
                    size: size_of(ty),
                    src,
                    mem,
                });
                s.push(src, ty);
            }
            WasmOp::I32Const(v) => {
                let dst = s.alloc()?;
                s.out.push(const_inst(dst, u64::from(*v as u32)));
                s.push(dst, Ty::I32);
            }
            WasmOp::I64Const(v) => {
                let dst = s.alloc()?;
                s.out.push(const_inst(dst, *v as u64));
                s.push(dst, Ty::I64);
            }
            WasmOp::Select => s.select(op)?,
            WasmOp::Drop => match s.pop_any(op)?.loc {
                Loc::Reg(r) => s.release(r),
                Loc::Spill(k) => s.free_spills.push(k),
            },
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
    // The frame: one 8-byte slot per local and per spill slot, rounded up to
    // 16 so rsp stays 16-byte aligned (it is after `pushq %rbp`).
    let slots = all_locals.len() as u64 + u64::from(s.spills);
    let bytes = slots * 8;
    if bytes > u64::from(FRAME_LIMIT) {
        return Err(SelectError::FrameTooLarge(bytes));
    }
    let frame = (bytes as u32).next_multiple_of(16);
    let mut out = prologue(params, all_locals.len(), frame)?;
    out.append(&mut s.out);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use Ty::{I32, I64};
    use WasmOp::*;

    const EPILOGUE: [&str; 3] = ["movq %rbp, %rsp", "popq %rbp", "retq"];

    /// The contract on what is written and where: `rbx, r12–r15` never;
    /// `rbp` and `rsp` only by the five frame instructions; an allocated
    /// temporary or a scratch register otherwise; and every memory operand is
    /// a slot of THIS frame — `rbp`-relative, 8-byte aligned, inside the
    /// `sub`'s reservation.
    fn check_contract(insts: &[Inst]) {
        let frame = insts
            .iter()
            .find_map(|i| match *i {
                Inst::AluImm {
                    op: ImmOp::Sub,
                    size: Size::Q,
                    dst: Reg::Rsp,
                    imm,
                } => Some(imm),
                _ => None,
            })
            .unwrap_or(0);
        assert_eq!(frame % 16, 0, "frame {frame} is not 16-byte aligned");
        let frame_insts = [
            "pushq %rbp".to_string(),
            "movq %rsp, %rbp".to_string(),
            format!("subq $0x{frame:x}, %rsp"),
            "movq %rbp, %rsp".to_string(),
            "popq %rbp".to_string(),
        ];
        for i in insts {
            let text = i.att();
            for r in i.writes() {
                if CALLEE_SAVED.contains(&r) {
                    assert!(
                        matches!(r, Reg::Rbp | Reg::Rsp) && frame_insts.contains(&text),
                        "{text} writes {r:?}"
                    );
                } else {
                    assert!(
                        TEMP_REGS.contains(&r) || SCRATCH_REGS.contains(&r),
                        "{text} writes {r:?}"
                    );
                }
            }
            if let Inst::Load { mem, .. } | Inst::Store { mem, .. } = *i {
                assert_eq!(mem.base, Reg::Rbp, "{text}");
                assert!(
                    mem.disp % 8 == 0 && (-frame..=-8).contains(&mem.disp),
                    "{text} is outside the {frame}-byte frame"
                );
            }
        }
    }

    fn att(insts: &[Inst]) -> Vec<String> {
        insts.iter().map(Inst::att).collect()
    }

    fn sel_full(ops: &[WasmOp], params: &[Ty], locals: &[Ty], results: &[Ty]) -> Vec<String> {
        let v = select(ops, params, locals, results).unwrap();
        check_contract(&v);
        att(&v)
    }

    /// The BODY of a function with no declared locals: the text between the
    /// prologue (frame + one store per parameter) and the epilogue, both of
    /// which are checked to be there.
    fn sel(ops: &[WasmOp], params: &[Ty], results: &[Ty]) -> Vec<String> {
        let v = sel_full(ops, params, &[], results);
        let pro = 2 + usize::from(!params.is_empty()) + params.len();
        assert_eq!(v[0], "pushq %rbp");
        assert_eq!(v[1], "movq %rsp, %rbp");
        assert_eq!(v[v.len() - 3..], EPILOGUE);
        v[pro..v.len() - 3].to_vec()
    }

    #[test]
    fn the_frame_homes_every_parameter_at_its_own_width() {
        assert_eq!(
            sel_full(
                &[LocalGet(0), LocalGet(1), I32Add, End],
                &[I32, I32],
                &[],
                &[I32]
            ),
            [
                "pushq %rbp",
                "movq %rsp, %rbp",
                "subq $0x10, %rsp",
                "movl %edi, -0x8(%rbp)",
                "movl %esi, -0x10(%rbp)",
                "movl -0x8(%rbp), %esi",
                "movl -0x10(%rbp), %edi",
                "addl %edi, %esi",
                "movl %esi, %eax",
                "movq %rbp, %rsp",
                "popq %rbp",
                "retq"
            ]
        );
        // Six parameters of mixed width: six slots, 48 bytes, a 48-byte frame.
        let v = sel_full(
            &[LocalGet(5), End],
            &[I32, I64, I32, I64, I32, I64],
            &[],
            &[I64],
        );
        assert_eq!(
            v[2..9],
            [
                "subq $0x30, %rsp",
                "movl %edi, -0x8(%rbp)",
                "movq %rsi, -0x10(%rbp)",
                "movl %edx, -0x18(%rbp)",
                "movq %rcx, -0x20(%rbp)",
                "movl %r8d, -0x28(%rbp)",
                "movq %r9, -0x30(%rbp)",
            ]
        );
        assert_eq!(v[9..11], ["movq -0x30(%rbp), %rsi", "movq %rsi, %rax"]);
        // No parameter, no local, no spill: no `sub`.
        assert_eq!(
            sel_full(&[End], &[], &[], &[]),
            [
                "pushq %rbp",
                "movq %rsp, %rbp",
                "movq %rbp, %rsp",
                "popq %rbp",
                "retq"
            ]
        );
    }

    /// A non-parameter local's slot is zeroed in the prologue, all 8 bytes,
    /// whatever its type — the stack below `rsp` is not zero.
    #[test]
    fn declared_locals_are_zeroed_in_the_prologue() {
        let v = sel_full(&[LocalGet(2), End], &[I32], &[I32, I64, I32], &[I64]);
        assert_eq!(
            v[2..8],
            [
                "subq $0x20, %rsp",
                "movl %edi, -0x8(%rbp)",
                "xorl %eax, %eax",
                "movq %rax, -0x10(%rbp)",
                "movq %rax, -0x18(%rbp)",
                "movq %rax, -0x20(%rbp)",
            ]
        );
        assert_eq!(v[8], "movq -0x18(%rbp), %rsi");
        // Locals and no parameter: zeroed just the same.
        let v = sel_full(&[LocalGet(0), End], &[], &[I32], &[I32]);
        assert_eq!(
            v[2..6],
            [
                "subq $0x10, %rsp",
                "xorl %eax, %eax",
                "movq %rax, -0x8(%rbp)",
                "movl -0x8(%rbp), %esi"
            ]
        );
    }

    #[test]
    fn local_set_stores_and_local_tee_stores_and_keeps() {
        assert_eq!(
            sel(
                &[LocalGet(1), LocalSet(0), LocalGet(0), End],
                &[I32, I32],
                &[I32]
            ),
            [
                "movl -0x10(%rbp), %esi",
                "movl %esi, -0x8(%rbp)",
                "movl -0x8(%rbp), %esi",
                "movl %esi, %eax"
            ]
        );
        assert_eq!(
            sel(&[LocalGet(1), LocalTee(0), End], &[I64, I64], &[I64]),
            [
                "movq -0x10(%rbp), %rsi",
                "movq %rsi, -0x8(%rbp)",
                "movq %rsi, %rax"
            ]
        );
    }

    /// `local.get` copies: a value already on the operand stack keeps the
    /// local's OLD value when the local is written afterwards.
    #[test]
    fn a_value_on_the_stack_is_not_changed_by_a_later_local_set() {
        // old(p0) - new(p0), with p0 := 7 in between.
        let ops = [
            LocalGet(0),
            I32Const(7),
            LocalSet(0),
            LocalGet(0),
            I32Sub,
            End,
        ];
        assert_eq!(
            sel(&ops, &[I32], &[I32]),
            [
                "movl -0x8(%rbp), %esi",
                "movl $0x7, %edi",
                "movl %edi, -0x8(%rbp)",
                "movl -0x8(%rbp), %edi",
                "subl %edi, %esi",
                "movl %esi, %eax"
            ]
        );
    }

    #[test]
    fn a_two_address_op_computes_into_the_left_operand() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64Sub, End],
                &[I64, I64],
                &[I64]
            ),
            [
                "movq -0x8(%rbp), %rsi",
                "movq -0x10(%rbp), %rdi",
                "subq %rdi, %rsi",
                "movq %rsi, %rax"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I32Mul, End],
                &[I32, I32],
                &[I32]
            ),
            [
                "movl -0x8(%rbp), %esi",
                "movl -0x10(%rbp), %edi",
                "imull %edi, %esi",
                "movl %esi, %eax"
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
            )[2..5],
            ["cmpl %edi, %esi", "setb %sil", "movzbl %sil, %esi"]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64GeS, End],
                &[I64, I64],
                &[I32]
            )[2..5],
            ["cmpq %rdi, %rsi", "setge %sil", "movzbl %sil, %esi"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64Eqz, End], &[I64], &[I32])[1..4],
            ["testq %rsi, %rsi", "sete %sil", "movzbl %sil, %esi"]
        );
    }

    /// The count goes in `cl`. `rcx` is scratch — no parameter lives there
    /// after the prologue, whatever the parameter count.
    #[test]
    fn a_shift_moves_its_count_into_cl() {
        let p4 = [I32, I32, I32, I32];
        assert_eq!(
            sel(&[LocalGet(0), LocalGet(3), I32ShrU, End], &p4, &[I32]),
            [
                "movl -0x8(%rbp), %esi",
                "movl -0x20(%rbp), %edi",
                "movl %edi, %ecx",
                "shrl %cl, %esi",
                "movl %esi, %eax"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64Rotr, End],
                &[I64, I64],
                &[I64]
            )[2..4],
            ["movl %edi, %ecx", "rorq %cl, %rsi"]
        );
    }

    #[test]
    fn select_tests_the_condition_then_cmoves_the_else_value() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), LocalGet(2), Select, End],
                &[I64, I64, I32],
                &[I64]
            ),
            [
                "movq -0x8(%rbp), %rsi",
                "movq -0x10(%rbp), %rdi",
                "movl -0x18(%rbp), %r8d",
                "testl %r8d, %r8d",
                "cmoveq %rdi, %rsi",
                "movq %rsi, %rax"
            ]
        );
    }

    #[test]
    fn constants_pick_the_shortest_correct_move() {
        for (v, text) in [
            (0xFFFF_FFFF, "movl $0xffffffff, %esi"),
            (-1, "movq $0xffffffffffffffff, %rsi"),
            (i64::from(i32::MIN), "movq $0xffffffff80000000, %rsi"),
            (0x1_0000_0000, "movabsq $0x100000000, %rsi"),
            (i64::MIN, "movabsq $0x8000000000000000, %rsi"),
        ] {
            assert_eq!(sel(&[I64Const(v), End], &[], &[I64])[0], text);
        }
        assert_eq!(
            sel(&[I32Const(-1), End], &[], &[I32])[0],
            "movl $0xffffffff, %esi"
        );
    }

    #[test]
    fn conversions() {
        // wrap is free; extend_u re-zeroes even right after it.
        assert_eq!(
            sel(
                &[LocalGet(0), I32WrapI64, I64ExtendI32U, End],
                &[I64],
                &[I64]
            ),
            [
                "movq -0x8(%rbp), %rsi",
                "movl %esi, %esi",
                "movq %rsi, %rax"
            ]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64ExtendI32S, End], &[I32], &[I64])[1],
            "movslq %esi, %rsi"
        );
        assert_eq!(
            sel(&[LocalGet(0), I32Extend8S, End], &[I32], &[I32])[1],
            "movsbl %sil, %esi"
        );
        assert_eq!(
            sel(&[LocalGet(0), I64Extend16S, End], &[I64], &[I64])[1],
            "movswq %si, %rsi"
        );
    }

    #[test]
    fn drop_frees_its_temporary_and_nop_emits_nothing() {
        assert_eq!(
            sel(&[I32Const(1), Drop, Nop, I32Const(2), End], &[], &[I32]),
            ["movl $0x1, %esi", "movl $0x2, %esi", "movl %esi, %eax"]
        );
    }

    /// Seven values live at once with six temporaries: the DEEPEST one is
    /// stored to a spill slot and loaded back when it is popped.
    #[test]
    fn a_seventh_live_value_spills_the_deepest_one() {
        let mut ops: Vec<WasmOp> = (1..=7).map(I32Const).collect();
        ops.extend(std::iter::repeat_n(I32Sub, 6));
        ops.push(End);
        let v = sel_full(&ops, &[], &[], &[I32]);
        assert_eq!(
            v,
            [
                "pushq %rbp",
                "movq %rsp, %rbp",
                "subq $0x10, %rsp",
                "movl $0x1, %esi",
                "movl $0x2, %edi",
                "movl $0x3, %r8d",
                "movl $0x4, %r9d",
                "movl $0x5, %r10d",
                "movl $0x6, %r11d",
                // No temporary left: 1, the deepest, goes to spill slot 0.
                "movq %rsi, -0x8(%rbp)",
                "movl $0x7, %esi",
                "subl %esi, %r11d",
                "subl %r11d, %r10d",
                "subl %r10d, %r9d",
                "subl %r9d, %r8d",
                "subl %r8d, %edi",
                // 1 comes back for the last subtraction.
                "movq -0x8(%rbp), %rsi",
                "subl %edi, %esi",
                "movl %esi, %eax",
                "movq %rbp, %rsp",
                "popq %rbp",
                "retq"
            ]
        );
    }

    /// Spill slots sit BELOW the locals, are reused once free, and a dropped
    /// spilled value frees its slot without a load.
    #[test]
    fn spill_slots_follow_the_locals_and_are_reused() {
        // One param and one local: spill slot 0 is the third slot.
        let mut ops: Vec<WasmOp> = (1..=7).map(I32Const).collect();
        ops.extend(std::iter::repeat_n(Drop, 7));
        // A second round: the slot is free again and reused.
        ops.extend((1..=7).map(I32Const));
        ops.extend(std::iter::repeat_n(Drop, 6));
        ops.push(End);
        let v = sel_full(&ops, &[I32], &[I32], &[I32]);
        assert_eq!(v[2], "subq $0x20, %rsp");
        let spills: Vec<&String> = v.iter().filter(|l| l.starts_with("movq %rsi, -")).collect();
        assert_eq!(spills, ["movq %rsi, -0x18(%rbp)"; 2]);
        // The first round's spilled value was dropped: one load, the result.
        let loads = v.iter().filter(|l| l.starts_with("movq -0x18")).count();
        assert_eq!(loads, 1);
    }

    /// A spilled operand of `select` is loaded BEFORE the `test`: nothing
    /// that could be confused with a flag-writer sits between `test` and
    /// `cmov`.
    #[test]
    fn select_reloads_every_operand_before_the_test() {
        // Six values under the select's three operands: all three operands
        // are in registers, the six below them all spilled or about to be.
        let mut ops: Vec<WasmOp> = (1..=9).map(I32Const).collect();
        ops.push(Select);
        ops.extend(std::iter::repeat_n(I32Add, 6));
        ops.push(End);
        let v = sel_full(&ops, &[], &[], &[I32]);
        let t = v.iter().position(|l| l.starts_with("testl")).unwrap();
        assert!(v[t + 1].starts_with("cmovel"), "{:?}", &v[t..t + 2]);
    }

    #[test]
    fn division_guards_come_before_the_divide() {
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I32DivS, End],
                &[I32, I32],
                &[I32]
            ),
            [
                "movl -0x8(%rbp), %esi",
                "movl -0x10(%rbp), %edi",
                // divisor == 0: trap.
                "testl %edi, %edi",
                "{disp32} jne .+0x8",
                "ud2",
                "movl %esi, %eax",
                // divisor == -1 and dividend == INT_MIN: trap.
                "cmpl $0xffffffff, %edi",
                "{disp32} jne .+0x15",
                "movl $0x80000000, %edx",
                "cmpl %edx, %eax",
                "{disp32} jne .+0x8",
                "ud2",
                "cltd",
                "idivl %edi",
                "movl %eax, %esi",
                "movl %esi, %eax"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64RemS, End],
                &[I64, I64],
                &[I64]
            )[2..],
            [
                "testq %rdi, %rdi",
                "{disp32} jne .+0x8",
                "ud2",
                "movq %rsi, %rax",
                // divisor == -1: divide 0, so the remainder is 0 and idiv
                // cannot overflow.
                "cmpq $0xffffffffffffffff, %rdi",
                "{disp32} jne .+0x8",
                "xorl %eax, %eax",
                "cqto",
                "idivq %rdi",
                "movq %rdx, %rsi",
                "movq %rsi, %rax"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I32RemU, End],
                &[I32, I32],
                &[I32]
            )[2..],
            [
                "testl %edi, %edi",
                "{disp32} jne .+0x8",
                "ud2",
                "movl %esi, %eax",
                "xorl %edx, %edx",
                "divl %edi",
                "movl %edx, %esi",
                "movl %esi, %eax"
            ]
        );
        assert_eq!(
            sel(
                &[LocalGet(0), LocalGet(1), I64DivU, End],
                &[I64, I64],
                &[I64]
            )[5..],
            [
                "movq %rsi, %rax",
                "xorl %edx, %edx",
                "divq %rdi",
                "movq %rax, %rsi",
                "movq %rsi, %rax"
            ]
        );
    }

    /// Every branch lands exactly on an instruction boundary of its own
    /// function, forward, and every `div`/`idiv` and `ud2` is preceded by a
    /// branch that can skip it or reach past it.
    #[test]
    fn every_branch_targets_an_instruction_boundary() {
        for op in [
            I32DivS, I32DivU, I32RemS, I32RemU, I64DivS, I64DivU, I64RemS, I64RemU,
        ] {
            let ty = rule_for(&op).unwrap().ty;
            let ops = [LocalGet(0), LocalGet(1), op.clone(), End];
            let v = select(&ops, &[ty, ty], &[], &[ty]).unwrap();
            check_contract(&v);
            let mut starts = vec![0usize];
            for i in &v {
                starts.push(starts.last().unwrap() + encode(i).len());
            }
            let mut branches = 0;
            for (k, i) in v.iter().enumerate() {
                if let Inst::Jcc { rel, .. } = *i {
                    assert!(rel > 0, "{op:?}: a backward or empty branch");
                    let target = starts[k + 1] + rel as usize;
                    assert!(
                        starts.contains(&target),
                        "{op:?}: branch into an instruction"
                    );
                    branches += 1;
                }
            }
            let traps = v.iter().filter(|i| **i == Inst::Ud2).count();
            let signed_div = matches!(op, I32DivS | I64DivS);
            assert_eq!(traps, if signed_div { 2 } else { 1 }, "{op:?}");
            // One branch per trap, and one more for the signed "divisor is
            // -1" test (which guards a trap for div_s, a zeroing for rem_s).
            let signed = matches!(op, I32DivS | I64DivS | I32RemS | I64RemS);
            assert_eq!(branches, traps + usize::from(signed), "{op:?}");
            assert_eq!(
                v.iter().filter(|i| matches!(i, Inst::Div { .. })).count(),
                1
            );
        }
    }

    #[test]
    fn bit_counts_use_baseline_instructions_only() {
        assert_eq!(
            sel(&[LocalGet(0), I32Clz, End], &[I32], &[I32])[1..5],
            [
                "movl $0x3f, %ecx",
                "bsrl %esi, %esi",
                "cmovel %ecx, %esi",
                "xorl $0x1f, %esi"
            ]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64Clz, End], &[I64], &[I64])[1..5],
            [
                "movl $0x7f, %ecx",
                "bsrq %rsi, %rsi",
                "cmoveq %rcx, %rsi",
                "xorq $0x3f, %rsi"
            ]
        );
        assert_eq!(
            sel(&[LocalGet(0), I32Ctz, End], &[I32], &[I32])[1..4],
            ["movl $0x20, %ecx", "bsfl %esi, %esi", "cmovel %ecx, %esi"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I64Ctz, End], &[I64], &[I64])[1..4],
            ["movl $0x40, %ecx", "bsfq %rsi, %rsi", "cmoveq %rcx, %rsi"]
        );
        assert_eq!(
            sel(&[LocalGet(0), I32Popcnt, End], &[I32], &[I32]),
            [
                "movl -0x8(%rbp), %esi",
                "movl %esi, %eax",
                "movl $0x1, %ecx",
                "shrl %cl, %eax",
                "movl $0x55555555, %edx",
                "andl %edx, %eax",
                "subl %eax, %esi",
                "movl %esi, %eax",
                "movl $0x2, %ecx",
                "shrl %cl, %eax",
                "movl $0x33333333, %edx",
                "andl %edx, %eax",
                "andl %edx, %esi",
                "addl %eax, %esi",
                "movl %esi, %eax",
                "movl $0x4, %ecx",
                "shrl %cl, %eax",
                "addl %eax, %esi",
                "movl $0xf0f0f0f, %edx",
                "andl %edx, %esi",
                "movl $0x1010101, %edx",
                "imull %edx, %esi",
                "movl $0x18, %ecx",
                "shrl %cl, %esi",
                "movl %esi, %eax"
            ]
        );
        let v = sel(&[LocalGet(0), I64Popcnt, End], &[I64], &[I64]);
        for needle in [
            "movabsq $0x5555555555555555, %rdx",
            "movabsq $0x3333333333333333, %rdx",
            "movabsq $0xf0f0f0f0f0f0f0f, %rdx",
            "movabsq $0x101010101010101, %rdx",
            "movl $0x38, %ecx",
            "imulq %rdx, %rsi",
        ] {
            assert!(v.iter().any(|l| l == needle), "no `{needle}` in {v:?}");
        }
    }

    #[test]
    fn return_then_end_and_nothing_else() {
        let v = select(&[LocalGet(1), Return, End], &[I32, I32], &[], &[I32]).unwrap();
        check_contract(&v);
        assert_eq!(att(&v[v.len() - 3..]), EPILOGUE);
        assert_eq!(v.iter().filter(|i| **i == Inst::Ret).count(), 1);
        assert_eq!(
            select(
                &[LocalGet(1), Return, LocalGet(0), End],
                &[I32, I32],
                &[],
                &[I32]
            ),
            Err(SelectError::AfterReturn(LocalGet(0)))
        );
        // `return` with more on the stack than the result: the top is it.
        assert_eq!(
            sel(&[I32Const(1), I32Const(2), Return, End], &[], &[I32]),
            ["movl $0x1, %esi", "movl $0x2, %edi", "movl %edi, %eax"]
        );
    }

    /// The frame limit: 512 slots fit, the 513th is declined by name —
    /// whether it is a local or a spill slot.
    #[test]
    fn a_frame_above_the_limit_is_declined() {
        let ok = vec![I64; 512];
        let v = sel_full(&[End], &[], &ok, &[]);
        assert_eq!(v[2], "subq $0x1000, %rsp");
        assert_eq!(
            select(&[End], &[], &[I64; 513], &[]),
            Err(SelectError::FrameTooLarge(4104))
        );
        // 512 locals and one spill.
        let mut ops: Vec<WasmOp> = (1..=7).map(I32Const).collect();
        ops.extend(std::iter::repeat_n(Drop, 7));
        ops.push(End);
        let e = select(&ops, &[], &ok, &[]).unwrap_err();
        assert_eq!(e, SelectError::FrameTooLarge(4104));
        assert!(e.to_string().contains("stack probe"), "{e}");
    }

    #[test]
    fn declines_name_their_cause() {
        assert_eq!(
            select(&[LocalGet(0), End], &[I32; 7], &[], &[I32]),
            Err(SelectError::TooManyParams(7))
        );
        assert_eq!(
            select(&[End], &[], &[], &[I32, I32]),
            Err(SelectError::MultiValue(2))
        );
        assert_eq!(
            select(&[LocalGet(0)], &[I32], &[], &[I32]),
            Err(SelectError::NoFinalEnd)
        );
        for op in [Call(0), Unreachable, Block, Loop, F32Add, GlobalGet(0)] {
            let e = select(&[op.clone(), End], &[I32], &[], &[]).unwrap_err();
            assert_eq!(e, SelectError::Unsupported(op.clone()));
            assert!(e.to_string().contains(&format!("{op:?}")), "{e}");
        }
    }

    /// A type the stack does not hold, or a local that does not exist, is a
    /// malformed body, never a guess.
    #[test]
    fn a_mistyped_stack_is_malformed() {
        for (ops, params, locals, results) in [
            (
                vec![LocalGet(0), LocalGet(1), I64Add, End],
                vec![I32, I64],
                vec![],
                I64,
            ),
            (vec![LocalGet(0), End], vec![I32, I32], vec![], I64),
            (
                vec![LocalGet(0), LocalGet(1), LocalGet(0), Select, End],
                vec![I32, I64],
                vec![],
                I32,
            ),
            // An i64 stored to an i32 local, through set and through tee.
            (
                vec![LocalGet(0), LocalSet(1), I32Const(0), End],
                vec![I64],
                vec![I32],
                I32,
            ),
            (
                vec![LocalGet(0), LocalTee(1), End],
                vec![I64],
                vec![I32],
                I64,
            ),
            // A local index past the declared locals.
            (vec![LocalGet(2), End], vec![I32], vec![I32], I32),
            (vec![I32Const(0), LocalSet(1), End], vec![I32], vec![], I32),
            (vec![LocalGet(0), I32WrapI64, End], vec![I32], vec![], I32),
        ] {
            assert!(
                matches!(
                    select(&ops, &params, &locals, &[results]),
                    Err(SelectError::Malformed(_))
                ),
                "{ops:?}"
            );
        }
    }
}
