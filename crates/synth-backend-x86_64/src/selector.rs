//! The x86-64 instruction selector — lanes X1 to X5 (RQ-91-X86SKEL,
//! RQ-91-X86ALU, RQ-91-X86FRAME, RQ-91-X86CTRL, #1741).
//!
//! LOWERED: integer code in a LEAF function of at most six i32/i64
//! parameters, any i32/i64 locals that fit the frame limit, and zero or one
//! i32/i64 result — `local.get`/`local.set`/`local.tee`,
//! `i32.const`/`i64.const`, the ops of the rule table
//! ([`crate::rules::RULES`]: add, sub, mul, and, or, xor, the shifts and
//! rotates, the compares and `eqz`, the extensions and `wrap`, `div`/`rem`
//! with their trap guards, `clz`/`ctz`/`popcnt`), `select`, `drop`, `nop`,
//! `return`, and (lane X5) structured control flow: `block`, `loop`,
//! `if`/`else`, `br`, `br_if`, `br_table` of at most 16 targets,
//! `unreachable` and `end`, with block types of zero or one i32/i64 result.
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
//! encoder, so there is no label and no size estimate. `unreachable` is a
//! bare `ud2`.
//!
//! CONTROL FLOW (lane X5). The frame record, the label-arity rule, the
//! blocktype ordinal, the dead-code skip and the join rule are
//! [`synth_core::lower`], shared with the AArch64 selector; this module only
//! emits. Every branch is `jmp rel32` or `jCC rel32` (no short form, no
//! relaxation), recorded as an instruction index and resolved once the body
//! is complete, from the encoder's lengths (an instruction's length does not
//! depend on its displacement). THE REGISTER STATE AT A JOIN is made the same
//! on every edge by one rule: when a `block`, `loop` or `if` opens, every
//! value on the operand stack is stored to the HOME slot of its depth (its
//! register freed), so every value beneath a frame lives in memory while the
//! frame is open — nothing inside can spill, move or overwrite it, because
//! the allocator only ever spills register-held values and live code never
//! pops below its frame's entry height (dead code, which may, is skipped). A
//! value a label carries goes to the home slot of the label's entry height,
//! on every edge into it (a fall-through `end` or `else`, a `br`, a taken
//! `br_if`, a `br_table` entry), and the join reads it from there. At every
//! label all six temporaries are free and no spill slot is live. A branch to
//! the function body itself is a return: its value goes to home slot 0 and
//! the shared epilogue loads it into `rax`. Home slots sit in the frame below
//! the spill slots, so a function without control flow is laid out — and
//! encoded — exactly as before lane X5.

use synth_core::WasmOp;
use synth_core::lower::{self, BlockTypeDecline, Control, ElseError, FrameKind};

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

/// The most `br_table` targets lowered (besides the default). Each is a
/// compare and a branch; a jump table is not built.
pub const BR_TABLE_LIMIT: usize = 16;

/// A block type, read from the module: its parameter count and its result
/// types (only i32 and i64 reach the selector; the backend refuses others).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BlockSig {
    pub params: usize,
    pub results: Vec<Ty>,
}

/// The largest frame lowered, in bytes below `rbp`. One page: a larger frame
/// could step over a guard page without touching it, and no stack probe is
/// emitted.
pub const FRAME_LIMIT: u32 = 4096;

/// Why a function was not lowered. Every variant names its cause.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum SelectError {
    /// The op has no x86-64 lowering in this lane.
    #[error(
        "x86_64: unsupported wasm op {0:?} (lanes X1-X5 lower i32/i64 integer code only: const, local.get/set/tee, add/sub/mul/and/or/xor, shifts and rotates, compares, extensions, div/rem, clz/ctz/popcnt, select, drop, return, block/loop/if/else/br/br_if/br_table/unreachable)"
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
    /// A block type with parameters, or with more than one result: a label
    /// carries at most one value here.
    #[error(
        "x86_64: {op:?} #{ord} has a block type with {what}, which is not lowered (a label carries at most one value)"
    )]
    BlockType {
        op: WasmOp,
        ord: usize,
        what: &'static str,
    },
    /// A `br_table` with more targets than [`BR_TABLE_LIMIT`].
    #[error(
        "x86_64: br_table with {0} targets; at most {BR_TABLE_LIMIT} are lowered (each is a compare and a branch; no jump table is built)"
    )]
    BrTableTargets(usize),
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
    /// The HOME slot of operand-stack depth `d`: where the value at depth `d`
    /// lives once a control frame has opened above it (module doc). Only the
    /// value at depth `d` ever lives there.
    Home(u32),
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
    /// The frame slot index of home slot 0, and how many home slots were used.
    home_base: u64,
    homes: u32,
    /// Branches to resolve once the body is complete: (the branch's
    /// instruction index, the target's instruction index).
    links: Vec<(usize, usize)>,
}

impl Sel<'_> {
    fn spill_mem(&self, k: u32) -> Result<Mem, SelectError> {
        slot(self.locals.len() as u64 + u64::from(k))
    }

    fn home_mem(&mut self, d: u32) -> Result<Mem, SelectError> {
        self.homes = self.homes.max(d + 1);
        slot(self.home_base + u64::from(d))
    }

    /// Give back whatever `v` held.
    fn release_val(&mut self, v: Val) {
        match v.loc {
            Loc::Reg(r) => self.release(r),
            Loc::Spill(k) => self.free_spills.push(k),
            Loc::Home(_) => {}
        }
    }

    /// Cut the operand stack to `n` values, releasing what the rest held.
    fn truncate(&mut self, n: usize) {
        while self.stack.len() > n {
            let v = self.stack.pop().expect("longer than n");
            self.release_val(v);
        }
    }

    /// Store every value on the operand stack to the home slot of its depth
    /// (module doc). Afterwards no temporary and no spill slot is in use by
    /// the stack. Only `mov`s: EFLAGS are untouched.
    fn flush(&mut self) -> Result<(), SelectError> {
        for d in 0..self.stack.len() {
            let v = self.stack[d];
            let depth = d as u32;
            match v.loc {
                Loc::Home(h) if h == depth => continue,
                Loc::Home(h) => {
                    return Err(SelectError::Malformed(format!(
                        "the operand at depth {d} lives in the home slot of depth {h}"
                    )));
                }
                Loc::Reg(r) => {
                    let mem = self.home_mem(depth)?;
                    self.out.push(Inst::Store {
                        size: Size::Q,
                        src: r,
                        mem,
                    });
                    self.release(r);
                }
                Loc::Spill(k) => {
                    let from = self.spill_mem(k)?;
                    let mem = self.home_mem(depth)?;
                    self.out.push(Inst::Load {
                        size: Size::Q,
                        dst: Reg::Rax,
                        mem: from,
                    });
                    self.out.push(Inst::Store {
                        size: Size::Q,
                        src: Reg::Rax,
                        mem,
                    });
                    self.free_spills.push(k);
                }
            }
            self.stack[d].loc = Loc::Home(depth);
        }
        Ok(())
    }

    /// Whether the top value is somewhere other than home slot `e`.
    fn top_not_home(&self, e: u32) -> bool {
        !matches!(self.stack.last(), Some(Val { loc: Loc::Home(d), .. }) if *d == e)
    }

    /// COPY the top value (of type `ty`, at depth `e` or above) into home slot
    /// `e`, where a label of entry height `e` reads its value. The value stays
    /// where it is. Only `mov`s, through `rax`.
    fn copy_top_home(&mut self, at: &WasmOp, e: usize, ty: Ty) -> Result<(), SelectError> {
        let Some(&v) = self.stack.last() else {
            return Err(SelectError::Malformed(format!(
                "{at:?} carries a value from an empty stack"
            )));
        };
        if self.stack.len() <= e || v.ty != ty {
            return Err(SelectError::Malformed(format!(
                "{at:?} carries a {:?} at depth {} to a label of type {ty:?} at height {e}",
                v.ty,
                self.stack.len() - 1
            )));
        }
        let e = e as u32;
        let to = self.home_mem(e)?;
        let from = match v.loc {
            Loc::Home(d) if d == e => return Ok(()),
            Loc::Reg(r) => {
                self.out.push(Inst::Store {
                    size: Size::Q,
                    src: r,
                    mem: to,
                });
                return Ok(());
            }
            Loc::Home(d) => self.home_mem(d)?,
            Loc::Spill(k) => self.spill_mem(k)?,
        };
        self.out.push(Inst::Load {
            size: Size::Q,
            dst: Reg::Rax,
            mem: from,
        });
        self.out.push(Inst::Store {
            size: Size::Q,
            src: Reg::Rax,
            mem: to,
        });
        Ok(())
    }

    /// A fall-through edge into the label of a frame with entry height `e`:
    /// the stack must hold exactly the frame's result (if any), which goes to
    /// home slot `e`.
    fn fall_into(&mut self, at: &WasmOp, e: usize, result: Option<Ty>) -> Result<(), SelectError> {
        let want = e + usize::from(result.is_some());
        if self.stack.len() != want {
            return Err(SelectError::Malformed(format!(
                "{} value(s) on the stack at {at:?}, the frame expects {want}",
                self.stack.len()
            )));
        }
        match result {
            Some(ty) => self.copy_top_home(at, e, ty),
            None => Ok(()),
        }
    }

    /// Emit a branch with a displacement to be resolved; its index.
    fn branch(&mut self, inst: Inst) -> usize {
        self.out.push(inst);
        self.out.len() - 1
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
                Loc::Spill(_) | Loc::Home(_) => None,
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
            Loc::Home(d) => {
                let r = self.alloc()?;
                let mem = self.home_mem(d)?;
                self.out.push(Inst::Load {
                    size: Size::Q,
                    dst: r,
                    mem,
                });
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
        self.epilogue();
        Ok(())
    }

    /// Drop the frame and return.
    fn epilogue(&mut self) {
        self.out.push(mov(Size::Q, Reg::Rsp, Reg::Rbp));
        self.out.push(Inst::Pop { reg: Reg::Rbp });
        self.out.push(Inst::Ret);
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

/// Lower one function body whose block types are all void (hand-built op
/// streams carry no block-type table). See [`select_function`].
pub fn select(
    ops: &[WasmOp],
    params: &[Ty],
    locals: &[Ty],
    results: &[Ty],
) -> Result<Vec<Inst>, SelectError> {
    select_function(ops, params, locals, results, &[])
}

/// Lower one function body.
///
/// `params` and `results` are the function's declared signature and `locals`
/// its declared non-parameter locals, in index order; the caller has already
/// checked that every one of them is `i32` or `i64` ([`crate::backend`] reads
/// the exact types from the module). `blocks` is the type of every `block`,
/// `loop` and `if` in op order (dead ones included); an op past its end is a
/// void block.
pub fn select_function(
    ops: &[WasmOp],
    params: &[Ty],
    locals: &[Ty],
    results: &[Ty],
    blocks: &[BlockSig],
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
    // The home slots sit below the spill slots, whose count is known only
    // once the body is lowered. So a body that uses them is lowered TWICE:
    // the first pass counts the spill slots (its home addresses are
    // provisional and its output is dropped), the second places the homes
    // below them. No decision of the lowering reads an address, so both
    // passes make the same decisions; that is checked.
    let base = all_locals.len() as u64;
    let first = lower_body(ops, &all_locals, results, blocks, base)?;
    let body = if first.homes == 0 {
        first
    } else {
        let second = lower_body(
            ops,
            &all_locals,
            results,
            blocks,
            base + u64::from(first.spills),
        )?;
        if (second.spills, second.homes) != (first.spills, first.homes) {
            return Err(SelectError::Malformed(format!(
                "the two passes disagree: {} spill and {} home slots, then {} and {}",
                first.spills, first.homes, second.spills, second.homes
            )));
        }
        second
    };
    // The frame: one 8-byte slot per local, per spill slot and per home slot,
    // rounded up to 16 so rsp stays 16-byte aligned (it is after `pushq
    // %rbp`).
    let slots = base + u64::from(body.spills) + u64::from(body.homes);
    let bytes = slots * 8;
    if bytes > u64::from(FRAME_LIMIT) {
        return Err(SelectError::FrameTooLarge(bytes));
    }
    let frame = (bytes as u32).next_multiple_of(16);
    let mut out = prologue(params, all_locals.len(), frame)?;
    out.extend(body.out);
    Ok(out)
}

/// One lowered body, without its prologue.
struct Lowered {
    out: Vec<Inst>,
    spills: u32,
    homes: u32,
}

type Frame = lower::Frame<usize, Ty>;
type Kind = FrameKind<usize>;

/// The frame a `block`/`loop`/`if` opens: its label and result arity
/// ([`lower::label_arities`], the shared rule) and its result type.
fn open_frame(
    ctl: &mut Control<usize, Ty>,
    op: &WasmOp,
    blocks: &[BlockSig],
    arities: &[(u8, u8)],
) -> Result<(u8, u8, Option<Ty>), SelectError> {
    let is_loop = matches!(op, WasmOp::Loop);
    let (ord, arity) = ctl.block_type(arities);
    let (label_arity, result_arity) =
        lower::label_arities(arity, is_loop).map_err(|d| SelectError::BlockType {
            op: op.clone(),
            ord,
            what: match d {
                BlockTypeDecline::Params => "parameters",
                BlockTypeDecline::MultiValue => "more than one result",
            },
        })?;
    let ty = if result_arity == 1 {
        Some(
            blocks
                .get(ord)
                .and_then(|b| b.results.first().copied())
                .ok_or_else(|| {
                    SelectError::Malformed(format!("{op:?} #{ord} has no result type"))
                })?,
        )
    } else {
        None
    };
    Ok((label_arity, result_arity, ty))
}

fn new_frame(kind: Kind, stack_entry: usize, arity: (u8, u8, Option<Ty>)) -> Frame {
    Frame {
        kind,
        pending: Vec::new(),
        dead_skip: None,
        stack_entry,
        label_arity: arity.0,
        result_arity: arity.1,
        slot: arity.2,
    }
}

/// The frame a branch of relative depth `depth` targets.
fn target(ctl: &Control<usize, Ty>, at: &WasmOp, depth: u32) -> Result<usize, SelectError> {
    ctl.target(depth).ok_or_else(|| {
        SelectError::Malformed(format!(
            "{at:?}: depth {depth} with {} label(s) open",
            ctl.depth()
        ))
    })
}

/// What a branch to frame `t` must hand over: `Some((entry height, type))`
/// when its label carries a value.
fn carried(
    ctl: &Control<usize, Ty>,
    at: &WasmOp,
    t: usize,
) -> Result<Option<(usize, Ty)>, SelectError> {
    let f = &ctl.frames()[t];
    if f.label_arity == 0 {
        return Ok(None);
    }
    let ty = f
        .slot
        .ok_or_else(|| SelectError::Malformed(format!("{at:?}: a valued label has no type")))?;
    Ok(Some((f.stack_entry, ty)))
}

/// Record the branch at instruction `pos` as an edge to frame `t`'s label: a
/// loop's header is known (backward), a block's or if's end is not yet
/// (forward, resolved at its `end`).
fn record(s: &mut Sel, ctl: &mut Control<usize, Ty>, t: usize, pos: usize) {
    match ctl.frames()[t].kind {
        Kind::Loop { entry } => s.links.push((pos, entry)),
        Kind::Block | Kind::If { .. } => ctl.frames_mut()[t].pending.push(pos),
    }
}

/// A CONDITIONAL edge to frame `t`, taken when `cond` holds (the flags are
/// already set). When the label carries a value that is not yet in its home
/// slot, the copy runs on the taken path only: the home slot of the label's
/// entry height may hold a live value on the path that falls through.
fn cond_edge(
    s: &mut Sel,
    ctl: &mut Control<usize, Ty>,
    at: &WasmOp,
    t: usize,
    cond: Cond,
) -> Result<(), SelectError> {
    if let Some((e, ty)) = carried(ctl, at, t)?
        && s.top_not_home(e as u32)
    {
        let over = s.branch(Inst::Jcc {
            cond: cond.negate(),
            rel: 0,
        });
        s.copy_top_home(at, e, ty)?;
        let pos = s.branch(Inst::Jmp { rel: 0 });
        record(s, ctl, t, pos);
        let here = s.out.len();
        s.links.push((over, here));
    } else {
        let pos = s.branch(Inst::Jcc { cond, rel: 0 });
        record(s, ctl, t, pos);
    }
    Ok(())
}

/// An UNCONDITIONAL edge to frame `t`.
fn edge(
    s: &mut Sel,
    ctl: &mut Control<usize, Ty>,
    at: &WasmOp,
    t: usize,
) -> Result<(), SelectError> {
    if let Some((e, ty)) = carried(ctl, at, t)? {
        s.copy_top_home(at, e, ty)?;
    }
    let pos = s.branch(Inst::Jmp { rel: 0 });
    record(s, ctl, t, pos);
    Ok(())
}

/// Write each recorded branch's displacement, from the encoder's lengths. A
/// branch's length does not depend on its displacement (always rel32).
fn resolve(out: &mut [Inst], links: &[(usize, usize)]) -> Result<(), SelectError> {
    let mut off = Vec::with_capacity(out.len() + 1);
    let mut at = 0usize;
    for i in out.iter() {
        off.push(at);
        at += encode(i).len();
    }
    off.push(at);
    for &(b, t) in links {
        let rel = i32::try_from(off[t] as i64 - off[b + 1] as i64)
            .map_err(|_| SelectError::Malformed("a branch beyond rel32".into()))?;
        match &mut out[b] {
            Inst::Jcc { rel: r, .. } | Inst::Jmp { rel: r } => *r = rel,
            other => {
                return Err(SelectError::Malformed(format!(
                    "a branch was recorded at `{other}`"
                )));
            }
        }
    }
    Ok(())
}

fn lower_body(
    ops: &[WasmOp],
    all_locals: &[Ty],
    results: &[Ty],
    blocks: &[BlockSig],
    home_base: u64,
) -> Result<Lowered, SelectError> {
    let arities: Vec<(u8, u8)> = blocks
        .iter()
        .map(|b| {
            (
                u8::try_from(b.params).unwrap_or(u8::MAX),
                u8::try_from(b.results.len()).unwrap_or(u8::MAX),
            )
        })
        .collect();
    let mut s = Sel {
        locals: all_locals,
        out: Vec::new(),
        stack: Vec::new(),
        free: TEMP_REGS.iter().rev().copied().collect(),
        free_spills: Vec::new(),
        spills: 0,
        home_base,
        homes: 0,
        links: Vec::new(),
    };
    let mut ctl: Control<usize, Ty> = Control::new();
    // The function body is the OUTERMOST frame: its label is the function's
    // end, so a `br` to it returns, carrying the function's result.
    let n = results.len() as u8;
    ctl.open(new_frame(Kind::Block, 0, (n, n, results.first().copied())));
    let mut ended = false;
    for op in ops {
        if ended {
            return Err(SelectError::Malformed(format!(
                "{op:?} follows the function's final `end`"
            )));
        }
        // Code after `br`/`br_table`/`return`/`unreachable` is dead: wasm
        // validates it against a polymorphic stack, so it may pop values that
        // are not there. It is skipped, never lowered (the shared rule).
        if ctl.skip_dead(op) {
            continue;
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
            WasmOp::Drop => {
                let v = s.pop_any(op)?;
                s.release_val(v);
            }
            WasmOp::Nop => {}
            WasmOp::Return => {
                s.ret(results, op)?;
                ctl.transfer();
            }
            WasmOp::Unreachable => {
                s.out.push(Inst::Ud2);
                ctl.transfer();
            }
            WasmOp::Block | WasmOp::Loop => {
                let arity = open_frame(&mut ctl, op, blocks, &arities)?;
                s.flush()?;
                let kind = if matches!(op, WasmOp::Loop) {
                    Kind::Loop { entry: s.out.len() }
                } else {
                    Kind::Block
                };
                ctl.open(new_frame(kind, s.stack.len(), arity));
            }
            WasmOp::If => {
                let arity = open_frame(&mut ctl, op, blocks, &arities)?;
                let c = s.pop_reg(op, Ty::I32)?;
                s.flush()?;
                s.out.push(Inst::Alu {
                    op: AluOp::Test,
                    size: Size::L,
                    dst: c,
                    src: c,
                });
                // To the else arm, or past the then arm, when the condition
                // is zero.
                let skip = s.branch(Inst::Jcc {
                    cond: Cond::E,
                    rel: 0,
                });
                s.release(c);
                let kind = Kind::If {
                    else_fixup: Some(skip),
                };
                ctl.open(new_frame(kind, s.stack.len(), arity));
            }
            WasmOp::Else => {
                let skip_then = ctl.begin_else().map_err(|e| {
                    SelectError::Malformed(
                        match e {
                            ElseError::NoFrame => "else with no open frame",
                            ElseError::Duplicate => "a second else for one if",
                            ElseError::NotIf => "else closes a frame that is not an if",
                        }
                        .into(),
                    )
                })?;
                let f = ctl.frames().last().expect("begin_else found the if");
                let (entry, result) = (f.stack_entry, f.slot);
                // A live then arm hands the join its result and jumps over
                // the else arm; a dead one emits nothing.
                let over_else = if ctl.reachable() {
                    s.fall_into(op, entry, result)?;
                    Some(s.branch(Inst::Jmp { rel: 0 }))
                } else {
                    None
                };
                s.truncate(entry);
                ctl.enter_else(over_else);
                let here = s.out.len();
                s.links.push((skip_then, here));
            }
            WasmOp::Br(depth) => {
                let t = target(&ctl, op, *depth)?;
                edge(&mut s, &mut ctl, op, t)?;
                ctl.transfer();
            }
            WasmOp::BrIf(depth) => {
                let t = target(&ctl, op, *depth)?;
                let c = s.pop_reg(op, Ty::I32)?;
                s.out.push(Inst::Alu {
                    op: AluOp::Test,
                    size: Size::L,
                    dst: c,
                    src: c,
                });
                cond_edge(&mut s, &mut ctl, op, t, Cond::Ne)?;
                s.release(c);
            }
            WasmOp::BrTable { targets, default } => {
                if targets.len() > BR_TABLE_LIMIT {
                    return Err(SelectError::BrTableTargets(targets.len()));
                }
                let ts: Vec<usize> = targets
                    .iter()
                    .map(|d| target(&ctl, op, *d))
                    .collect::<Result<_, _>>()?;
                let dflt = target(&ctl, op, *default)?;
                let idx = s.pop_reg(op, Ty::I32)?;
                // One compare per index; an index past the last (unsigned,
                // so a negative one too) falls to the default.
                for (i, &t) in ts.iter().enumerate() {
                    s.out.push(Inst::AluImm {
                        op: ImmOp::Cmp,
                        size: Size::L,
                        dst: idx,
                        imm: i as i32,
                    });
                    cond_edge(&mut s, &mut ctl, op, t, Cond::E)?;
                }
                edge(&mut s, &mut ctl, op, dflt)?;
                s.release(idx);
                ctl.transfer();
            }
            WasmOp::End => {
                let f = ctl
                    .frames()
                    .last()
                    .ok_or_else(|| SelectError::Malformed("end with no open frame".into()))?;
                let (entry, result) = (f.stack_entry, f.slot);
                let function = ctl.depth() == 1;
                let fall = ctl.reachable();
                if function {
                    let closed = ctl.end().expect("the function frame is open");
                    if closed.fixups.is_empty() {
                        // Only the fall-through returns (or nothing does).
                        if fall {
                            if s.stack.len() != results.len() {
                                return Err(SelectError::Malformed(format!(
                                    "{} value(s) on the stack at the final `end`, {} result(s) declared",
                                    s.stack.len(),
                                    results.len()
                                )));
                            }
                            s.ret(results, op)?;
                        }
                    } else {
                        // Branches to the function body: one shared epilogue
                        // reading the result from home slot 0.
                        if fall {
                            s.fall_into(op, 0, result)?;
                        }
                        let here = s.out.len();
                        s.links.extend(closed.fixups.iter().map(|&p| (p, here)));
                        if let Some(ty) = result {
                            let mem = s.home_mem(0)?;
                            s.out.push(Inst::Load {
                                size: size_of(ty),
                                dst: Reg::Rax,
                                mem,
                            });
                        }
                        s.epilogue();
                    }
                    ended = true;
                } else {
                    if fall {
                        s.fall_into(op, entry, result)?;
                    }
                    let closed = ctl.end().expect("a frame is open");
                    let here = s.out.len();
                    s.links.extend(closed.fixups.iter().map(|&p| (p, here)));
                    s.truncate(entry);
                    // The join reads the label's value from its home slot.
                    if let (Some(ty), true) = (result, closed.join_live) {
                        s.stack.push(Val {
                            loc: Loc::Home(entry as u32),
                            ty,
                        });
                    }
                }
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
    resolve(&mut s.out, &s.links)?;
    Ok(Lowered {
        out: s.out,
        spills: s.spills,
        homes: s.homes,
    })
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
        // Lane X5: code after `return` is dead and skipped, not lowered and
        // not refused: the output is the same as without it.
        assert_eq!(
            select(
                &[LocalGet(1), Return, LocalGet(0), Drop, Drop, End],
                &[I32, I32],
                &[],
                &[I32]
            ),
            Ok(v)
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
        for op in [Call(0), F32Add, GlobalGet(0), MemorySize(0)] {
            let e = select(&[op.clone(), End], &[I32], &[], &[]).unwrap_err();
            assert_eq!(e, SelectError::Unsupported(op.clone()));
            assert!(e.to_string().contains(&format!("{op:?}")), "{e}");
        }
    }

    fn sig(results: &[Ty]) -> BlockSig {
        BlockSig {
            params: 0,
            results: results.to_vec(),
        }
    }

    /// Lane X5: a `br` that is the last thing in its block jumps to the very
    /// next instruction (rel 0), and the value it carries is in the label's
    /// home slot, inside this frame.
    #[test]
    fn a_branch_to_the_next_instruction_has_displacement_zero() {
        let v = select_function(
            &[Block, I32Const(7), Br(0), End, End],
            &[],
            &[],
            &[I32],
            &[sig(&[I32])],
        )
        .unwrap();
        check_contract(&v);
        let jmps: Vec<&Inst> = v.iter().filter(|i| matches!(i, Inst::Jmp { .. })).collect();
        assert_eq!(jmps, [&Inst::Jmp { rel: 0 }]);
        assert_eq!(
            att(&v),
            [
                "pushq %rbp",
                "movq %rsp, %rbp",
                "subq $0x10, %rsp",
                "movl $0x7, %esi",
                "movq %rsi, -0x8(%rbp)",
                "{disp32} jmp .+0x5",
                "movq -0x8(%rbp), %rsi",
                "movl %esi, %eax",
                "movq %rbp, %rsp",
                "popq %rbp",
                "retq",
            ]
        );
    }

    /// The value beneath a block is stored to its home slot when the block
    /// opens, and the frame counts that slot.
    #[test]
    fn a_value_beneath_a_frame_lives_in_its_home_slot() {
        let v = select_function(
            &[I32Const(1), Block, End, End],
            &[],
            &[I64],
            &[I32],
            &[sig(&[])],
        )
        .unwrap();
        check_contract(&v);
        assert!(att(&v).contains(&"movq %rsi, -0x10(%rbp)".to_string()));
    }

    #[test]
    fn control_flow_declines_name_their_cause() {
        let table = |n: usize| BrTable {
            targets: vec![0; n],
            default: 0,
        };
        for n in [0, 1, BR_TABLE_LIMIT] {
            select(&[Block, I32Const(0), table(n), End, End], &[], &[], &[]).unwrap();
        }
        let e = select(&[Block, I32Const(0), table(17), End, End], &[], &[], &[]).unwrap_err();
        assert_eq!(e, SelectError::BrTableTargets(17));
        assert!(e.to_string().contains("at most 16"), "{e}");
        let with = |b: BlockSig| select_function(&[Block, End, End], &[], &[], &[], &[b]);
        let e = with(BlockSig {
            params: 1,
            results: vec![],
        })
        .unwrap_err();
        assert!(e.to_string().contains("parameters"), "{e}");
        let e = with(sig(&[I32, I64])).unwrap_err();
        assert!(e.to_string().contains("more than one result"), "{e}");
        assert!(matches!(e, SelectError::BlockType { ord: 0, .. }));
    }

    /// A malformed control structure is an `Err`, never a panic.
    #[test]
    fn malformed_control_flow_is_an_error() {
        for ops in [
            vec![Else, End],
            vec![Block, Else, End, End],
            vec![Br(1), End],
            vec![Block, BrIf(2), End, End],
            vec![Block, End],
            vec![End, End],
        ] {
            assert!(
                matches!(
                    select(&ops, &[I32], &[], &[]),
                    Err(SelectError::Malformed(_) | SelectError::NoFinalEnd)
                ),
                "{ops:?}"
            );
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
