//! WASM → RV32 instruction selector.
//!
//! Covers the i32 surface (arithmetic, logic, shifts, comparisons, division
//! with trap-on-zero), loads/stores against linear memory, simple control
//! flow (block / loop / if / br / br_if), and local variable access.
//!
//! Out of scope (see `select_simple` doc comments for the full list):
//! - i64 (handled by `select_i64.rs` in a follow-up PR)
//! - F32/F64 (RV32F/D — not yet wired)
//! - br_table (lowered in B3 alongside jump tables)
//! - Cross-function calls (need linker-resolvable Call ops + relocations)
//! - Component Model lifting/lowering
//!
//! Memory model: the wasm linear-memory base lives in `s11` (x27) — chosen
//! because it's callee-saved across the AAPCS-style RV calling convention,
//! so leaf-style functions can rely on it without a re-load. The startup
//! code (B3) is responsible for setting s11 before main runs.

use crate::register::Reg;
use crate::riscv_op::{Branch, RiscVOp};
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

    #[error("control stack mismatch: {0}")]
    ControlMismatch(&'static str),

    #[error("br depth {depth} out of range (control stack height {height})")]
    BrOutOfRange { depth: u32, height: usize },
}

/// Output of the selector.
pub struct RiscVSelection {
    pub ops: Vec<RiscVOp>,
}

/// Linear-memory base register. The startup code is responsible for loading
/// the address of `__linear_memory_base` here. Callees may reuse it freely
/// because the RV psABI marks `s11` as callee-saved.
const LINEAR_MEM_BASE: Reg = Reg::S11;

/// Translate a flat sequence of WASM ops to RV32 ops.
///
/// This is the entry point used by `RiscVBackend::compile_function`. The
/// selector is structurally similar to a single pass through the wasm,
/// keeping a virtual register stack and a control-flow stack for blocks /
/// loops / if-else / br targets. Branches are emitted with symbolic labels
/// (`L0`, `L1`, …) and the ELF builder resolves them when laying out the
/// function.
///
/// Supported ops (∗ = covered by tests):
/// - i32: const ∗, add ∗, sub ∗, mul ∗, div_s ∗, div_u ∗, rem_s ∗, rem_u ∗,
///   and ∗, or ∗, xor ∗, shl ∗, shr_s ∗, shr_u ∗, eqz ∗, eq ∗, ne ∗,
///   lt_s ∗, lt_u ∗, le_s ∗, le_u ∗, gt_s ∗, gt_u ∗, ge_s ∗, ge_u ∗,
///   load ∗, store ∗, load8_s/u ∗, load16_s/u ∗, store8 ∗, store16 ∗
/// - locals: get, set, tee
/// - control: block, loop, if, else, end, br, br_if, return
/// - misc: drop, nop, unreachable
pub fn select(wasm_ops: &[WasmOp], num_params: u32) -> Result<RiscVSelection, SelectorError> {
    let mut ctx = Selector::new(num_params);
    ctx.lower_seq(wasm_ops)?;
    ctx.emit_return_epilogue();
    Ok(RiscVSelection { ops: ctx.out })
}

/// Backwards-compatible alias for the original simple selector. The new
/// `select` superset handles everything `select_simple` did and more —
/// kept here so `compile_function` doesn't have to change.
pub fn select_simple(
    wasm_ops: &[WasmOp],
    num_params: u32,
) -> Result<RiscVSelection, SelectorError> {
    select(wasm_ops, num_params)
}

/// Internal control-flow frame. Every wasm `block`/`loop`/`if` pushes one.
struct ControlFrame {
    /// What kind of frame it is — affects br semantics (loop targets the
    /// top of the loop, block/if target the end label).
    kind: FrameKind,
    /// Label emitted when the frame ends.
    end_label: String,
    /// For loops, the label at the top of the loop body — that's where br
    /// inside a loop frame jumps to.
    head_label: Option<String>,
    /// For if frames: the label at the start of the else block (None if
    /// no else has been emitted yet).
    else_label: Option<String>,
    /// Snapshot of the value-stack height when this frame was pushed.
    /// Used to drop excess values on br / end.
    stack_height_at_entry: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FrameKind {
    Block,
    Loop,
    If,
    /// We've seen the matching `else` and are emitting the else body.
    Else,
}

struct Selector {
    out: Vec<RiscVOp>,
    /// Virtual stack of registers holding wasm values.
    vstack: Vec<Reg>,
    /// Control-flow frames; index 0 is the outermost.
    ctrl: Vec<ControlFrame>,
    /// Argument registers for the current function's params (a0..a7).
    arg_regs: Vec<Reg>,
    /// Available temporary registers, recycled in round-robin order.
    temps: Vec<Reg>,
    next_temp: usize,
    /// Counter for generating unique labels (L0, L1, ...).
    next_label: u32,
    /// Tracks whether we already emitted the function-final return.
    emitted_return: bool,
}

impl Selector {
    fn new(num_params: u32) -> Self {
        // a0..a(min(7,num_params-1)) hold params, t0..t6 + s1..s10 are
        // available as temporaries. Note we deliberately do NOT use s0 (fp)
        // or s11 (linear-memory base) — they're reserved for the runtime.
        let temps = vec![
            Reg::T0,
            Reg::T1,
            Reg::T2,
            Reg::T3,
            Reg::T4,
            Reg::T5,
            Reg::T6,
            Reg::S1,
            Reg::S2,
            Reg::S3,
            Reg::S4,
            Reg::S5,
            Reg::S6,
        ];
        Self {
            out: Vec::new(),
            vstack: Vec::new(),
            ctrl: Vec::new(),
            arg_regs: Reg::arg_regs(num_params as usize),
            temps,
            next_temp: 0,
            next_label: 0,
            emitted_return: false,
        }
    }

    fn fresh_label(&mut self, prefix: &str) -> String {
        let n = self.next_label;
        self.next_label += 1;
        format!("{}{}", prefix, n)
    }

    fn alloc_temp(&mut self) -> Reg {
        let r = self.temps[self.next_temp % self.temps.len()];
        self.next_temp += 1;
        r
    }

    fn push_val(&mut self, r: Reg) {
        self.vstack.push(r);
    }

    fn pop_val(&mut self, op: &WasmOp) -> Result<Reg, SelectorError> {
        self.vstack
            .pop()
            .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))
    }

    fn pop_pair(&mut self, op: &WasmOp) -> Result<(Reg, Reg), SelectorError> {
        let rhs = self.pop_val(op)?;
        let lhs = self.pop_val(op)?;
        Ok((lhs, rhs))
    }

    fn lower_seq(&mut self, wasm_ops: &[WasmOp]) -> Result<(), SelectorError> {
        for op in wasm_ops {
            self.lower_one(op)?;
            if self.emitted_return {
                break;
            }
        }
        Ok(())
    }

    fn lower_one(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        use WasmOp::*;
        match op {
            // ─── Locals ─────────────────────────────────────────────────
            LocalGet(idx) => self.lower_local_get(*idx, op)?,
            LocalSet(idx) => self.lower_local_set(*idx, op)?,
            LocalTee(idx) => self.lower_local_tee(*idx, op)?,

            // ─── Constants ──────────────────────────────────────────────
            I32Const(v) => {
                let dst = self.alloc_temp();
                emit_load_imm(&mut self.out, dst, *v);
                self.push_val(dst);
            }

            // ─── Arithmetic ─────────────────────────────────────────────
            I32Add => self.bin(op, |rd, rs1, rs2| RiscVOp::Add { rd, rs1, rs2 })?,
            I32Sub => self.bin(op, |rd, rs1, rs2| RiscVOp::Sub { rd, rs1, rs2 })?,
            I32Mul => self.bin(op, |rd, rs1, rs2| RiscVOp::Mul { rd, rs1, rs2 })?,
            I32DivS => self.bin_with_zero_trap(op, |rd, rs1, rs2| RiscVOp::Div { rd, rs1, rs2 })?,
            I32DivU => {
                self.bin_with_zero_trap(op, |rd, rs1, rs2| RiscVOp::Divu { rd, rs1, rs2 })?
            }
            I32RemS => self.bin_with_zero_trap(op, |rd, rs1, rs2| RiscVOp::Rem { rd, rs1, rs2 })?,
            I32RemU => {
                self.bin_with_zero_trap(op, |rd, rs1, rs2| RiscVOp::Remu { rd, rs1, rs2 })?
            }

            // ─── Bitwise ────────────────────────────────────────────────
            I32And => self.bin(op, |rd, rs1, rs2| RiscVOp::And { rd, rs1, rs2 })?,
            I32Or => self.bin(op, |rd, rs1, rs2| RiscVOp::Or { rd, rs1, rs2 })?,
            I32Xor => self.bin(op, |rd, rs1, rs2| RiscVOp::Xor { rd, rs1, rs2 })?,

            // ─── Shifts ─────────────────────────────────────────────────
            I32Shl => self.bin(op, |rd, rs1, rs2| RiscVOp::Sll { rd, rs1, rs2 })?,
            I32ShrS => self.bin(op, |rd, rs1, rs2| RiscVOp::Sra { rd, rs1, rs2 })?,
            I32ShrU => self.bin(op, |rd, rs1, rs2| RiscVOp::Srl { rd, rs1, rs2 })?,

            // ─── Comparisons (return 0 or 1 in a register) ─────────────
            I32Eqz => self.lower_eqz(op)?,
            I32Eq => self.lower_cmp_eq(op, false)?,
            I32Ne => self.lower_cmp_eq(op, true)?,
            I32LtS => self.lower_cmp_signed_lt(op, false)?,
            I32GtS => self.lower_cmp_signed_lt(op, true)?, // a > b = b < a
            I32LeS => self.lower_cmp_signed_ge(op, true)?, // a <= b = !(a > b) = !(b < a)
            I32GeS => self.lower_cmp_signed_ge(op, false)?, // a >= b = !(a < b)
            I32LtU => self.lower_cmp_unsigned_lt(op, false)?,
            I32GtU => self.lower_cmp_unsigned_lt(op, true)?,
            I32LeU => self.lower_cmp_unsigned_ge(op, true)?,
            I32GeU => self.lower_cmp_unsigned_ge(op, false)?,

            // ─── Memory ─────────────────────────────────────────────────
            I32Load { offset, align: _ } => self.lower_load_word(op, *offset)?,
            I32Load8S { offset, align: _ } => {
                self.lower_load_subword(op, *offset, LoadKind::I8S)?
            }
            I32Load8U { offset, align: _ } => {
                self.lower_load_subword(op, *offset, LoadKind::I8U)?
            }
            I32Load16S { offset, align: _ } => {
                self.lower_load_subword(op, *offset, LoadKind::I16S)?
            }
            I32Load16U { offset, align: _ } => {
                self.lower_load_subword(op, *offset, LoadKind::I16U)?
            }
            I32Store { offset, align: _ } => self.lower_store(op, *offset, StoreKind::Word)?,
            I32Store8 { offset, align: _ } => self.lower_store(op, *offset, StoreKind::Byte)?,
            I32Store16 { offset, align: _ } => self.lower_store(op, *offset, StoreKind::Half)?,

            // ─── Stack manipulation ─────────────────────────────────────
            Drop => {
                self.pop_val(op)?;
            }
            Nop => {}
            Unreachable => {
                // RISC-V's recommended trap mnemonic is `unimp` (= csrrw x0, cycle, x0)
                // but `ebreak` is universally recognized as a trap and works in
                // bare-metal firmware. Use ebreak for now.
                self.out.push(RiscVOp::Ebreak);
            }

            // ─── Control flow ───────────────────────────────────────────
            Block => {
                let end = self.fresh_label("Lend");
                self.ctrl.push(ControlFrame {
                    kind: FrameKind::Block,
                    end_label: end,
                    head_label: None,
                    else_label: None,
                    stack_height_at_entry: self.vstack.len(),
                });
            }
            Loop => {
                let end = self.fresh_label("Lloop_end");
                let head = self.fresh_label("Lloop_head");
                self.out.push(RiscVOp::Label { name: head.clone() });
                self.ctrl.push(ControlFrame {
                    kind: FrameKind::Loop,
                    end_label: end,
                    head_label: Some(head),
                    else_label: None,
                    stack_height_at_entry: self.vstack.len(),
                });
            }
            If => self.lower_if(op)?,
            Else => self.lower_else(op)?,
            End => self.lower_end()?,
            Br(depth) => self.lower_br(*depth, op)?,
            BrIf(depth) => self.lower_br_if(*depth, op)?,

            Return => {
                self.emit_return_epilogue();
                self.emitted_return = true;
            }

            other => return Err(SelectorError::Unsupported(other.clone())),
        }
        Ok(())
    }

    // ────────── Locals ──────────

    fn lower_local_get(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        let dst = self.alloc_temp();
        if (idx as usize) < self.arg_regs.len() {
            // mv dst, arg
            self.out.push(RiscVOp::Addi {
                rd: dst,
                rs1: self.arg_regs[idx as usize],
                imm: 0,
            });
        } else {
            // Locals beyond params are stack-allocated. For the skeleton
            // we don't materialize the frame — emit a clear error instead.
            return Err(SelectorError::Unsupported(op.clone()));
        }
        self.push_val(dst);
        Ok(())
    }

    fn lower_local_set(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_val(op)?;
        if (idx as usize) < self.arg_regs.len() {
            // mv arg, src
            self.out.push(RiscVOp::Addi {
                rd: self.arg_regs[idx as usize],
                rs1: src,
                imm: 0,
            });
            Ok(())
        } else {
            Err(SelectorError::Unsupported(op.clone()))
        }
    }

    fn lower_local_tee(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        // tee = set + get; the value remains on the stack.
        let src = *self
            .vstack
            .last()
            .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
        if (idx as usize) < self.arg_regs.len() {
            self.out.push(RiscVOp::Addi {
                rd: self.arg_regs[idx as usize],
                rs1: src,
                imm: 0,
            });
            Ok(())
        } else {
            Err(SelectorError::Unsupported(op.clone()))
        }
    }

    // ────────── Binary helpers ──────────

    fn bin<F>(&mut self, op: &WasmOp, build: F) -> Result<(), SelectorError>
    where
        F: FnOnce(Reg, Reg, Reg) -> RiscVOp,
    {
        let (rs1, rs2) = self.pop_pair(op)?;
        let rd = self.alloc_temp();
        self.out.push(build(rd, rs1, rs2));
        self.push_val(rd);
        Ok(())
    }

    /// Like `bin`, but inserts `beqz rs2, Ltrap; ... ; ebreak; Ltrap_done:`
    /// to enforce wasm's "div/rem by zero traps" semantics.
    fn bin_with_zero_trap<F>(&mut self, op: &WasmOp, build: F) -> Result<(), SelectorError>
    where
        F: FnOnce(Reg, Reg, Reg) -> RiscVOp,
    {
        let (rs1, rs2) = self.pop_pair(op)?;
        let rd = self.alloc_temp();
        let ok_label = self.fresh_label("Ldiv_ok");
        // bne rs2, zero, Ldiv_ok  → skip trap when divisor != 0
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: rs2,
            rs2: Reg::ZERO,
            label: ok_label.clone(),
        });
        self.out.push(RiscVOp::Ebreak);
        self.out.push(RiscVOp::Label {
            name: ok_label.clone(),
        });
        self.out.push(build(rd, rs1, rs2));
        self.push_val(rd);
        Ok(())
    }

    // ────────── Comparisons ──────────

    fn lower_eqz(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_val(op)?;
        let dst = self.alloc_temp();
        // sltiu dst, src, 1  → 1 iff src == 0
        self.out.push(RiscVOp::Sltiu {
            rd: dst,
            rs1: src,
            imm: 1,
        });
        self.push_val(dst);
        Ok(())
    }

    fn lower_cmp_eq(&mut self, op: &WasmOp, invert: bool) -> Result<(), SelectorError> {
        let (lhs, rhs) = self.pop_pair(op)?;
        let diff = self.alloc_temp();
        // xor diff, lhs, rhs   → 0 iff equal
        self.out.push(RiscVOp::Xor {
            rd: diff,
            rs1: lhs,
            rs2: rhs,
        });
        let dst = self.alloc_temp();
        if invert {
            // ne: sltu dst, zero, diff → 1 iff diff != 0
            self.out.push(RiscVOp::Sltu {
                rd: dst,
                rs1: Reg::ZERO,
                rs2: diff,
            });
        } else {
            // eq: sltiu dst, diff, 1 → 1 iff diff == 0
            self.out.push(RiscVOp::Sltiu {
                rd: dst,
                rs1: diff,
                imm: 1,
            });
        }
        self.push_val(dst);
        Ok(())
    }

    fn lower_cmp_signed_lt(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair(op)?;
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Slt { rd: dst, rs1, rs2 });
        self.push_val(dst);
        Ok(())
    }

    fn lower_cmp_signed_ge(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        // a >= b  =  !(a < b) ; le maps via swap.
        let (a, b) = self.pop_pair(op)?;
        let lt = self.alloc_temp();
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Slt { rd: lt, rs1, rs2 });
        // dst = lt ^ 1  (flip 0/1)
        self.out.push(RiscVOp::Xori {
            rd: dst,
            rs1: lt,
            imm: 1,
        });
        self.push_val(dst);
        Ok(())
    }

    fn lower_cmp_unsigned_lt(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair(op)?;
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Sltu { rd: dst, rs1, rs2 });
        self.push_val(dst);
        Ok(())
    }

    fn lower_cmp_unsigned_ge(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair(op)?;
        let lt = self.alloc_temp();
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Sltu { rd: lt, rs1, rs2 });
        self.out.push(RiscVOp::Xori {
            rd: dst,
            rs1: lt,
            imm: 1,
        });
        self.push_val(dst);
        Ok(())
    }

    // ────────── Memory ──────────

    fn lower_load_word(&mut self, op: &WasmOp, offset: u32) -> Result<(), SelectorError> {
        let addr = self.pop_val(op)?;
        let dst = self.alloc_temp();
        // tmp = base + addr
        let tmp = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: tmp,
            rs1: LINEAR_MEM_BASE,
            rs2: addr,
        });
        // lw dst, offset(tmp)
        self.out.push(RiscVOp::Lw {
            rd: dst,
            rs1: tmp,
            imm: offset_to_imm(offset)?,
        });
        self.push_val(dst);
        Ok(())
    }

    fn lower_load_subword(
        &mut self,
        op: &WasmOp,
        offset: u32,
        kind: LoadKind,
    ) -> Result<(), SelectorError> {
        let addr = self.pop_val(op)?;
        let dst = self.alloc_temp();
        let tmp = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: tmp,
            rs1: LINEAR_MEM_BASE,
            rs2: addr,
        });
        let imm = offset_to_imm(offset)?;
        let op_built = match kind {
            LoadKind::I8S => RiscVOp::Lb {
                rd: dst,
                rs1: tmp,
                imm,
            },
            LoadKind::I8U => RiscVOp::Lbu {
                rd: dst,
                rs1: tmp,
                imm,
            },
            LoadKind::I16S => RiscVOp::Lh {
                rd: dst,
                rs1: tmp,
                imm,
            },
            LoadKind::I16U => RiscVOp::Lhu {
                rd: dst,
                rs1: tmp,
                imm,
            },
        };
        self.out.push(op_built);
        self.push_val(dst);
        Ok(())
    }

    fn lower_store(
        &mut self,
        op: &WasmOp,
        offset: u32,
        kind: StoreKind,
    ) -> Result<(), SelectorError> {
        let value = self.pop_val(op)?;
        let addr = self.pop_val(op)?;
        let tmp = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: tmp,
            rs1: LINEAR_MEM_BASE,
            rs2: addr,
        });
        let imm = offset_to_imm(offset)?;
        let op_built = match kind {
            StoreKind::Word => RiscVOp::Sw {
                rs1: tmp,
                rs2: value,
                imm,
            },
            StoreKind::Half => RiscVOp::Sh {
                rs1: tmp,
                rs2: value,
                imm,
            },
            StoreKind::Byte => RiscVOp::Sb {
                rs1: tmp,
                rs2: value,
                imm,
            },
        };
        self.out.push(op_built);
        Ok(())
    }

    // ────────── Control flow ──────────

    fn lower_if(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let cond = self.pop_val(op)?;
        let else_label = self.fresh_label("Lelse");
        let end_label = self.fresh_label("Lif_end");
        // beq cond, zero, Lelse  → skip the then-branch when cond is false
        self.out.push(RiscVOp::Branch {
            cond: Branch::Eq,
            rs1: cond,
            rs2: Reg::ZERO,
            label: else_label.clone(),
        });
        self.ctrl.push(ControlFrame {
            kind: FrameKind::If,
            end_label,
            head_label: None,
            else_label: Some(else_label),
            stack_height_at_entry: self.vstack.len(),
        });
        Ok(())
    }

    fn lower_else(&mut self, _op: &WasmOp) -> Result<(), SelectorError> {
        let frame = self
            .ctrl
            .last_mut()
            .ok_or(SelectorError::ControlMismatch("else without matching if"))?;
        if frame.kind != FrameKind::If {
            return Err(SelectorError::ControlMismatch(
                "else where the open frame is not an if",
            ));
        }
        let end = frame.end_label.clone();
        let else_label = frame
            .else_label
            .clone()
            .ok_or(SelectorError::ControlMismatch("if frame has no else label"))?;
        // jal zero, Lif_end  → end of then-branch jumps past the else
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: end,
        });
        // Lelse:
        self.out.push(RiscVOp::Label { name: else_label });
        // Reset the value-stack height to what it was at if-entry — wasm
        // discards then-branch values when entering the else-branch.
        self.vstack.truncate(frame.stack_height_at_entry);
        frame.kind = FrameKind::Else;
        Ok(())
    }

    fn lower_end(&mut self) -> Result<(), SelectorError> {
        if let Some(frame) = self.ctrl.pop() {
            // Emit the end-of-block label, plus (for an If with no Else) the
            // else label too — both targets land here when control falls
            // through.
            if frame.kind == FrameKind::If
                && let Some(else_label) = frame.else_label.clone()
            {
                // The if had no else: emit the else label here and let it
                // join the end label so beq lands here.
                self.out.push(RiscVOp::Label { name: else_label });
            }
            self.out.push(RiscVOp::Label {
                name: frame.end_label,
            });
        } else {
            // Function-level end → emit return epilogue.
            self.emit_return_epilogue();
            self.emitted_return = true;
        }
        Ok(())
    }

    fn lower_br(&mut self, depth: u32, _op: &WasmOp) -> Result<(), SelectorError> {
        let target_label = self.target_label_for_depth(depth)?;
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: target_label,
        });
        Ok(())
    }

    fn lower_br_if(&mut self, depth: u32, op: &WasmOp) -> Result<(), SelectorError> {
        let cond = self.pop_val(op)?;
        let target_label = self.target_label_for_depth(depth)?;
        // bne cond, zero, target — branch when condition is true (non-zero)
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: cond,
            rs2: Reg::ZERO,
            label: target_label,
        });
        Ok(())
    }

    fn target_label_for_depth(&self, depth: u32) -> Result<String, SelectorError> {
        let height = self.ctrl.len();
        let depth = depth as usize;
        if depth >= height {
            return Err(SelectorError::BrOutOfRange {
                depth: depth as u32,
                height,
            });
        }
        let frame = &self.ctrl[height - 1 - depth];
        // For loops, br targets the head; for blocks/ifs, br targets the end.
        let label = match frame.kind {
            FrameKind::Loop => frame
                .head_label
                .clone()
                .expect("loop frame must have a head label"),
            _ => frame.end_label.clone(),
        };
        Ok(label)
    }

    /// Emit `mv a0, top; ret` — the function epilogue.
    fn emit_return_epilogue(&mut self) {
        if let Some(&top) = self.vstack.last()
            && top != Reg::A0
        {
            self.out.push(RiscVOp::Addi {
                rd: Reg::A0,
                rs1: top,
                imm: 0,
            });
        }
        self.out.push(RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::RA,
            imm: 0,
        });
    }
}

#[derive(Debug, Clone, Copy)]
enum LoadKind {
    I8S,
    I8U,
    I16S,
    I16U,
}

#[derive(Debug, Clone, Copy)]
enum StoreKind {
    Word,
    Half,
    Byte,
}

fn offset_to_imm(offset: u32) -> Result<i32, SelectorError> {
    if offset > 2047 {
        // RV32 imm12 only supports ±2 KiB. Larger wasm offsets need an
        // extra `addi tmp, tmp, hi` step, which we'll add when a real wasm
        // module hits this. The skeleton fails loudly so we don't silently
        // truncate.
        return Err(SelectorError::ImmediateTooLarge {
            value: offset as i64,
            context: "memory offset",
        });
    }
    Ok(offset as i32)
}

/// Materialize a 32-bit immediate into `rd` using `lui + addi` when needed.
fn emit_load_imm(out: &mut Vec<RiscVOp>, rd: Reg, value: i32) {
    if (-2048..=2047).contains(&value) {
        out.push(RiscVOp::Addi {
            rd,
            rs1: Reg::ZERO,
            imm: value,
        });
        return;
    }
    let value_u = value as u32;
    let lo12 = (value_u & 0xFFF) as i32;
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

    fn s(ops: &[WasmOp], num_params: u32) -> Vec<RiscVOp> {
        select(ops, num_params).unwrap().ops
    }

    fn count<F: Fn(&RiscVOp) -> bool>(out: &[RiscVOp], f: F) -> usize {
        out.iter().filter(|o| f(o)).count()
    }

    #[test]
    fn add_two_params() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Add,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Add { .. })) == 1);
        assert!(matches!(
            out.last().unwrap(),
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                ..
            }
        ));
    }

    #[test]
    fn div_emits_zero_trap() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32DivS,
                WasmOp::End,
            ],
            2,
        );
        // bne ... zero, Ldiv_ok ; ebreak ; Ldiv_ok: ; div ...
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )) >= 1
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Ebreak)) >= 1);
        assert!(count(&out, |op| matches!(op, RiscVOp::Div { .. })) >= 1);
    }

    #[test]
    fn rem_unsigned_emits_remu() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32RemU,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Remu { .. })) == 1);
    }

    #[test]
    fn cmp_lt_signed_uses_slt() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32LtS,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Slt { .. })) == 1);
    }

    #[test]
    fn cmp_gt_uses_slt_with_swap() {
        // a > b is encoded as slt rd, b, a (swap). We can't tell that from
        // the count alone, but we can verify exactly one slt was emitted.
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32GtS,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Slt { .. })) == 1);
    }

    #[test]
    fn cmp_le_uses_slt_xor() {
        // le_s: lt(b, a) ^ 1 — produces one slt and one xori.
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32LeS,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Slt { .. })) == 1);
        assert!(count(&out, |op| matches!(op, RiscVOp::Xori { imm: 1, .. })) == 1);
    }

    #[test]
    fn eq_uses_xor_sltiu() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Eq,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Xor { .. })) == 1);
        assert!(count(&out, |op| matches!(op, RiscVOp::Sltiu { imm: 1, .. })) == 1);
    }

    #[test]
    fn ne_uses_xor_sltu() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Ne,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Xor { .. })) == 1);
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Sltu { rs1: Reg::ZERO, .. }
            )) == 1
        );
    }

    #[test]
    fn shifts_use_register_form() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Shl,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Sll { .. })) == 1);
    }

    #[test]
    fn shr_signed_uses_sra() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32ShrS,
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Sra { .. })) == 1);
    }

    #[test]
    fn load_word_uses_lw_via_base_plus_addr() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            1,
        );
        // add tmp, s11, addr ; lw dst, 0(tmp)
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Add {
                    rs1: LINEAR_MEM_BASE,
                    ..
                }
            )) == 1
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Lw { .. })) == 1);
    }

    #[test]
    fn store_word_uses_sw() {
        let out = s(
            &[
                WasmOp::LocalGet(0), // address
                WasmOp::LocalGet(1), // value
                WasmOp::I32Store {
                    offset: 16,
                    align: 2,
                },
                WasmOp::End,
            ],
            2,
        );
        let sw = out.iter().find(|op| matches!(op, RiscVOp::Sw { .. }));
        assert!(matches!(sw, Some(RiscVOp::Sw { imm: 16, .. })));
    }

    #[test]
    fn store_byte_uses_sb() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Store8 {
                    offset: 0,
                    align: 0,
                },
                WasmOp::End,
            ],
            2,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Sb { .. })) == 1);
    }

    #[test]
    fn load_signed_byte_uses_lb() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load8S {
                    offset: 4,
                    align: 0,
                },
                WasmOp::End,
            ],
            1,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Lb { imm: 4, .. })) == 1);
    }

    #[test]
    fn load_unsigned_halfword_uses_lhu() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load16U {
                    offset: 8,
                    align: 1,
                },
                WasmOp::End,
            ],
            1,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Lhu { imm: 8, .. })) == 1);
    }

    #[test]
    fn block_end_emits_label_only() {
        let out = s(&[WasmOp::Block, WasmOp::End, WasmOp::End], 0);
        // One Label for the block end + one for the function epilogue's
        // implicit end... actually the function-level End emits the
        // epilogue (no label). So exactly 1 Label.
        assert!(count(&out, |op| matches!(op, RiscVOp::Label { .. })) == 1);
    }

    #[test]
    fn loop_emits_head_label() {
        let out = s(&[WasmOp::Loop, WasmOp::End, WasmOp::End], 0);
        // Loop emits a head label up front and an end label at End.
        assert!(count(&out, |op| matches!(op, RiscVOp::Label { .. })) == 2);
    }

    #[test]
    fn br_in_loop_jumps_to_head() {
        let out = s(
            &[
                WasmOp::Loop,
                WasmOp::Br(0),
                WasmOp::End, // end of loop
                WasmOp::End, // function end
            ],
            0,
        );
        // Find the head label name (first Label emitted after Loop).
        let head_label = match out.iter().find(|op| matches!(op, RiscVOp::Label { .. })) {
            Some(RiscVOp::Label { name }) => name.clone(),
            _ => panic!("expected at least one label"),
        };
        // The Jal should target the head label, NOT the end label.
        let jal_target = out.iter().find_map(|op| match op {
            RiscVOp::Jal { label, .. } => Some(label.clone()),
            _ => None,
        });
        assert_eq!(jal_target, Some(head_label));
    }

    #[test]
    fn br_in_block_jumps_to_end() {
        let out = s(
            &[
                WasmOp::Block,
                WasmOp::Br(0),
                WasmOp::End, // end of block (this label is the br target)
                WasmOp::End,
            ],
            0,
        );
        // The Jal target should be the end label, which is the (only) Label op.
        let label_name = match out.iter().find(|op| matches!(op, RiscVOp::Label { .. })) {
            Some(RiscVOp::Label { name }) => name.clone(),
            _ => panic!("missing label"),
        };
        let jal_target = out.iter().find_map(|op| match op {
            RiscVOp::Jal { label, .. } => Some(label.clone()),
            _ => None,
        });
        assert_eq!(jal_target, Some(label_name));
    }

    #[test]
    fn if_without_else_uses_beq_to_end() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::If,
                WasmOp::End, // end of if (no else)
                WasmOp::End,
            ],
            1,
        );
        // We expect one beq to skip the then-branch when cond is zero.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Eq,
                    ..
                }
            )) == 1
        );
    }

    #[test]
    fn if_else_emits_jal_skip() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::If,
                WasmOp::Else,
                WasmOp::End,
                WasmOp::End,
            ],
            1,
        );
        // The then-branch needs to jump past the else.
        assert!(count(&out, |op| matches!(op, RiscVOp::Jal { .. })) >= 1);
    }

    #[test]
    fn br_if_uses_bne() {
        let out = s(
            &[
                WasmOp::Block,
                WasmOp::LocalGet(0),
                WasmOp::BrIf(0),
                WasmOp::End,
                WasmOp::End,
            ],
            1,
        );
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )) == 1
        );
    }

    #[test]
    fn br_out_of_range_errors() {
        let r = select(
            &[
                WasmOp::Br(5), // no enclosing frames at all
                WasmOp::End,
            ],
            0,
        );
        assert!(matches!(r, Err(SelectorError::BrOutOfRange { .. })));
    }

    #[test]
    fn drop_pops_stack() {
        let out = s(&[WasmOp::I32Const(42), WasmOp::Drop, WasmOp::End], 0);
        // No mv to a0 because the stack is empty after drop.
        let last = out.last().unwrap();
        assert!(matches!(
            last,
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                ..
            }
        ));
    }

    #[test]
    fn unreachable_emits_ebreak() {
        let out = s(&[WasmOp::Unreachable, WasmOp::End], 0);
        assert!(count(&out, |op| matches!(op, RiscVOp::Ebreak)) == 1);
    }

    #[test]
    fn local_tee_keeps_value_on_stack() {
        // tee(0); add — should produce one mv to the local + one add
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Const(1),
                WasmOp::LocalTee(0),
                WasmOp::I32Add,
                WasmOp::End,
            ],
            1,
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Add { .. })) == 1);
    }

    #[test]
    fn memory_offset_too_large_errors() {
        let r = select(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load {
                    offset: 4096, // > 2047
                    align: 2,
                },
                WasmOp::End,
            ],
            1,
        );
        assert!(matches!(r, Err(SelectorError::ImmediateTooLarge { .. })));
    }
}
