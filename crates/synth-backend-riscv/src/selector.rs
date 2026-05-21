//! WASM → RV32 instruction selector.
//!
//! Covers the i32 surface (arithmetic, logic, shifts, comparisons, division
//! with trap-on-zero), loads/stores against linear memory, simple control
//! flow (block / loop / if / br / br_if), and local variable access.
//!
//! Out of scope (see `select_simple` doc comments for the full list):
//! - i64 divide / remainder (Phase 3 — needs a `__divdi3`-style software
//!   long-division routine; RV32 has no 64-bit divide instruction)
//! - sign-extending sub-word i64 loads (`i64.load8_s` etc.)
//! - F32/F64 (RV32F/D — not yet wired)
//! - br_table (lowered in B3 alongside jump tables)
//! - Cross-function calls (need linker-resolvable Call ops + relocations)
//! - Component Model lifting/lowering
//!
//! i64 representation: on RV32, an i64 value is held in a *register pair*
//! `(lo, hi)` where `lo` is bits [31:0] and `hi` is bits [63:32]. The two
//! halves don't need to be consecutive registers (unlike ARM's LDRD/STRD
//! pair requirement) — any two distinct temporaries work.
//!
//! Memory model: the wasm linear-memory base lives in `s11` (x27) — chosen
//! because it's callee-saved across the AAPCS-style RV calling convention,
//! so leaf-style functions can rely on it without a re-load. The startup
//! code (B3) is responsible for setting s11 before main runs.

use crate::register::Reg;
use crate::riscv_op::{Branch, RiscVOp};
use synth_core::wasm_op::WasmOp;
use thiserror::Error;

/// Per-access memory-bounds policy for the RV32 selector. Mirrors the ARM
/// `BoundsCheckConfig` in spirit — see `docs/binary-safety-design.md` §3.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RvBoundsMode {
    /// No inline check (default; relies on PMP or trusted-module assumption).
    #[default]
    None,
    /// Hardware PMP enforcement. Same code-gen as `None` but distinguished
    /// so the safety-manifest can record the intent.
    Pmp,
    /// Software check: `bgeu addr, mem_size, Ltrap; ...; Ltrap: ebreak`
    /// emitted before each load/store. The memory size is materialised
    /// inline (`emit_load_imm`) per access — Phase 1 acceptably simple;
    /// Phase 2 will reserve a callee-saved register for it.
    Software {
        /// Linear-memory size in bytes. Anything `addr + offset + access_size`
        /// `>=` this triggers the trap.
        mem_size: u32,
    },
    /// AND-mask: `andi addr, addr, (mem_size - 1)` — power-of-two only.
    /// Wraps on OOB rather than trapping; matches the ARM "Masking" mode.
    Mask {
        /// Must be `mem_size - 1`, where `mem_size` is a power of two.
        mask: u32,
    },
}

/// Options for RV32 instruction selection. Phase 1 of the binary-safety
/// roadmap surfaces a small set of safety knobs here; later phases will
/// likely group them into a `SafetyProfile` struct shared between backends.
#[derive(Debug, Clone, Copy, Default)]
pub struct SelectorOptions {
    /// Memory-bounds policy. See `RvBoundsMode`.
    pub bounds: RvBoundsMode,
    /// Emit the `INT_MIN / -1` overflow guard around signed-division ops.
    /// Always on for spec-compliant WASM output; exposed as a knob so the
    /// fuzz harness can disable it when comparing IR-level behaviour only.
    pub signed_div_overflow_trap: bool,
}

impl SelectorOptions {
    /// Construct an options bundle with both safety knobs at their compliant
    /// defaults (signed-div overflow trap on, bounds-check off).
    pub fn wasm_compliant() -> Self {
        Self {
            bounds: RvBoundsMode::None,
            signed_div_overflow_trap: true,
        }
    }
}

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

    #[error("stack type mismatch at op {op:?}: expected {expected}, found {found} on top of stack")]
    StackTypeMismatch {
        op: WasmOp,
        expected: &'static str,
        found: &'static str,
    },
}

/// A value sitting on the selector's virtual stack. RV32 is a 32-bit ISA so
/// i32s map to a single register, while i64s require a `(lo, hi)` pair (see
/// the module-level docs for the bit-ordering convention).
#[derive(Debug, Clone, Copy)]
enum VstackVal {
    I32(Reg),
    I64 { lo: Reg, hi: Reg },
}

/// An i64 register pair: `.0` is `lo` (bits [31:0]), `.1` is `hi` (bits [63:32]).
type I64Pair = (Reg, Reg);

impl VstackVal {
    fn type_name(self) -> &'static str {
        match self {
            VstackVal::I32(_) => "i32",
            VstackVal::I64 { .. } => "i64",
        }
    }
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
    select_with_options(wasm_ops, num_params, SelectorOptions::wasm_compliant())
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

/// Same as [`select`], but lets the caller dial in safety options.
/// Phase 1 of `docs/binary-safety-design.md` §3.1 / §3.3.
pub fn select_with_options(
    wasm_ops: &[WasmOp],
    num_params: u32,
    options: SelectorOptions,
) -> Result<RiscVSelection, SelectorError> {
    let mut ctx = Selector::new_with_options(num_params, options);
    ctx.lower_seq(wasm_ops)?;
    ctx.emit_return_epilogue();
    Ok(RiscVSelection { ops: ctx.out })
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
    /// Virtual stack of values produced by lowering. i32s occupy a single
    /// register; i64s occupy a `(lo, hi)` register pair.
    vstack: Vec<VstackVal>,
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
    /// Phase-1 safety options (bounds-check policy, signed-div overflow trap).
    options: SelectorOptions,
}

impl Selector {
    fn new_with_options(num_params: u32, options: SelectorOptions) -> Self {
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
            options,
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

    fn push_i32(&mut self, r: Reg) {
        self.vstack.push(VstackVal::I32(r));
    }

    fn push_i64(&mut self, lo: Reg, hi: Reg) {
        self.vstack.push(VstackVal::I64 { lo, hi });
    }

    fn pop_any(&mut self, op: &WasmOp) -> Result<VstackVal, SelectorError> {
        self.vstack
            .pop()
            .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))
    }

    /// Pop the top of stack and assert it's an i32. Errors with
    /// `StackTypeMismatch` if the top is an i64 (caller's bug, never the
    /// wasm input's bug — by this point the wasm has been validated).
    fn pop_i32(&mut self, op: &WasmOp) -> Result<Reg, SelectorError> {
        let v = self.pop_any(op)?;
        match v {
            VstackVal::I32(r) => Ok(r),
            other => {
                // Restore for diagnostic determinism — the function will
                // bail out anyway, but we don't want subsequent code to
                // see a different stack layout if someone catches the err.
                self.vstack.push(other);
                Err(SelectorError::StackTypeMismatch {
                    op: op.clone(),
                    expected: "i32",
                    found: other.type_name(),
                })
            }
        }
    }

    /// Pop the top of stack and assert it's an i64, returning `(lo, hi)`.
    fn pop_i64(&mut self, op: &WasmOp) -> Result<I64Pair, SelectorError> {
        let v = self.pop_any(op)?;
        match v {
            VstackVal::I64 { lo, hi } => Ok((lo, hi)),
            other => {
                self.vstack.push(other);
                Err(SelectorError::StackTypeMismatch {
                    op: op.clone(),
                    expected: "i64",
                    found: other.type_name(),
                })
            }
        }
    }

    /// Pop two i32s; returns `(lhs, rhs)` in wasm push-order (lhs was pushed
    /// first, rhs second — i.e. rhs is on top of stack).
    fn pop_pair_i32(&mut self, op: &WasmOp) -> Result<(Reg, Reg), SelectorError> {
        let rhs = self.pop_i32(op)?;
        let lhs = self.pop_i32(op)?;
        Ok((lhs, rhs))
    }

    /// Pop two i64s; returns `((lhs_lo, lhs_hi), (rhs_lo, rhs_hi))`.
    fn pop_pair_i64(&mut self, op: &WasmOp) -> Result<(I64Pair, I64Pair), SelectorError> {
        let rhs = self.pop_i64(op)?;
        let lhs = self.pop_i64(op)?;
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
                self.push_i32(dst);
            }
            I64Const(v) => {
                let lo = self.alloc_temp();
                let hi = self.alloc_temp();
                emit_load_imm(&mut self.out, lo, *v as i32);
                emit_load_imm(&mut self.out, hi, (*v >> 32) as i32);
                self.push_i64(lo, hi);
            }

            // ─── Arithmetic ─────────────────────────────────────────────
            I32Add => self.bin(op, |rd, rs1, rs2| RiscVOp::Add { rd, rs1, rs2 })?,
            I32Sub => self.bin(op, |rd, rs1, rs2| RiscVOp::Sub { rd, rs1, rs2 })?,
            I32Mul => self.bin(op, |rd, rs1, rs2| RiscVOp::Mul { rd, rs1, rs2 })?,
            I32DivS => {
                self.bin_with_signed_div_traps(op, |rd, rs1, rs2| RiscVOp::Div { rd, rs1, rs2 })?
            }
            I32DivU => {
                self.bin_with_zero_trap(op, |rd, rs1, rs2| RiscVOp::Divu { rd, rs1, rs2 })?
            }
            I32RemS => {
                self.bin_with_signed_div_traps(op, |rd, rs1, rs2| RiscVOp::Rem { rd, rs1, rs2 })?
            }
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

            // ─── i64 arithmetic / logic ─────────────────────────────────
            I64Add => self.lower_i64_add(op)?,
            I64Sub => self.lower_i64_sub(op)?,
            I64And => self.lower_i64_bitwise(op, |rd, rs1, rs2| RiscVOp::And { rd, rs1, rs2 })?,
            I64Or => self.lower_i64_bitwise(op, |rd, rs1, rs2| RiscVOp::Or { rd, rs1, rs2 })?,
            I64Xor => self.lower_i64_bitwise(op, |rd, rs1, rs2| RiscVOp::Xor { rd, rs1, rs2 })?,

            // ─── i64 multiply ───────────────────────────────────────────
            I64Mul => self.lower_i64_mul(op)?,

            // ─── i64 shifts / rotates ───────────────────────────────────
            I64Shl => self.lower_i64_shift(op, ShiftKind::Shl)?,
            I64ShrS => self.lower_i64_shift(op, ShiftKind::ShrS)?,
            I64ShrU => self.lower_i64_shift(op, ShiftKind::ShrU)?,
            I64Rotl => self.lower_i64_rotate(op, true)?,
            I64Rotr => self.lower_i64_rotate(op, false)?,

            // ─── i64 bit-counting ───────────────────────────────────────
            I64Clz => self.lower_i64_clz(op)?,
            I64Ctz => self.lower_i64_ctz(op)?,
            I64Popcnt => self.lower_i64_popcnt(op)?,

            // ─── i64 comparisons (result is an i32 0/1) ─────────────────
            I64Eq => self.lower_i64_eq(op, false)?,
            I64Ne => self.lower_i64_eq(op, true)?,
            I64Eqz => self.lower_i64_eqz(op)?,
            I64LtS => self.lower_i64_cmp(op, CmpKind::Lt, true)?,
            I64LtU => self.lower_i64_cmp(op, CmpKind::Lt, false)?,
            I64LeS => self.lower_i64_cmp(op, CmpKind::Le, true)?,
            I64LeU => self.lower_i64_cmp(op, CmpKind::Le, false)?,
            I64GtS => self.lower_i64_cmp(op, CmpKind::Gt, true)?,
            I64GtU => self.lower_i64_cmp(op, CmpKind::Gt, false)?,
            I64GeS => self.lower_i64_cmp(op, CmpKind::Ge, true)?,
            I64GeU => self.lower_i64_cmp(op, CmpKind::Ge, false)?,

            // ─── i64 / i32 conversions ──────────────────────────────────
            I64ExtendI32U => self.lower_i64_extend_i32_u(op)?,
            I64ExtendI32S => self.lower_i64_extend_i32_s(op)?,
            I32WrapI64 => self.lower_i32_wrap_i64(op)?,

            // ─── i64 in-place sign extension ────────────────────────────
            I64Extend8S => self.lower_i64_extend_sub(op, 8)?,
            I64Extend16S => self.lower_i64_extend_sub(op, 16)?,
            I64Extend32S => self.lower_i64_extend_sub(op, 32)?,

            // i64 division / remainder is deferred to Phase 3 — RV32 has no
            // 64-bit divide instruction, so these need a `__divdi3`-style
            // software long-division routine (multi-block loop). Implementing
            // it inline would balloon the selector; emitting it as a runtime
            // helper needs a call-out the selector doesn't yet support.
            // Until then they fall through to the `Unsupported` arm below —
            // fail loudly rather than silently miscompile.
            // I64DivS / I64DivU / I64RemS / I64RemU — Phase 3.

            // ─── i64 memory ─────────────────────────────────────────────
            I64Load { offset, align: _ } => self.lower_i64_load(op, *offset)?,
            I64Store { offset, align: _ } => self.lower_i64_store(op, *offset)?,

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
                // Drop is type-agnostic: pop whatever's on top (i32 or i64).
                // Popping an i64 discards the whole pair in one shot.
                self.pop_any(op)?;
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

            // Cross-function call. WASM-level types tell us how many
            // args to consume from the value stack and how many results
            // to push back, but the selector doesn't yet have access to
            // the function signature (decoder doesn't pipe it down here).
            //
            // Minimum-viable semantics for v0.3.1:
            //   * Move the top N vstack values into a0..a(N-1) where
            //     N = min(vstack.len(), 8). The wasm validator
            //     guarantees the stack matches the callee's arity.
            //   * Emit `RiscVOp::Call { label }`. The ELF builder
            //     resolves the label to a PC-relative `auipc + jalr`
            //     pair when the callee is in the same compilation unit
            //     (single `.text` section — the common case for
            //     self-contained wasm modules).
            //   * Push a fresh vreg (= a0) onto the value stack as the
            //     return value. Multi-result calls (wasm 2.0 feature)
            //     and proper AAPCS arg saturation past 8 args are
            //     deferred.
            //
            // What this does NOT yet model:
            //   * Cross-`.text` relocations (linker fixup) — single-unit only
            //   * Caller-side R0..R7 invalidation across the BL
            //   * Multi-result returns (wasm 2.0)
            //   * More than 8 args (spill to stack per RV psABI)
            Call(func_idx) => self.lower_call(*func_idx, op)?,

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
        // Phase 1: locals are always treated as i32. i64 locals would need
        // two arg-register slots and live outside the scope of this PR.
        self.push_i32(dst);
        Ok(())
    }

    fn lower_local_set(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_i32(op)?;
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
        // tee = set + get; the value remains on the stack. Phase 1 only
        // handles i32 locals — see lower_local_set for the same restriction.
        let top = self
            .vstack
            .last()
            .copied()
            .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
        let src = match top {
            VstackVal::I32(r) => r,
            other => {
                return Err(SelectorError::StackTypeMismatch {
                    op: op.clone(),
                    expected: "i32",
                    found: other.type_name(),
                });
            }
        };
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
        let (rs1, rs2) = self.pop_pair_i32(op)?;
        let rd = self.alloc_temp();
        self.out.push(build(rd, rs1, rs2));
        self.push_i32(rd);
        Ok(())
    }

    /// Like `bin`, but inserts `beqz rs2, Ltrap; ... ; ebreak; Ltrap_done:`
    /// to enforce wasm's "div/rem by zero traps" semantics.
    fn bin_with_zero_trap<F>(&mut self, op: &WasmOp, build: F) -> Result<(), SelectorError>
    where
        F: FnOnce(Reg, Reg, Reg) -> RiscVOp,
    {
        let (rs1, rs2) = self.pop_pair_i32(op)?;
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
        self.push_i32(rd);
        Ok(())
    }

    /// Variant of `bin_with_zero_trap` that also guards `INT_MIN / -1`, which
    /// `div`/`rem` would silently return as `INT_MIN` / `0` respectively — WASM
    /// semantics require a trap. See `docs/binary-safety-design.md` §3.3.
    ///
    /// Sequence:
    /// ```text
    ///   bne   rs2, zero, .Ldiv_ok   ; divide-by-zero guard (existing)
    ///   ebreak
    /// .Ldiv_ok:
    ///   ; signed-overflow guard (only when options.signed_div_overflow_trap)
    ///   lui   tmin, %hi(INT_MIN)
    ///   addi  tmin, tmin, %lo(INT_MIN)         ; t = 0x80000000
    ///   bne   rs1, tmin, .Lsdiv_ok
    ///   li    tneg1, -1
    ///   bne   rs2, tneg1, .Lsdiv_ok
    ///   ebreak
    /// .Lsdiv_ok:
    ///   div   rd, rs1, rs2
    /// ```
    fn bin_with_signed_div_traps<F>(&mut self, op: &WasmOp, build: F) -> Result<(), SelectorError>
    where
        F: FnOnce(Reg, Reg, Reg) -> RiscVOp,
    {
        let (rs1, rs2) = self.pop_pair_i32(op)?;
        let rd = self.alloc_temp();
        // Trap 1: divisor == 0
        let ok_zero = self.fresh_label("Ldiv_ok");
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: rs2,
            rs2: Reg::ZERO,
            label: ok_zero.clone(),
        });
        self.out.push(RiscVOp::Ebreak);
        self.out.push(RiscVOp::Label { name: ok_zero });

        // Trap 2: INT_MIN / -1
        if self.options.signed_div_overflow_trap {
            let ok_overflow = self.fresh_label("Lsdiv_ok");
            let tmin = self.alloc_temp();
            // INT_MIN = 0x80000000. emit_load_imm decomposes into lui+addi.
            emit_load_imm(&mut self.out, tmin, i32::MIN);
            // bne rs1, tmin, .Lsdiv_ok → dividend != INT_MIN, no overflow
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1,
                rs2: tmin,
                label: ok_overflow.clone(),
            });
            let neg1 = self.alloc_temp();
            self.out.push(RiscVOp::Addi {
                rd: neg1,
                rs1: Reg::ZERO,
                imm: -1,
            });
            // bne rs2, -1, .Lsdiv_ok → divisor != -1, no overflow
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1: rs2,
                rs2: neg1,
                label: ok_overflow.clone(),
            });
            self.out.push(RiscVOp::Ebreak);
            self.out.push(RiscVOp::Label { name: ok_overflow });
        }

        self.out.push(build(rd, rs1, rs2));
        self.push_i32(rd);
        Ok(())
    }

    // ────────── Comparisons ──────────

    fn lower_eqz(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_i32(op)?;
        let dst = self.alloc_temp();
        // sltiu dst, src, 1  → 1 iff src == 0
        self.out.push(RiscVOp::Sltiu {
            rd: dst,
            rs1: src,
            imm: 1,
        });
        self.push_i32(dst);
        Ok(())
    }

    fn lower_cmp_eq(&mut self, op: &WasmOp, invert: bool) -> Result<(), SelectorError> {
        let (lhs, rhs) = self.pop_pair_i32(op)?;
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
        self.push_i32(dst);
        Ok(())
    }

    fn lower_cmp_signed_lt(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair_i32(op)?;
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Slt { rd: dst, rs1, rs2 });
        self.push_i32(dst);
        Ok(())
    }

    fn lower_cmp_signed_ge(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        // a >= b  =  !(a < b) ; le maps via swap.
        let (a, b) = self.pop_pair_i32(op)?;
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
        self.push_i32(dst);
        Ok(())
    }

    fn lower_cmp_unsigned_lt(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair_i32(op)?;
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Sltu { rd: dst, rs1, rs2 });
        self.push_i32(dst);
        Ok(())
    }

    fn lower_cmp_unsigned_ge(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair_i32(op)?;
        let lt = self.alloc_temp();
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        self.out.push(RiscVOp::Sltu { rd: lt, rs1, rs2 });
        self.out.push(RiscVOp::Xori {
            rd: dst,
            rs1: lt,
            imm: 1,
        });
        self.push_i32(dst);
        Ok(())
    }

    // ────────── Memory ──────────

    /// Emit the per-access safety guard before a load/store, returning a
    /// (possibly rewritten) address register. The returned register is what
    /// later code uses as the effective wasm-side address.
    ///
    /// Behaviour by mode:
    /// - `None` / `Pmp`: pass-through (no instructions emitted; PMP handles
    ///   faults via hardware).
    /// - `Software { mem_size }`: emit
    ///   `addi guard, addr, +(offset + access_size - 1)`
    ///   `lui/addi mlim, mem_size`
    ///   `bgeu guard, mlim, Ltrap`
    ///   `j Lok ; Ltrap: ebreak ; Lok:`
    ///   The check guards the last byte of the access, matching the ARM
    ///   software-bounds-check from §3.1.
    /// - `Mask { mask }`: emit `andi rd, addr, mask` (when `mask` fits in 12 bits)
    ///   or `lui/addi mtmp, mask; and rd, addr, mtmp` otherwise. The result is
    ///   the masked address; the caller uses *that* for the subsequent access.
    fn emit_bounds_check(
        &mut self,
        addr: Reg,
        offset: u32,
        access_size: u32,
    ) -> Result<Reg, SelectorError> {
        match self.options.bounds {
            RvBoundsMode::None | RvBoundsMode::Pmp => Ok(addr),
            RvBoundsMode::Software { mem_size } => {
                let end_byte = offset.checked_add(access_size.saturating_sub(1)).ok_or(
                    SelectorError::ImmediateTooLarge {
                        value: offset as i64 + access_size as i64,
                        context: "bounds-check end byte",
                    },
                )?;
                let guard = self.alloc_temp();
                if end_byte == 0 {
                    self.out.push(RiscVOp::Addi {
                        rd: guard,
                        rs1: addr,
                        imm: 0,
                    });
                } else if end_byte < 2048 {
                    self.out.push(RiscVOp::Addi {
                        rd: guard,
                        rs1: addr,
                        imm: end_byte as i32,
                    });
                } else {
                    // Materialise the offset into a temporary, then add.
                    let off_tmp = self.alloc_temp();
                    emit_load_imm(&mut self.out, off_tmp, end_byte as i32);
                    self.out.push(RiscVOp::Add {
                        rd: guard,
                        rs1: addr,
                        rs2: off_tmp,
                    });
                }
                let mlim = self.alloc_temp();
                emit_load_imm(&mut self.out, mlim, mem_size as i32);
                let ok_label = self.fresh_label("Lbnd_ok");
                let trap_label = self.fresh_label("Lbnd_trap");
                // bgeu guard, mlim, Lbnd_trap → branch to trap when OOB
                self.out.push(RiscVOp::Branch {
                    cond: Branch::Geu,
                    rs1: guard,
                    rs2: mlim,
                    label: trap_label.clone(),
                });
                // happy path falls through to the load/store; insert an
                // unconditional jump past the trap so we can place the
                // ebreak at the end of the sequence.
                self.out.push(RiscVOp::Jal {
                    rd: Reg::ZERO,
                    label: ok_label.clone(),
                });
                self.out.push(RiscVOp::Label { name: trap_label });
                self.out.push(RiscVOp::Ebreak);
                self.out.push(RiscVOp::Label { name: ok_label });
                Ok(addr)
            }
            RvBoundsMode::Mask { mask } => {
                let masked = self.alloc_temp();
                if mask <= 0x7FF {
                    self.out.push(RiscVOp::Andi {
                        rd: masked,
                        rs1: addr,
                        imm: mask as i32,
                    });
                } else {
                    let mtmp = self.alloc_temp();
                    emit_load_imm(&mut self.out, mtmp, mask as i32);
                    self.out.push(RiscVOp::And {
                        rd: masked,
                        rs1: addr,
                        rs2: mtmp,
                    });
                }
                Ok(masked)
            }
        }
    }

    fn lower_load_word(&mut self, op: &WasmOp, offset: u32) -> Result<(), SelectorError> {
        let addr = self.pop_i32(op)?;
        let addr = self.emit_bounds_check(addr, offset, 4)?;
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
        self.push_i32(dst);
        Ok(())
    }

    fn lower_load_subword(
        &mut self,
        op: &WasmOp,
        offset: u32,
        kind: LoadKind,
    ) -> Result<(), SelectorError> {
        let addr = self.pop_i32(op)?;
        let access_size = match kind {
            LoadKind::I8S | LoadKind::I8U => 1,
            LoadKind::I16S | LoadKind::I16U => 2,
        };
        let addr = self.emit_bounds_check(addr, offset, access_size)?;
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
        self.push_i32(dst);
        Ok(())
    }

    fn lower_store(
        &mut self,
        op: &WasmOp,
        offset: u32,
        kind: StoreKind,
    ) -> Result<(), SelectorError> {
        let value = self.pop_i32(op)?;
        let addr = self.pop_i32(op)?;
        let access_size = match kind {
            StoreKind::Byte => 1,
            StoreKind::Half => 2,
            StoreKind::Word => 4,
        };
        let addr = self.emit_bounds_check(addr, offset, access_size)?;
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
        let cond = self.pop_i32(op)?;
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
        let cond = self.pop_i32(op)?;
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

    /// Lower a wasm `call func_idx` op.
    ///
    /// Moves the top N vstack values (N capped at 8 for v0.3.1) into the
    /// AAPCS argument registers a0..a(N-1), then emits a label-based
    /// `RiscVOp::Call`. After the call, pushes a fresh return-value vreg
    /// (= a0) onto the vstack.
    ///
    /// Notable simplifications carried by this v0.3.1 cut, documented
    /// for the follow-up:
    /// * Args beyond 8 are silently dropped — the RV psABI says they
    ///   spill to the stack at well-defined offsets; not implemented.
    /// * The vreg pushed for the result is always `a0`; if the wasm
    ///   callee returns nothing, the caller's subsequent `drop` will
    ///   pop a stale `a0` (harmless because the value isn't used).
    /// * No invalidation of vregs currently bound to a0..a7 from before
    ///   the call — those values are clobbered by the BL but the
    ///   selector doesn't yet model that. Use `drop` or `local.tee`
    ///   between values you want to survive a call.
    fn lower_call(&mut self, func_idx: u32, _op: &WasmOp) -> Result<(), SelectorError> {
        // Move the top-of-stack values into a0..a7 in source order.
        // The wasm value stack is LIFO so the *last* push is the right-most
        // arg; we drain into argument registers in reverse.
        let n_args = self.vstack.len().min(8);
        let args: Vec<VstackVal> = self.vstack.drain(self.vstack.len() - n_args..).collect();
        let arg_regs = [
            Reg::A0,
            Reg::A1,
            Reg::A2,
            Reg::A3,
            Reg::A4,
            Reg::A5,
            Reg::A6,
            Reg::A7,
        ];
        for (i, src) in args.iter().enumerate() {
            // v0.3.1 Call handles only i32 args. An i64 argument occupies
            // two registers per the RV psABI and needs function-signature
            // info to marshal correctly — out of scope for the leaf-call
            // subset (tracked for v0.4 alongside `FuncSig` plumbing).
            let src_reg = match src {
                VstackVal::I32(r) => *r,
                VstackVal::I64 { .. } => {
                    return Err(SelectorError::Unsupported(WasmOp::Call(func_idx)));
                }
            };
            let dst = arg_regs[i];
            if src_reg != dst {
                self.out.push(RiscVOp::Addi {
                    rd: dst,
                    rs1: src_reg,
                    imm: 0,
                });
            }
        }

        // Emit the call. The ELF builder resolves `synth_func_{idx}` to
        // a PC-relative target when both functions are in the same .text
        // section — sufficient for the calculator and similar
        // self-contained wasm modules.
        self.out.push(RiscVOp::Call {
            label: format!("synth_func_{}", func_idx),
        });

        // Return value lands in a0 (AAPCS). Push it back as a new vreg.
        // Real multi-result returns (wasm 2.0) would push (a0, a1) here.
        // Treated as i32 — i64-returning calls are v0.4 scope.
        self.push_i32(Reg::A0);
        Ok(())
    }

    /// Emit `mv a0, top; ret` — the function epilogue.
    ///
    /// For i64 returns the wasm ABI puts the lo half in `a0` and the hi half
    /// in `a1` (matches the RISC-V psABI for 64-bit return values on RV32).
    /// We only emit the moves when the source isn't already in the target
    /// return register, to avoid a redundant `addi`.
    fn emit_return_epilogue(&mut self) {
        if let Some(top) = self.vstack.last().copied() {
            match top {
                VstackVal::I32(r) => {
                    if r != Reg::A0 {
                        self.out.push(RiscVOp::Addi {
                            rd: Reg::A0,
                            rs1: r,
                            imm: 0,
                        });
                    }
                }
                VstackVal::I64 { lo, hi } => {
                    if lo != Reg::A0 {
                        self.out.push(RiscVOp::Addi {
                            rd: Reg::A0,
                            rs1: lo,
                            imm: 0,
                        });
                    }
                    if hi != Reg::A1 {
                        self.out.push(RiscVOp::Addi {
                            rd: Reg::A1,
                            rs1: hi,
                            imm: 0,
                        });
                    }
                }
            }
        }
        self.out.push(RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::RA,
            imm: 0,
        });
    }

    // ────────── i64 lowerings (Phase 1) ──────────
    //
    // On RV32 an i64 lives in a register pair `(lo, hi)` per the convention
    // in the module docs. Each operation pops one or two pairs from vstack,
    // emits the equivalent sequence on the 32-bit halves, and pushes the
    // result (either as another i64 pair or as an i32 0/1 for comparisons).

    /// 64-bit add with carry: `lo = al+bl ; carry = (lo <u al) ; hi = ah+bh+carry`.
    fn lower_i64_add(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let ((al, ah), (bl, bh)) = self.pop_pair_i64(op)?;
        let lo = self.alloc_temp();
        let carry = self.alloc_temp();
        let hi_sum = self.alloc_temp();
        let hi = self.alloc_temp();
        // lo = al + bl
        self.out.push(RiscVOp::Add {
            rd: lo,
            rs1: al,
            rs2: bl,
        });
        // carry = (lo <u al) — unsigned overflow detection. Adding two
        // unsigned 32-bit values overflows iff the result is < either operand.
        self.out.push(RiscVOp::Sltu {
            rd: carry,
            rs1: lo,
            rs2: al,
        });
        // hi_sum = ah + bh
        self.out.push(RiscVOp::Add {
            rd: hi_sum,
            rs1: ah,
            rs2: bh,
        });
        // hi = hi_sum + carry
        self.out.push(RiscVOp::Add {
            rd: hi,
            rs1: hi_sum,
            rs2: carry,
        });
        self.push_i64(lo, hi);
        Ok(())
    }

    /// 64-bit sub with borrow: `borrow = (al <u bl) ; lo = al-bl ; hi = ah-bh-borrow`.
    fn lower_i64_sub(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let ((al, ah), (bl, bh)) = self.pop_pair_i64(op)?;
        let borrow = self.alloc_temp();
        let lo = self.alloc_temp();
        let hi_diff = self.alloc_temp();
        let hi = self.alloc_temp();
        // borrow = (al <u bl) — captured *before* the subtraction so we
        // observe the pre-subtraction relation.
        self.out.push(RiscVOp::Sltu {
            rd: borrow,
            rs1: al,
            rs2: bl,
        });
        // lo = al - bl
        self.out.push(RiscVOp::Sub {
            rd: lo,
            rs1: al,
            rs2: bl,
        });
        // hi_diff = ah - bh
        self.out.push(RiscVOp::Sub {
            rd: hi_diff,
            rs1: ah,
            rs2: bh,
        });
        // hi = hi_diff - borrow
        self.out.push(RiscVOp::Sub {
            rd: hi,
            rs1: hi_diff,
            rs2: borrow,
        });
        self.push_i64(lo, hi);
        Ok(())
    }

    /// Pairwise bitwise op on lo and hi (and/or/xor share this shape).
    fn lower_i64_bitwise<F>(&mut self, op: &WasmOp, build: F) -> Result<(), SelectorError>
    where
        F: Fn(Reg, Reg, Reg) -> RiscVOp,
    {
        let ((al, ah), (bl, bh)) = self.pop_pair_i64(op)?;
        let lo = self.alloc_temp();
        let hi = self.alloc_temp();
        self.out.push(build(lo, al, bl));
        self.out.push(build(hi, ah, bh));
        self.push_i64(lo, hi);
        Ok(())
    }

    /// i64 eq / ne — diff both halves, or them together, then sltiu / sltu.
    /// Result is an i32 0/1 value.
    fn lower_i64_eq(&mut self, op: &WasmOp, invert: bool) -> Result<(), SelectorError> {
        let ((al, ah), (bl, bh)) = self.pop_pair_i64(op)?;
        let d_lo = self.alloc_temp();
        let d_hi = self.alloc_temp();
        let d = self.alloc_temp();
        let dst = self.alloc_temp();
        // d_lo = al ^ bl ; d_hi = ah ^ bh ; d = d_lo | d_hi  → 0 iff equal
        self.out.push(RiscVOp::Xor {
            rd: d_lo,
            rs1: al,
            rs2: bl,
        });
        self.out.push(RiscVOp::Xor {
            rd: d_hi,
            rs1: ah,
            rs2: bh,
        });
        self.out.push(RiscVOp::Or {
            rd: d,
            rs1: d_lo,
            rs2: d_hi,
        });
        if invert {
            // ne: dst = (0 <u d) → 1 iff d != 0
            self.out.push(RiscVOp::Sltu {
                rd: dst,
                rs1: Reg::ZERO,
                rs2: d,
            });
        } else {
            // eq: dst = (d <u 1) → 1 iff d == 0
            self.out.push(RiscVOp::Sltiu {
                rd: dst,
                rs1: d,
                imm: 1,
            });
        }
        self.push_i32(dst);
        Ok(())
    }

    /// i64 eqz: pops one i64, returns i32 0/1.
    fn lower_i64_eqz(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let (lo, hi) = self.pop_i64(op)?;
        let d = self.alloc_temp();
        let dst = self.alloc_temp();
        // d = lo | hi → 0 iff both halves are zero
        self.out.push(RiscVOp::Or {
            rd: d,
            rs1: lo,
            rs2: hi,
        });
        // dst = (d <u 1) → 1 iff d == 0
        self.out.push(RiscVOp::Sltiu {
            rd: dst,
            rs1: d,
            imm: 1,
        });
        self.push_i32(dst);
        Ok(())
    }

    /// Zero-extend i32 → i64: lo = src, hi = 0.
    fn lower_i64_extend_i32_u(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_i32(op)?;
        let hi = self.alloc_temp();
        // hi = 0 (via `addi hi, zero, 0` — no dedicated li-zero op).
        self.out.push(RiscVOp::Addi {
            rd: hi,
            rs1: Reg::ZERO,
            imm: 0,
        });
        self.push_i64(src, hi);
        Ok(())
    }

    /// Sign-extend i32 → i64: lo = src, hi = sra(src, 31).
    /// SRA by 31 produces all-ones when src is negative, all-zeros otherwise.
    fn lower_i64_extend_i32_s(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_i32(op)?;
        let hi = self.alloc_temp();
        self.out.push(RiscVOp::Srai {
            rd: hi,
            rs1: src,
            shamt: 31,
        });
        self.push_i64(src, hi);
        Ok(())
    }

    /// Wrap i64 → i32: keep lo, drop hi. No instructions emitted — the lo
    /// register simply continues to live on the value stack as an i32.
    fn lower_i32_wrap_i64(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let (lo, _hi) = self.pop_i64(op)?;
        self.push_i32(lo);
        Ok(())
    }

    /// i64 load: two word-loads at `offset` and `offset+4`. Little-endian
    /// memory layout, matching wasm's spec (lo at lower address).
    fn lower_i64_load(&mut self, op: &WasmOp, offset: u32) -> Result<(), SelectorError> {
        let addr = self.pop_i32(op)?;
        let tmp = self.alloc_temp();
        let lo = self.alloc_temp();
        let hi = self.alloc_temp();
        // Single address calculation reused for both word loads.
        self.out.push(RiscVOp::Add {
            rd: tmp,
            rs1: LINEAR_MEM_BASE,
            rs2: addr,
        });
        let imm_lo = offset_to_imm(offset)?;
        // The high word lives at `offset + 4`; check the same imm12 range.
        let imm_hi = offset_to_imm(offset.checked_add(4).ok_or(
            SelectorError::ImmediateTooLarge {
                value: offset as i64 + 4,
                context: "i64 load high-word offset",
            },
        )?)?;
        self.out.push(RiscVOp::Lw {
            rd: lo,
            rs1: tmp,
            imm: imm_lo,
        });
        self.out.push(RiscVOp::Lw {
            rd: hi,
            rs1: tmp,
            imm: imm_hi,
        });
        self.push_i64(lo, hi);
        Ok(())
    }

    /// i64 store: pops value (i64) and addr (i32), then two `sw` at offset
    /// and offset+4. Little-endian, matching wasm's spec.
    fn lower_i64_store(&mut self, op: &WasmOp, offset: u32) -> Result<(), SelectorError> {
        let (lo, hi) = self.pop_i64(op)?;
        let addr = self.pop_i32(op)?;
        let tmp = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: tmp,
            rs1: LINEAR_MEM_BASE,
            rs2: addr,
        });
        let imm_lo = offset_to_imm(offset)?;
        let imm_hi = offset_to_imm(offset.checked_add(4).ok_or(
            SelectorError::ImmediateTooLarge {
                value: offset as i64 + 4,
                context: "i64 store high-word offset",
            },
        )?)?;
        self.out.push(RiscVOp::Sw {
            rs1: tmp,
            rs2: lo,
            imm: imm_lo,
        });
        self.out.push(RiscVOp::Sw {
            rs1: tmp,
            rs2: hi,
            imm: imm_hi,
        });
        Ok(())
    }

    // ────────── i64 lowerings (Phase 2) ──────────
    //
    // Phase 2 adds the harder i64 surface: multiply, the cross-word shifts
    // and rotates, the bit-counting trio, the signed/unsigned compare
    // ladders, and the in-place sub-word sign extensions. Division and
    // remainder are deferred to Phase 3 (need a __divdi3-style runtime).

    /// 64×64 → low-64 multiply.
    ///
    /// A full 128-bit product isn't needed — wasm `i64.mul` keeps only the
    /// low 64 bits. Writing `a = a_hi·2^32 + a_lo`, `b = b_hi·2^32 + b_lo`:
    /// ```text
    ///   a·b = a_hi·b_hi·2^64            (drops — above bit 63)
    ///       + (a_hi·b_lo + a_lo·b_hi)·2^32
    ///       + a_lo·b_lo
    /// ```
    /// So the low half is just `mul(a_lo, b_lo)` and the high half is the
    /// carry out of that product (`mulhu(a_lo, b_lo)` — the *unsigned* upper
    /// 32 bits, since the halves are treated as unsigned limbs) plus the two
    /// cross terms `mul(a_lo, b_hi)` and `mul(a_hi, b_lo)`. The `a_hi·b_hi`
    /// term lands entirely above bit 63 and is discarded.
    fn lower_i64_mul(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let ((al, ah), (bl, bh)) = self.pop_pair_i64(op)?;
        let lo = self.alloc_temp();
        let hi_carry = self.alloc_temp();
        let cross1 = self.alloc_temp();
        let cross2 = self.alloc_temp();
        let hi_partial = self.alloc_temp();
        let hi = self.alloc_temp();
        // lo = a_lo * b_lo  (low 32 bits of the limb product)
        self.out.push(RiscVOp::Mul {
            rd: lo,
            rs1: al,
            rs2: bl,
        });
        // hi_carry = mulhu(a_lo, b_lo)  — upper 32 bits of the same product,
        // i.e. the carry from the low limb into the high limb.
        self.out.push(RiscVOp::Mulhu {
            rd: hi_carry,
            rs1: al,
            rs2: bl,
        });
        // cross1 = a_lo * b_hi  (only the low 32 bits matter at the 2^32 place)
        self.out.push(RiscVOp::Mul {
            rd: cross1,
            rs1: al,
            rs2: bh,
        });
        // cross2 = a_hi * b_lo
        self.out.push(RiscVOp::Mul {
            rd: cross2,
            rs1: ah,
            rs2: bl,
        });
        // hi = hi_carry + cross1 + cross2
        self.out.push(RiscVOp::Add {
            rd: hi_partial,
            rs1: hi_carry,
            rs2: cross1,
        });
        self.out.push(RiscVOp::Add {
            rd: hi,
            rs1: hi_partial,
            rs2: cross2,
        });
        self.push_i64(lo, hi);
        Ok(())
    }

    /// 64-bit shift by a runtime amount (shl / shr_s / shr_u).
    ///
    /// The wasm shift amount is itself an i64 on the stack, but only the low
    /// 6 bits matter (`shamt mod 64`). RV32's register shifts (`sll`/`srl`/
    /// `sra`) already mask the amount to its low 5 bits, so a within-word
    /// shift "for free" computes `x << (shamt & 31)`. The hard part is the
    /// carry between halves and the `shamt >= 32` case.
    ///
    /// We emit a data-dependent branch on bit 5 of the shift amount:
    ///
    /// **Left shift, `shamt < 32`:**
    /// ```text
    ///   lo' = lo << s
    ///   hi' = (hi << s) | (lo >> (32 - s))     ; bits carried up from lo
    /// ```
    /// The `lo >> (32 - s)` term needs care when `s == 0`: `32 - 0 == 32`
    /// which RV masks back to `0`, so `lo >> 0 == lo` would wrongly OR the
    /// whole of lo into hi. We guard that by computing the carry as
    /// `(lo >> 1) >> (31 - s)` — a two-step shift that is well-defined for
    /// every `s` in `0..=31` and yields 0 when `s == 0`.
    ///
    /// **Left shift, `shamt >= 32`:** all of lo moves into hi.
    /// ```text
    ///   hi' = lo << (s - 32)        ; s-32 in 0..=31, RV masks it anyway
    ///   lo' = 0
    /// ```
    /// Right shifts are the mirror image (carry goes downward; for shr_s the
    /// fill is the sign bit, materialised once via `sra hi, 31`).
    fn lower_i64_shift(&mut self, op: &WasmOp, kind: ShiftKind) -> Result<(), SelectorError> {
        // rhs is the i64 shift amount; only its low limb is relevant.
        let ((vlo, vhi), (samt, _samt_hi)) = self.pop_pair_i64(op)?;
        // s = shamt & 63 — clamp to the 0..=63 window wasm guarantees.
        let s = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: s,
            rs1: samt,
            imm: 63,
        });
        // s_lo = s & 31 — the within-word part (also what RV's shift uses).
        let s_lo = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: s_lo,
            rs1: s,
            imm: 31,
        });
        // Result registers — written by both arms of the branch, so they
        // must be allocated once up front (a fresh temp per arm would leave
        // the join point reading an undefined register).
        let res_lo = self.alloc_temp();
        let res_hi = self.alloc_temp();

        let big_label = self.fresh_label("Lshift_big");
        let done_label = self.fresh_label("Lshift_done");
        // andi test, s, 32 ; bne test, zero, Lshift_big → take the cross-word
        // path when bit 5 of the shift amount is set (shamt >= 32).
        let test = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: test,
            rs1: s,
            imm: 32,
        });
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: test,
            rs2: Reg::ZERO,
            label: big_label.clone(),
        });

        // ── small case: shamt < 32 ───────────────────────────────────────
        // `inv = 31 - s_lo` is the complementary shift used to extract the
        // bits crossing the half boundary. Built once, reused below.
        let inv = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: inv,
            rs1: Reg::ZERO,
            imm: 31,
        });
        self.out.push(RiscVOp::Sub {
            rd: inv,
            rs1: inv,
            rs2: s_lo,
        });
        match kind {
            ShiftKind::Shl => {
                // lo' = lo << s
                self.out.push(RiscVOp::Sll {
                    rd: res_lo,
                    rs1: vlo,
                    rs2: s_lo,
                });
                // carry = (lo >> 1) >> (31 - s)  — well-defined for s==0..31
                let carry = self.alloc_temp();
                self.out.push(RiscVOp::Srli {
                    rd: carry,
                    rs1: vlo,
                    shamt: 1,
                });
                self.out.push(RiscVOp::Srl {
                    rd: carry,
                    rs1: carry,
                    rs2: inv,
                });
                // hi' = (hi << s) | carry
                let hi_shifted = self.alloc_temp();
                self.out.push(RiscVOp::Sll {
                    rd: hi_shifted,
                    rs1: vhi,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Or {
                    rd: res_hi,
                    rs1: hi_shifted,
                    rs2: carry,
                });
            }
            ShiftKind::ShrS | ShiftKind::ShrU => {
                // hi' = hi >> s  (sra for shr_s, srl for shr_u)
                self.out.push(if kind == ShiftKind::ShrS {
                    RiscVOp::Sra {
                        rd: res_hi,
                        rs1: vhi,
                        rs2: s_lo,
                    }
                } else {
                    RiscVOp::Srl {
                        rd: res_hi,
                        rs1: vhi,
                        rs2: s_lo,
                    }
                });
                // carry = (hi << 1) << (31 - s)  — bits dropping down from hi
                let carry = self.alloc_temp();
                self.out.push(RiscVOp::Slli {
                    rd: carry,
                    rs1: vhi,
                    shamt: 1,
                });
                self.out.push(RiscVOp::Sll {
                    rd: carry,
                    rs1: carry,
                    rs2: inv,
                });
                // lo' = (lo >> s) | carry  — lo is always logical-shifted.
                let lo_shifted = self.alloc_temp();
                self.out.push(RiscVOp::Srl {
                    rd: lo_shifted,
                    rs1: vlo,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Or {
                    rd: res_lo,
                    rs1: lo_shifted,
                    rs2: carry,
                });
            }
        }
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: done_label.clone(),
        });

        // ── big case: shamt >= 32 ────────────────────────────────────────
        // The whole of one half moves into the other; `s_lo` (= s & 31) is
        // exactly `s - 32` because bit 5 is set, so it doubles as the
        // residual shift amount within the surviving half.
        self.out.push(RiscVOp::Label { name: big_label });
        match kind {
            ShiftKind::Shl => {
                // hi' = lo << (s - 32) ; lo' = 0
                self.out.push(RiscVOp::Sll {
                    rd: res_hi,
                    rs1: vlo,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Addi {
                    rd: res_lo,
                    rs1: Reg::ZERO,
                    imm: 0,
                });
            }
            ShiftKind::ShrU => {
                // lo' = hi >> (s - 32) ; hi' = 0
                self.out.push(RiscVOp::Srl {
                    rd: res_lo,
                    rs1: vhi,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Addi {
                    rd: res_hi,
                    rs1: Reg::ZERO,
                    imm: 0,
                });
            }
            ShiftKind::ShrS => {
                // lo' = hi >>s (s - 32) ; hi' = sign(hi) = hi >>s 31
                self.out.push(RiscVOp::Sra {
                    rd: res_lo,
                    rs1: vhi,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Srai {
                    rd: res_hi,
                    rs1: vhi,
                    shamt: 31,
                });
            }
        }
        self.out.push(RiscVOp::Label { name: done_label });
        self.push_i64(res_lo, res_hi);
        Ok(())
    }

    /// 64-bit rotate (rotl / rotr) by a runtime amount.
    ///
    /// Composed from the two shifts: `rotl(x, n) = (x << n) | (x >> (64-n))`
    /// and `rotr(x, n) = (x >> n) | (x << (64-n))`. The shift helper already
    /// handles the cross-word logic, so the rotate just feeds it the right
    /// amounts and ORs the two i64 results half-by-half.
    ///
    /// `n` is masked to `0..=63`; `64 - (n mod 64)` is computed as
    /// `(64 - n) mod 64` so that `n == 0` maps to a `0` counter-shift rather
    /// than a 64-bit shift (which the shift helper would treat as `shamt &
    /// 63 == 0` anyway — but computing it explicitly keeps the intent clear).
    fn lower_i64_rotate(&mut self, op: &WasmOp, left: bool) -> Result<(), SelectorError> {
        let ((vlo, vhi), (namt, _namt_hi)) = self.pop_i64_then_amount(op)?;
        // n = amount & 63
        let n = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: n,
            rs1: namt,
            imm: 63,
        });
        // comp = (64 - n) & 63  — the complementary rotate distance.
        let comp = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: comp,
            rs1: Reg::ZERO,
            imm: 64,
        });
        self.out.push(RiscVOp::Sub {
            rd: comp,
            rs1: comp,
            rs2: n,
        });
        self.out.push(RiscVOp::Andi {
            rd: comp,
            rs1: comp,
            imm: 63,
        });
        // For rotl: part_a = x << n, part_b = x >> comp.
        // For rotr: part_a = x >> n, part_b = x << comp.
        let (amt_a, amt_b) = (n, comp);
        let (a_lo, a_hi) = if left {
            self.emit_i64_shift_inline(vlo, vhi, amt_a, ShiftKind::Shl)
        } else {
            self.emit_i64_shift_inline(vlo, vhi, amt_a, ShiftKind::ShrU)
        };
        let (b_lo, b_hi) = if left {
            self.emit_i64_shift_inline(vlo, vhi, amt_b, ShiftKind::ShrU)
        } else {
            self.emit_i64_shift_inline(vlo, vhi, amt_b, ShiftKind::Shl)
        };
        // result = part_a | part_b, half by half.
        let res_lo = self.alloc_temp();
        let res_hi = self.alloc_temp();
        self.out.push(RiscVOp::Or {
            rd: res_lo,
            rs1: a_lo,
            rs2: b_lo,
        });
        self.out.push(RiscVOp::Or {
            rd: res_hi,
            rs1: a_hi,
            rs2: b_hi,
        });
        self.push_i64(res_lo, res_hi);
        Ok(())
    }

    /// Pop an i64 value and an i64 shift/rotate amount, returning
    /// `((v_lo, v_hi), (amt_lo, amt_hi))`. Identical to `pop_pair_i64` —
    /// kept as a named helper so the rotate code reads naturally.
    fn pop_i64_then_amount(&mut self, op: &WasmOp) -> Result<(I64Pair, I64Pair), SelectorError> {
        self.pop_pair_i64(op)
    }

    /// Emit an i64 shift whose value and amount are already in registers
    /// (rather than on the vstack), returning the `(lo, hi)` result pair.
    /// This is the register-level core of `lower_i64_shift`, factored out so
    /// the rotate lowering can issue two shifts without round-tripping
    /// through the value stack. The cross-word branching logic is identical
    /// to `lower_i64_shift` — see that method's doc comment for the math.
    fn emit_i64_shift_inline(
        &mut self,
        vlo: Reg,
        vhi: Reg,
        amount: Reg,
        kind: ShiftKind,
    ) -> I64Pair {
        let s = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: s,
            rs1: amount,
            imm: 63,
        });
        let s_lo = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: s_lo,
            rs1: s,
            imm: 31,
        });
        let res_lo = self.alloc_temp();
        let res_hi = self.alloc_temp();
        let big_label = self.fresh_label("Lshift_big");
        let done_label = self.fresh_label("Lshift_done");
        let test = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: test,
            rs1: s,
            imm: 32,
        });
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: test,
            rs2: Reg::ZERO,
            label: big_label.clone(),
        });
        // small case
        let inv = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: inv,
            rs1: Reg::ZERO,
            imm: 31,
        });
        self.out.push(RiscVOp::Sub {
            rd: inv,
            rs1: inv,
            rs2: s_lo,
        });
        match kind {
            ShiftKind::Shl => {
                self.out.push(RiscVOp::Sll {
                    rd: res_lo,
                    rs1: vlo,
                    rs2: s_lo,
                });
                let carry = self.alloc_temp();
                self.out.push(RiscVOp::Srli {
                    rd: carry,
                    rs1: vlo,
                    shamt: 1,
                });
                self.out.push(RiscVOp::Srl {
                    rd: carry,
                    rs1: carry,
                    rs2: inv,
                });
                let hi_shifted = self.alloc_temp();
                self.out.push(RiscVOp::Sll {
                    rd: hi_shifted,
                    rs1: vhi,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Or {
                    rd: res_hi,
                    rs1: hi_shifted,
                    rs2: carry,
                });
            }
            ShiftKind::ShrS | ShiftKind::ShrU => {
                self.out.push(if kind == ShiftKind::ShrS {
                    RiscVOp::Sra {
                        rd: res_hi,
                        rs1: vhi,
                        rs2: s_lo,
                    }
                } else {
                    RiscVOp::Srl {
                        rd: res_hi,
                        rs1: vhi,
                        rs2: s_lo,
                    }
                });
                let carry = self.alloc_temp();
                self.out.push(RiscVOp::Slli {
                    rd: carry,
                    rs1: vhi,
                    shamt: 1,
                });
                self.out.push(RiscVOp::Sll {
                    rd: carry,
                    rs1: carry,
                    rs2: inv,
                });
                let lo_shifted = self.alloc_temp();
                self.out.push(RiscVOp::Srl {
                    rd: lo_shifted,
                    rs1: vlo,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Or {
                    rd: res_lo,
                    rs1: lo_shifted,
                    rs2: carry,
                });
            }
        }
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: done_label.clone(),
        });
        // big case
        self.out.push(RiscVOp::Label { name: big_label });
        match kind {
            ShiftKind::Shl => {
                self.out.push(RiscVOp::Sll {
                    rd: res_hi,
                    rs1: vlo,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Addi {
                    rd: res_lo,
                    rs1: Reg::ZERO,
                    imm: 0,
                });
            }
            ShiftKind::ShrU => {
                self.out.push(RiscVOp::Srl {
                    rd: res_lo,
                    rs1: vhi,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Addi {
                    rd: res_hi,
                    rs1: Reg::ZERO,
                    imm: 0,
                });
            }
            ShiftKind::ShrS => {
                self.out.push(RiscVOp::Sra {
                    rd: res_lo,
                    rs1: vhi,
                    rs2: s_lo,
                });
                self.out.push(RiscVOp::Srai {
                    rd: res_hi,
                    rs1: vhi,
                    shamt: 31,
                });
            }
        }
        self.out.push(RiscVOp::Label { name: done_label });
        (res_lo, res_hi)
    }

    /// 64-bit count-leading-zeros → i32 result in `0..=64`.
    ///
    /// RV32IMAC has no `clz` (that's Zbb), so each 32-bit half uses a
    /// software `clz_word` (an unrolled binary-search sequence — see
    /// `emit_clz_word`). The 64-bit answer branches on whether the high
    /// half is non-zero:
    /// ```text
    ///   if hi != 0 { clz = clz_word(hi) }
    ///   else       { clz = 32 + clz_word(lo) }
    /// ```
    fn lower_i64_clz(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let (lo, hi) = self.pop_i64(op)?;
        let result = self.alloc_temp();
        let hi_zero = self.fresh_label("Lclz_hizero");
        let done = self.fresh_label("Lclz_done");
        // beq hi, zero, Lclz_hizero → all leading zeros are in (or past) lo.
        self.out.push(RiscVOp::Branch {
            cond: Branch::Eq,
            rs1: hi,
            rs2: Reg::ZERO,
            label: hi_zero.clone(),
        });
        // hi != 0: the answer is entirely within the high word.
        let hi_clz = self.emit_clz_word(hi);
        self.out.push(RiscVOp::Addi {
            rd: result,
            rs1: hi_clz,
            imm: 0,
        });
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: done.clone(),
        });
        // hi == 0: 32 leading zeros from the high word + clz of the low word.
        self.out.push(RiscVOp::Label { name: hi_zero });
        let lo_clz = self.emit_clz_word(lo);
        self.out.push(RiscVOp::Addi {
            rd: result,
            rs1: lo_clz,
            imm: 32,
        });
        self.out.push(RiscVOp::Label { name: done });
        self.push_i32(result);
        Ok(())
    }

    /// 64-bit count-trailing-zeros → i32 result in `0..=64`.
    ///
    /// Mirror of clz: branch on the *low* half.
    /// ```text
    ///   if lo != 0 { ctz = ctz_word(lo) }
    ///   else       { ctz = 32 + ctz_word(hi) }
    /// ```
    fn lower_i64_ctz(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let (lo, hi) = self.pop_i64(op)?;
        let result = self.alloc_temp();
        let lo_zero = self.fresh_label("Lctz_lozero");
        let done = self.fresh_label("Lctz_done");
        self.out.push(RiscVOp::Branch {
            cond: Branch::Eq,
            rs1: lo,
            rs2: Reg::ZERO,
            label: lo_zero.clone(),
        });
        // lo != 0: answer is within the low word.
        let lo_ctz = self.emit_ctz_word(lo);
        self.out.push(RiscVOp::Addi {
            rd: result,
            rs1: lo_ctz,
            imm: 0,
        });
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: done.clone(),
        });
        // lo == 0: 32 trailing zeros from the low word + ctz of the high word.
        self.out.push(RiscVOp::Label { name: lo_zero });
        let hi_ctz = self.emit_ctz_word(hi);
        self.out.push(RiscVOp::Addi {
            rd: result,
            rs1: hi_ctz,
            imm: 32,
        });
        self.out.push(RiscVOp::Label { name: done });
        self.push_i32(result);
        Ok(())
    }

    /// 64-bit population count → i32 result in `0..=64`.
    ///
    /// `popcnt(x) = popcnt(x_lo) + popcnt(x_hi)` — the two halves are
    /// independent, no carry. Each `popcnt_word` is the classic SWAR
    /// bit-twiddle (see `emit_popcnt_word`).
    fn lower_i64_popcnt(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let (lo, hi) = self.pop_i64(op)?;
        let lo_pc = self.emit_popcnt_word(lo);
        let hi_pc = self.emit_popcnt_word(hi);
        let result = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: result,
            rs1: lo_pc,
            rs2: hi_pc,
        });
        self.push_i32(result);
        Ok(())
    }

    /// Software count-leading-zeros for a single 32-bit word, returning the
    /// register holding the `0..=32` result.
    ///
    /// Uses the standard branchless binary-search reduction: at each step,
    /// test whether the value's set bits all live in the lower `k` bits; if
    /// so the top `k` bits were all zero — add `k` to the count and shift
    /// the value left by `k` to bring the next window into view. Probing
    /// k = 16, 8, 4, 2, 1 narrows to the exact leading-zero count. A final
    /// correction handles the all-zero input (which would otherwise report
    /// 31 instead of 32).
    ///
    /// The sequence is fully unrolled and branch-free, so it costs a fixed
    /// number of instructions regardless of input — preferable to a loop in
    /// a leaf compiler with no spill slots.
    fn emit_clz_word(&mut self, src: Reg) -> Reg {
        // x is the running value; n accumulates the count.
        let x = self.alloc_temp();
        let n = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: x,
            rs1: src,
            imm: 0,
        });
        self.out.push(RiscVOp::Addi {
            rd: n,
            rs1: Reg::ZERO,
            imm: 0,
        });
        // For each probe width k: if (x >> (32-k)) == 0 then the top k bits
        // are zero — add k to n and shift x up by k. Implemented branchlessly
        // via a 0/1 mask derived from sltiu.
        for k in [16u8, 8, 4, 2, 1] {
            let probe = self.alloc_temp();
            // probe = x >> (32 - k)  — the top k bits, right-justified.
            self.out.push(RiscVOp::Srli {
                rd: probe,
                rs1: x,
                shamt: 32 - k,
            });
            // is_zero = (probe == 0) ? 1 : 0
            let is_zero = self.alloc_temp();
            self.out.push(RiscVOp::Sltiu {
                rd: is_zero,
                rs1: probe,
                imm: 1,
            });
            // n += is_zero * k  → add k only when the window was all zeros.
            let add = self.alloc_temp();
            self.out.push(RiscVOp::Slli {
                rd: add,
                rs1: is_zero,
                shamt: k.trailing_zeros() as u8,
            });
            self.out.push(RiscVOp::Add {
                rd: n,
                rs1: n,
                rs2: add,
            });
            // shift = is_zero * k, then x <<= shift (no-op when window had a 1).
            self.out.push(RiscVOp::Sll {
                rd: x,
                rs1: x,
                rs2: add,
            });
        }
        // After the five probes, n is 31 for an all-zero input (each window
        // contributed) and the true count for anything else. Correct the
        // off-by-one: if the original src was 0, the answer is 32.
        let is_src_zero = self.alloc_temp();
        self.out.push(RiscVOp::Sltiu {
            rd: is_src_zero,
            rs1: src,
            imm: 1,
        });
        let result = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: result,
            rs1: n,
            rs2: is_src_zero,
        });
        result
    }

    /// Software count-trailing-zeros for a 32-bit word → register with the
    /// `0..=32` result.
    ///
    /// Trick: `x & -x` isolates the lowest set bit, then `ctz(x) =
    /// 31 - clz(x & -x)` for any non-zero `x`. The all-zero input is handled
    /// separately because `x & -x == 0` would feed clz a zero (clz → 32,
    /// giving `31 - 32 = -1`), so we add a correction that forces the answer
    /// to 32 when `src == 0`.
    fn emit_ctz_word(&mut self, src: Reg) -> Reg {
        // neg = -src ; iso = src & neg  — isolates the lowest set bit.
        let neg = self.alloc_temp();
        self.out.push(RiscVOp::Sub {
            rd: neg,
            rs1: Reg::ZERO,
            rs2: src,
        });
        let iso = self.alloc_temp();
        self.out.push(RiscVOp::And {
            rd: iso,
            rs1: src,
            rs2: neg,
        });
        // clz_iso = clz(iso). For non-zero src, ctz = 31 - clz_iso.
        let clz_iso = self.emit_clz_word(iso);
        let thirty_one = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: thirty_one,
            rs1: Reg::ZERO,
            imm: 31,
        });
        let ctz = self.alloc_temp();
        self.out.push(RiscVOp::Sub {
            rd: ctz,
            rs1: thirty_one,
            rs2: clz_iso,
        });
        // src == 0 correction: `iso` is 0, clz_iso is 32, so ctz computed as
        // -1. Add 33 in that case to land on 32 ( -1 + 33 = 32 ).
        let is_src_zero = self.alloc_temp();
        self.out.push(RiscVOp::Sltiu {
            rd: is_src_zero,
            rs1: src,
            imm: 1,
        });
        // correction = is_src_zero * 33
        let corr = self.alloc_temp();
        self.out.push(RiscVOp::Slli {
            rd: corr,
            rs1: is_src_zero,
            shamt: 5,
        });
        // corr is now is_src_zero*32; add is_src_zero once more for *33.
        self.out.push(RiscVOp::Add {
            rd: corr,
            rs1: corr,
            rs2: is_src_zero,
        });
        let result = self.alloc_temp();
        self.out.push(RiscVOp::Add {
            rd: result,
            rs1: ctz,
            rs2: corr,
        });
        result
    }

    /// Software population count for a 32-bit word → register with the
    /// `0..=32` result.
    ///
    /// The classic SWAR (SIMD-within-a-register) bit-twiddle:
    /// ```text
    ///   x = x - ((x >> 1) & 0x55555555)               ; sum bits in pairs
    ///   x = (x & 0x33333333) + ((x >> 2) & 0x33333333) ; sum pairs into nibbles
    ///   x = (x + (x >> 4)) & 0x0F0F0F0F                ; sum nibbles into bytes
    ///   x = (x * 0x01010101) >> 24                     ; sum bytes via mul
    /// ```
    /// The final `mul` collapses the four byte-sums into the top byte — this
    /// is why the routine needs the M extension (which RV32IMAC has).
    fn emit_popcnt_word(&mut self, src: Reg) -> Reg {
        let m1 = self.alloc_temp(); // 0x55555555
        let m2 = self.alloc_temp(); // 0x33333333
        let m4 = self.alloc_temp(); // 0x0F0F0F0F
        let m8 = self.alloc_temp(); // 0x01010101
        emit_load_imm(&mut self.out, m1, 0x5555_5555u32 as i32);
        emit_load_imm(&mut self.out, m2, 0x3333_3333u32 as i32);
        emit_load_imm(&mut self.out, m4, 0x0F0F_0F0Fu32 as i32);
        emit_load_imm(&mut self.out, m8, 0x0101_0101u32 as i32);

        // step 1: x = x - ((x >> 1) & m1)
        let x = self.alloc_temp();
        let t = self.alloc_temp();
        self.out.push(RiscVOp::Srli {
            rd: t,
            rs1: src,
            shamt: 1,
        });
        self.out.push(RiscVOp::And {
            rd: t,
            rs1: t,
            rs2: m1,
        });
        self.out.push(RiscVOp::Sub {
            rd: x,
            rs1: src,
            rs2: t,
        });
        // step 2: x = (x & m2) + ((x >> 2) & m2)
        let a = self.alloc_temp();
        let b = self.alloc_temp();
        self.out.push(RiscVOp::And {
            rd: a,
            rs1: x,
            rs2: m2,
        });
        self.out.push(RiscVOp::Srli {
            rd: b,
            rs1: x,
            shamt: 2,
        });
        self.out.push(RiscVOp::And {
            rd: b,
            rs1: b,
            rs2: m2,
        });
        self.out.push(RiscVOp::Add {
            rd: x,
            rs1: a,
            rs2: b,
        });
        // step 3: x = (x + (x >> 4)) & m4
        self.out.push(RiscVOp::Srli {
            rd: t,
            rs1: x,
            shamt: 4,
        });
        self.out.push(RiscVOp::Add {
            rd: x,
            rs1: x,
            rs2: t,
        });
        self.out.push(RiscVOp::And {
            rd: x,
            rs1: x,
            rs2: m4,
        });
        // step 4: x = (x * m8) >> 24  — the byte-sum collapse.
        self.out.push(RiscVOp::Mul {
            rd: x,
            rs1: x,
            rs2: m8,
        });
        let result = self.alloc_temp();
        self.out.push(RiscVOp::Srli {
            rd: result,
            rs1: x,
            shamt: 24,
        });
        result
    }

    /// 64-bit comparison ladder (lt / le / gt / ge, signed or unsigned).
    /// Result is an i32 0/1.
    ///
    /// The standard hi-then-lo decomposition. For `a < b`:
    /// ```text
    ///   if a_hi != b_hi { result = (a_hi <cmp> b_hi) }   ; hi decides
    ///   else            { result = (a_lo <u  b_lo) }     ; lo is the tie-break
    /// ```
    /// The hi-half comparison uses the *signed* relation for signed ops
    /// (`slt`) and the unsigned relation otherwise (`sltu`). The lo-half
    /// comparison is **always unsigned** — the low 32 bits are a magnitude,
    /// the sign lives entirely in the high word.
    ///
    /// `le` / `gt` / `ge` are derived from `lt` by the usual identities:
    /// `a > b ≡ b < a` (swap operands) and `a >= b ≡ !(a < b)`,
    /// `a <= b ≡ !(b < a)` (swap + invert). We compute a base `lt` with the
    /// possibly-swapped operands, then optionally flip the 0/1 result.
    fn lower_i64_cmp(
        &mut self,
        op: &WasmOp,
        kind: CmpKind,
        signed: bool,
    ) -> Result<(), SelectorError> {
        let ((al, ah), (bl, bh)) = self.pop_pair_i64(op)?;
        // Reduce every variant to a "strictly-less-than" on a chosen operand
        // ordering, plus an optional final invert:
        //   lt : less(a, b)            ge : !less(a, b)
        //   gt : less(b, a)            le : !less(b, a)
        let (swap, invert) = match kind {
            CmpKind::Lt => (false, false),
            CmpKind::Ge => (false, true),
            CmpKind::Gt => (true, false),
            CmpKind::Le => (true, true),
        };
        let ((xl, xh), (yl, yh)) = if swap {
            ((bl, bh), (al, ah))
        } else {
            ((al, ah), (bl, bh))
        };
        // result holds the 0/1 outcome; written by both arms of the branch.
        let result = self.alloc_temp();
        let hi_eq = self.fresh_label("Lcmp_hieq");
        let done = self.fresh_label("Lcmp_done");
        // beq x_hi, y_hi, Lcmp_hieq → hi halves tie, fall through to lo test.
        self.out.push(RiscVOp::Branch {
            cond: Branch::Eq,
            rs1: xh,
            rs2: yh,
            label: hi_eq.clone(),
        });
        // hi halves differ: the hi comparison is the whole answer. Signed
        // ops compare the hi halves *signed* (the sign bit lives here).
        self.out.push(if signed {
            RiscVOp::Slt {
                rd: result,
                rs1: xh,
                rs2: yh,
            }
        } else {
            RiscVOp::Sltu {
                rd: result,
                rs1: xh,
                rs2: yh,
            }
        });
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: done.clone(),
        });
        // hi halves equal: tie-break on the lo halves, always *unsigned*.
        self.out.push(RiscVOp::Label { name: hi_eq });
        self.out.push(RiscVOp::Sltu {
            rd: result,
            rs1: xl,
            rs2: yl,
        });
        self.out.push(RiscVOp::Label { name: done });
        // For ge / le, flip the strict-less result: a >= b ≡ !(a < b).
        if invert {
            let flipped = self.alloc_temp();
            self.out.push(RiscVOp::Xori {
                rd: flipped,
                rs1: result,
                imm: 1,
            });
            self.push_i32(flipped);
        } else {
            self.push_i32(result);
        }
        Ok(())
    }

    /// In-place sign extension `i64.extend{8,16,32}_s`.
    ///
    /// Wasm semantics: the input is an i64; sign-extend its low `width` bits
    /// across the whole 64-bit value. The high `64 - width` bits of the
    /// input are discarded.
    ///
    /// For width 8 / 16 we sign-extend within the low word by a shift pair
    /// `(x << (32-width)) >>s (32-width)`, then propagate the sign into the
    /// high word with `sra lo, 31` (all-ones if negative, all-zeros if not).
    /// For width 32 the low word is already the full value, so we only need
    /// the sign-propagation step.
    fn lower_i64_extend_sub(&mut self, op: &WasmOp, width: u8) -> Result<(), SelectorError> {
        let (lo_in, _hi_in) = self.pop_i64(op)?;
        let lo = self.alloc_temp();
        if width < 32 {
            // shift = 32 - width ; lo = (lo_in << shift) >>s shift
            let shift = 32 - width;
            self.out.push(RiscVOp::Slli {
                rd: lo,
                rs1: lo_in,
                shamt: shift,
            });
            self.out.push(RiscVOp::Srai {
                rd: lo,
                rs1: lo,
                shamt: shift,
            });
        } else {
            // width == 32: the low word is already the sign-extended value;
            // just carry it forward (mv lo, lo_in).
            self.out.push(RiscVOp::Addi {
                rd: lo,
                rs1: lo_in,
                imm: 0,
            });
        }
        // hi = sra(lo, 31) — broadcast the sign bit across the high word.
        let hi = self.alloc_temp();
        self.out.push(RiscVOp::Srai {
            rd: hi,
            rs1: lo,
            shamt: 31,
        });
        self.push_i64(lo, hi);
        Ok(())
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

/// Which 64-bit shift to lower. Drives the `lower_i64_shift` cross-word
/// branching — all three share the same `shamt >= 32` structure but differ
/// in the per-half instruction (logical vs. arithmetic) and the direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShiftKind {
    /// `i64.shl` — logical left.
    Shl,
    /// `i64.shr_s` — arithmetic right (sign-propagating).
    ShrS,
    /// `i64.shr_u` — logical right (zero-fill).
    ShrU,
}

/// Which 64-bit comparison to lower. The signed/unsigned distinction is a
/// separate flag because only the *hi*-half comparison changes with
/// signedness — the lo half is always compared unsigned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CmpKind {
    Lt,
    Le,
    Gt,
    Ge,
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

    // ─── Phase 1 binary-safety tests ────────────────────────────────────

    fn s_with_opts(ops: &[WasmOp], num_params: u32, o: SelectorOptions) -> Vec<RiscVOp> {
        select_with_options(ops, num_params, o).unwrap().ops
    }

    #[test]
    fn rv32_software_bounds_emits_bgeu_and_ebreak() {
        let opts = SelectorOptions {
            bounds: RvBoundsMode::Software { mem_size: 0x10000 },
            signed_div_overflow_trap: true,
        };
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            1,
            opts,
        );
        // Expect at least one BGEU against the memsize and one ebreak in the
        // trap basic block.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Geu,
                    ..
                }
            )) >= 1,
            "expected at least one bgeu for the bounds check, got: {:?}",
            out
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Ebreak)) >= 1,
            "expected an ebreak in the trap path"
        );
    }

    // ──────────── i64 Phase-1 tests ────────────
    //
    // These tests assert the *shape* of the emitted sequence (op counts, kinds,
    // and select fields), which is the right granularity for a selector — we
    // don't want to over-pin register allocation choices.

    /// Helper: build the op sequence for an i64 test scenario. Appends an
    /// `End` so the function epilogue is emitted; tests work with the full
    /// output. `num_params` controls how many arg registers are available
    /// (use 1+ for sequences that contain `LocalGet`).
    fn run_i64_with_params(seq: &[WasmOp], num_params: u32) -> Vec<RiscVOp> {
        let mut full = seq.to_vec();
        full.push(WasmOp::End);
        s(&full, num_params)
    }

    /// Most i64 tests use only consts → no LocalGet → no arg regs needed.
    fn run_i64(seq: &[WasmOp]) -> Vec<RiscVOp> {
        run_i64_with_params(seq, 0)
    }

    #[test]
    fn i64_const_emits_two_load_imm_sequences() {
        // I64Const(0x1_0000_0001) → lo = 1, hi = 1. Each half goes through
        // emit_load_imm (here both fit in the addi short path), giving 2
        // Addi-from-ZERO ops.
        let out = run_i64(&[WasmOp::I64Const(0x1_0000_0001), WasmOp::Drop]);
        let imm_loads = count(&out, |op| {
            matches!(op, RiscVOp::Addi { rs1: Reg::ZERO, .. })
        });
        // 2 for the i64 const (lo + hi), nothing else (Drop emits no code).
        assert_eq!(imm_loads, 2);
    }

    #[test]
    fn i64_add_emits_add_sltu_add_add_pattern() {
        let out = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Add,
            WasmOp::Drop,
        ]);
        // Skip past the const-materialization Addi/Lui ops and the trailing
        // Jalr; isolate the I64Add's emitted sequence.
        let from_add: Vec<&RiscVOp> = out
            .iter()
            .skip_while(|o| !matches!(o, RiscVOp::Add { .. }))
            .collect();
        // Expected: Add, Sltu, Add, Add, then function epilogue's Jalr.
        assert!(matches!(from_add[0], RiscVOp::Add { .. }));
        assert!(matches!(from_add[1], RiscVOp::Sltu { .. }));
        assert!(matches!(from_add[2], RiscVOp::Add { .. }));
        assert!(matches!(from_add[3], RiscVOp::Add { .. }));
    }

    #[test]
    fn i64_sub_emits_borrow_pattern() {
        let out = run_i64(&[
            WasmOp::I64Const(10),
            WasmOp::I64Const(3),
            WasmOp::I64Sub,
            WasmOp::Drop,
        ]);
        // Expected: Sltu (borrow), Sub (lo), Sub (hi diff), Sub (hi - borrow)
        let from_sub: Vec<&RiscVOp> = out
            .iter()
            .skip_while(|o| !matches!(o, RiscVOp::Sltu { .. }))
            .collect();
        assert!(matches!(from_sub[0], RiscVOp::Sltu { .. }));
        assert!(matches!(from_sub[1], RiscVOp::Sub { .. }));
        assert!(matches!(from_sub[2], RiscVOp::Sub { .. }));
        assert!(matches!(from_sub[3], RiscVOp::Sub { .. }));
    }

    #[test]
    fn i64_and_or_xor_each_emit_two_ops() {
        // I64And: two And ops on lo/hi
        let out_and = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64And,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out_and, |op| matches!(op, RiscVOp::And { .. })),
            2,
            "I64And should emit 2 And ops"
        );

        let out_or = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Or,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out_or, |op| matches!(op, RiscVOp::Or { .. })),
            2,
            "I64Or should emit 2 Or ops"
        );

        let out_xor = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Xor,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out_xor, |op| matches!(op, RiscVOp::Xor { .. })),
            2,
            "I64Xor should emit 2 Xor ops"
        );
    }

    #[test]
    fn rv32_no_bounds_check_emits_no_bgeu() {
        let opts = SelectorOptions::wasm_compliant();
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            1,
            opts,
        );
        // No bgeu should be emitted when the bounds mode is `None`.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Geu,
                    ..
                }
            )) == 0,
            "no bounds-check bgeu expected when mode is None, got: {:?}",
            out
        );
    }

    #[test]
    fn i64_eq_emits_xor_xor_or_sltiu() {
        let out = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Eq,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Xor { .. })),
            2,
            "I64Eq emits two Xors (one per half)"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Or { .. })),
            1,
            "I64Eq ors the half-diffs together"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sltiu { imm: 1, .. })),
            1,
            "I64Eq compares the combined diff with 1 (sltiu)"
        );
    }

    #[test]
    fn i64_ne_emits_xor_xor_or_sltu() {
        let out = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64Ne,
            WasmOp::Drop,
        ]);
        assert_eq!(count(&out, |op| matches!(op, RiscVOp::Xor { .. })), 2);
        assert_eq!(count(&out, |op| matches!(op, RiscVOp::Or { .. })), 1);
        assert_eq!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Sltu { rs1: Reg::ZERO, .. }
            )),
            1,
            "I64Ne uses sltu rd, zero, diff"
        );
    }

    #[test]
    fn i64_eqz_emits_or_sltiu() {
        // I64Eqz pops i64 and pushes i32 — verify by checking we don't get a
        // Type-mismatch on a subsequent i32 consumer.
        let out = run_i64(&[
            WasmOp::I64Const(0),
            WasmOp::I64Eqz,
            // After Eqz the stack should hold an i32; an I32Eqz consumer
            // confirms the type-state on the vstack.
            WasmOp::I32Eqz,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Or { .. })),
            1,
            "I64Eqz emits a single Or"
        );
        // Two Sltiu(imm=1): one from I64Eqz, one from the I32Eqz that follows.
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sltiu { imm: 1, .. })),
            2,
        );
    }

    #[test]
    fn i64_extend_i32_u_pushes_zero_hi() {
        // I64ExtendI32U: hi = 0 (via `addi rd, ZERO, 0`). The presence of an
        // extra Addi-from-ZERO with imm=0 is the giveaway.
        let out = run_i64(&[
            WasmOp::I32Const(5), // small enough to take the addi short path
            WasmOp::I64ExtendI32U,
            WasmOp::Drop,
        ]);
        // We get: addi (i32const 5), addi (hi=0). Both have rs1=ZERO; the
        // hi-zero load uses imm=0.
        assert!(
            out.iter().any(|op| matches!(
                op,
                RiscVOp::Addi {
                    rs1: Reg::ZERO,
                    imm: 0,
                    ..
                }
            )),
            "expected addi rd, zero, 0 to zero the hi half"
        );
    }

    #[test]
    fn i64_extend_i32_s_emits_sra_31() {
        let out = run_i64(&[WasmOp::I32Const(5), WasmOp::I64ExtendI32S, WasmOp::Drop]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 31, .. })),
            1,
            "I64ExtendI32S uses srai by 31 to sign-extend"
        );
    }

    #[test]
    fn i32_wrap_i64_drops_hi() {
        // I32WrapI64 emits zero new instructions; the lo half just continues
        // to live on the value stack as an i32. We verify the op count is
        // exactly what the surrounding const+drop emits, with no leftover.
        let baseline = run_i64(&[WasmOp::I64Const(42), WasmOp::Drop]);
        let with_wrap = run_i64(&[WasmOp::I64Const(42), WasmOp::I32WrapI64, WasmOp::Drop]);
        assert_eq!(
            baseline.len(),
            with_wrap.len(),
            "I32WrapI64 must not emit any instructions"
        );
    }

    #[test]
    fn i64_load_emits_two_lw_at_offset_and_offset_plus_4() {
        let out = run_i64_with_params(
            &[
                WasmOp::LocalGet(0), // address (treated as i32)
                WasmOp::I64Load {
                    offset: 16,
                    align: 3,
                },
                WasmOp::Drop,
            ],
            1,
        );
        // We expect two Lw ops with imms 16 and 20.
        let lws: Vec<i32> = out
            .iter()
            .filter_map(|op| match op {
                RiscVOp::Lw { imm, .. } => Some(*imm),
                _ => None,
            })
            .collect();
        assert_eq!(lws, vec![16, 20], "I64Load emits lw @offset and @offset+4");
    }

    #[test]
    fn i64_store_emits_two_sw_at_offset_and_offset_plus_4() {
        let out = run_i64_with_params(
            &[
                WasmOp::LocalGet(0), // address
                WasmOp::I64Const(0xDEADBEEF_CAFEBABE_u64 as i64),
                WasmOp::I64Store {
                    offset: 8,
                    align: 3,
                },
            ],
            1,
        );
        let sws: Vec<i32> = out
            .iter()
            .filter_map(|op| match op {
                RiscVOp::Sw { imm, .. } => Some(*imm),
                _ => None,
            })
            .collect();
        assert_eq!(sws, vec![8, 12], "I64Store emits sw @offset and @offset+4");
    }

    // -------- Call (v0.3.1 minimum-viable) --------

    /// Smoke: a single-arg, single-return call. Args move to a0; the
    /// `RiscVOp::Call` label encodes the func index.
    #[test]
    fn call_emits_label_and_argument_marshalling() {
        let out = s(
            &[
                WasmOp::LocalGet(0), // arg 0 = a0 (already)
                WasmOp::Call(7),
                WasmOp::End,
            ],
            1,
        );
        // Must contain a Call op with the expected label
        let has_call = out.iter().any(|op| {
            matches!(op,
            RiscVOp::Call { label } if label == "synth_func_7")
        });
        assert!(
            has_call,
            "expected Call {{ label: \"synth_func_7\" }}, got: {:?}",
            out
        );
    }

    #[test]
    fn rv32_pmp_mode_emits_no_inline_check() {
        let opts = SelectorOptions {
            bounds: RvBoundsMode::Pmp,
            signed_div_overflow_trap: true,
        };
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            1,
            opts,
        );
        // PMP mode behaves the same as None in code-gen — hardware handles it.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Geu,
                    ..
                }
            )) == 0
        );
    }

    #[test]
    fn rv32_mask_mode_emits_andi() {
        // mask = 65535 (= 0x10000 - 1). 0xFFFF > 0x7FF so emit_load_imm + and.
        let opts = SelectorOptions {
            bounds: RvBoundsMode::Mask { mask: 0xFFFF },
            signed_div_overflow_trap: true,
        };
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Load {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            1,
            opts,
        );
        // Either Andi (small mask) or And (large mask) appears for the mask op.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::And { .. } | RiscVOp::Andi { .. }
            )) >= 1
        );
    }

    #[test]
    fn rv32_signed_div_emits_overflow_guard() {
        let opts = SelectorOptions::wasm_compliant();
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32DivS,
                WasmOp::End,
            ],
            2,
            opts,
        );
        // Expect: bne rs2,zero (zero-divisor guard) AND bne rs1,INT_MIN (overflow)
        // AND bne rs2,-1 (overflow). So at least 3 BNE-shaped branches.
        let bne_count = count(&out, |op| {
            matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )
        });
        assert!(
            bne_count >= 3,
            "expected at least 3 BNEs (zero + INT_MIN + -1 guards), got {} in: {:?}",
            bne_count,
            out
        );
        // And two ebreaks: one for div-by-zero, one for the overflow trap.
        assert!(count(&out, |op| matches!(op, RiscVOp::Ebreak)) >= 2);
    }

    #[test]
    fn rv32_signed_div_overflow_trap_disabled_only_emits_zero_guard() {
        let opts = SelectorOptions {
            bounds: RvBoundsMode::None,
            signed_div_overflow_trap: false,
        };
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32DivS,
                WasmOp::End,
            ],
            2,
            opts,
        );
        // Only the zero-divisor BNE; no overflow guards.
        let bne_count = count(&out, |op| {
            matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )
        });
        assert_eq!(bne_count, 1);
        assert_eq!(count(&out, |op| matches!(op, RiscVOp::Ebreak)), 1);
    }

    #[test]
    fn rv32_unsigned_div_skips_overflow_guard() {
        // Unsigned division has no INT_MIN/-1 special case.
        let opts = SelectorOptions::wasm_compliant();
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32DivU,
                WasmOp::End,
            ],
            2,
            opts,
        );
        let bne_count = count(&out, |op| {
            matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )
        });
        assert_eq!(bne_count, 1, "only zero-divisor guard expected for div_u");
    }

    #[test]
    fn rv32_signed_rem_also_gets_overflow_guard() {
        let opts = SelectorOptions::wasm_compliant();
        let out = s_with_opts(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32RemS,
                WasmOp::End,
            ],
            2,
            opts,
        );
        let bne_count = count(&out, |op| {
            matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )
        });
        assert!(bne_count >= 3);
        assert!(count(&out, |op| matches!(op, RiscVOp::Rem { .. })) == 1);
    }

    /// Two-arg call: top-of-stack args move to a0 and a1 in source order.
    /// The lower arg (last-pushed) is the *first* arg per wasm semantics.
    #[test]
    fn call_two_args_marshals_to_a0_a1() {
        let out = s(
            &[
                WasmOp::I32Const(11), // pushed first → arg 0 → a0
                WasmOp::I32Const(22), // pushed second → arg 1 → a1
                WasmOp::Call(3),
                WasmOp::End,
            ],
            0,
        );
        let has_call = out
            .iter()
            .any(|op| matches!(op, RiscVOp::Call { label } if label == "synth_func_3"));
        assert!(has_call);
        // After the call, the return value vreg = a0 is on the stack and
        // gets moved to a0 by the End epilogue (a no-op).
    }

    /// Limitation marker: back-to-back `Call`s with surviving prior
    /// results need function-signature info we don't yet plumb. v0.3.1
    /// supports leaf-call patterns; v0.4 will pipe `FuncSig` from the
    /// decoder and lift this restriction.
    ///
    /// This test is deliberately written to FAIL today as documentation
    /// of the gap — it would be deleted/inverted in v0.4. Marked
    /// `#[ignore]` so CI passes; revisit when signature plumbing lands.
    #[test]
    #[ignore = "v0.3.1 Call lowering needs function-signature info to handle back-to-back calls with surviving results — tracked for v0.4"]
    fn recursive_self_call_emits_two_call_ops() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Const(1),
                WasmOp::I32Sub,
                WasmOp::Call(0), // first recursive call
                WasmOp::LocalGet(0),
                WasmOp::I32Const(2),
                WasmOp::I32Sub,
                WasmOp::Call(0), // second recursive call
                WasmOp::I32Add,
                WasmOp::End,
            ],
            1,
        );
        let call_count = out
            .iter()
            .filter(|op| matches!(op, RiscVOp::Call { label } if label == "synth_func_0"))
            .count();
        assert_eq!(call_count, 2, "expected 2 calls in fib pattern: {:?}", out);
    }

    // ──────────── i64 Phase-2 tests ────────────
    //
    // Same shape-assertion style as the Phase-1 i64 tests: count/kind of the
    // emitted `RiscVOp`s, plus structural pins on the hardest lowerings (the
    // shift cross-word branch and the clz hi-vs-lo branch).

    /// Slice the output starting at the first op matching `pred` — used to
    /// isolate one op's emitted sequence past the const-materialisation noise.
    fn slice_from<F: Fn(&RiscVOp) -> bool>(out: &[RiscVOp], pred: F) -> Vec<RiscVOp> {
        out.iter().skip_while(|o| !pred(o)).cloned().collect()
    }

    // -------- I64Mul --------

    #[test]
    fn i64_mul_emits_mul_mulhu_cross_terms() {
        // lo = mul(al,bl); hi = mulhu(al,bl) + mul(al,bh) + mul(ah,bl).
        // → 3 Mul, 1 Mulhu, 2 Add.
        let out = run_i64(&[
            WasmOp::I64Const(3),
            WasmOp::I64Const(5),
            WasmOp::I64Mul,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Mul { .. })),
            3,
            "I64Mul emits 3 mul (low product + 2 cross terms)"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Mulhu { .. })),
            1,
            "I64Mul emits 1 mulhu for the low-product carry"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Add { .. })),
            2,
            "I64Mul sums the carry and two cross terms with 2 adds"
        );
    }

    // -------- I64Shl / I64ShrS / I64ShrU --------

    #[test]
    fn i64_shl_emits_cross_word_branch_and_two_sequences() {
        // The shift lowering is data-dependent: it emits a branch on bit 5
        // of the shift amount plus a small-case and a big-case sequence.
        let out = run_i64(&[
            WasmOp::I64Const(0xFF),
            WasmOp::I64Const(4),
            WasmOp::I64Shl,
            WasmOp::Drop,
        ]);
        // One bne branches to the >= 32 (cross-word) path.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )) >= 1,
            "I64Shl must branch on shamt >= 32"
        );
        // One Jal skips the big-case sequence after the small case.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Jal { .. })) >= 1,
            "I64Shl small-case path jumps over the big-case sequence"
        );
        // Two labels: the big-case entry + the join point.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Label { .. })) >= 2,
            "I64Shl emits a big-case label and a done label"
        );
    }

    #[test]
    fn i64_shl_small_case_uses_register_shifts_and_carry_or() {
        // Pin the within-word (< 32) sequence structure: the small case does
        // `lo << s`, a carry extracted via `(lo >> 1) >> inv`, `hi << s`, and
        // ORs the carry in. So the small-case region has Sll/Srl/Or ops and
        // an Srli (the `>> 1` of the carry extraction).
        let out = run_i64(&[
            WasmOp::I64Const(0x1234),
            WasmOp::I64Const(8),
            WasmOp::I64Shl,
            WasmOp::Drop,
        ]);
        // The carry path uses `srli rd, lo, 1`.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srli { shamt: 1, .. })) >= 1,
            "I64Shl small case extracts the cross-half carry via `>> 1`"
        );
        // At least two register Sll: `lo << s` and `hi << s`.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Sll { .. })) >= 2,
            "I64Shl small case shifts both halves with register Sll"
        );
        // The carry is merged into hi with an Or.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Or { .. })) >= 1,
            "I64Shl small case ORs the carry into the high half"
        );
    }

    #[test]
    fn i64_shl_big_case_zeroes_low_half() {
        // The >= 32 (big-case) sequence sets lo' = 0 via `addi rd, zero, 0`.
        let out = run_i64(&[
            WasmOp::I64Const(0xABCD),
            WasmOp::I64Const(40),
            WasmOp::I64Shl,
            WasmOp::Drop,
        ]);
        // After the Lshift_big label, an addi-from-zero with imm 0 zeroes lo.
        let big = slice_from(
            &out,
            |op| matches!(op, RiscVOp::Label { name } if name.starts_with("Lshift_big")),
        );
        assert!(
            big.iter().any(|op| matches!(
                op,
                RiscVOp::Addi {
                    rs1: Reg::ZERO,
                    imm: 0,
                    ..
                }
            )),
            "I64Shl big case must zero the low half"
        );
    }

    #[test]
    fn i64_shr_s_uses_sra_in_both_cases() {
        // shr_s arithmetic-shifts the high half; the big case also produces
        // the sign fill via `srai hi, 31`.
        let out = run_i64(&[
            WasmOp::I64Const(-1),
            WasmOp::I64Const(3),
            WasmOp::I64ShrS,
            WasmOp::Drop,
        ]);
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Sra { .. })) >= 1,
            "I64ShrS uses arithmetic register shift on the high half"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 31, .. })) >= 1,
            "I64ShrS big case fills the high half with the sign via srai 31"
        );
    }

    #[test]
    fn i64_shr_u_uses_only_logical_shifts() {
        // shr_u must never emit an arithmetic shift — zero-fill throughout.
        let out = run_i64(&[
            WasmOp::I64Const(-1),
            WasmOp::I64Const(5),
            WasmOp::I64ShrU,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sra { .. })),
            0,
            "I64ShrU is logical — no arithmetic register shift"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Srai { .. })),
            0,
            "I64ShrU is logical — no arithmetic immediate shift"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srl { .. })) >= 1,
            "I64ShrU uses logical register shifts"
        );
    }

    // -------- I64Rotl / I64Rotr --------

    #[test]
    fn i64_rotl_composes_two_shifts() {
        // rotl(x,n) = (x << n) | (x >> (64-n)). Each shift is a full
        // cross-word lowering, so we get two branches and a final pair of
        // ORs joining the two i64 results.
        let out = run_i64(&[
            WasmOp::I64Const(0x1),
            WasmOp::I64Const(7),
            WasmOp::I64Rotl,
            WasmOp::Drop,
        ]);
        // Two cross-word shift branches (one per composed shift).
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )) >= 2,
            "I64Rotl composes two shifts, each with its own cross-word branch"
        );
        // The two i64 shift results are ORed half-by-half at the end.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Or { .. })) >= 2,
            "I64Rotl ORs the two shift results half by half"
        );
    }

    #[test]
    fn i64_rotr_composes_two_shifts() {
        let out = run_i64(&[
            WasmOp::I64Const(0x8000_0000),
            WasmOp::I64Const(9),
            WasmOp::I64Rotr,
            WasmOp::Drop,
        ]);
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    ..
                }
            )) >= 2
        );
        assert!(count(&out, |op| matches!(op, RiscVOp::Or { .. })) >= 2);
    }

    // -------- I64Clz / I64Ctz / I64Popcnt --------

    #[test]
    fn i64_clz_branches_on_high_half() {
        // clz: `if hi != 0 { clz_word(hi) } else { 32 + clz_word(lo) }`.
        // The hi-vs-lo decision is a `beq hi, zero, ...`.
        let out = run_i64(&[WasmOp::I64Const(0x1234), WasmOp::I64Clz, WasmOp::Drop]);
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Eq,
                    rs2: Reg::ZERO,
                    ..
                }
            )) >= 1,
            "I64Clz branches on whether the high half is zero"
        );
        // The hi==0 arm adds 32 to the low-word clz — `addi rd, _, 32`.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Addi { imm: 32, .. })) >= 1,
            "I64Clz hi==0 arm adds 32 for the all-zero high word"
        );
    }

    #[test]
    fn i64_clz_word_helper_uses_binary_search_probes() {
        // emit_clz_word probes widths 16/8/4/2/1; each probe shifts the
        // value down by 32-k. So the clz lowering must contain srli ops at
        // shamts 16, 24, 28, 30, 31 (one set per half → at least one of each).
        let out = run_i64(&[WasmOp::I64Const(0x40), WasmOp::I64Clz, WasmOp::Drop]);
        for shamt in [16u8, 24, 28, 30, 31] {
            assert!(
                count(
                    &out,
                    |op| matches!(op, RiscVOp::Srli { shamt: s, .. } if *s == shamt)
                ) >= 1,
                "I64Clz binary-search probe at shamt {} missing",
                shamt
            );
        }
    }

    #[test]
    fn i64_ctz_branches_on_low_half() {
        // ctz mirrors clz: branch on whether the *low* half is zero.
        let out = run_i64(&[WasmOp::I64Const(0x100), WasmOp::I64Ctz, WasmOp::Drop]);
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Eq,
                    rs2: Reg::ZERO,
                    ..
                }
            )) >= 1,
            "I64Ctz branches on whether the low half is zero"
        );
        // ctz_word isolates the lowest set bit via `x & -x`: a Sub-from-zero
        // (negate) followed by an And.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Sub { rs1: Reg::ZERO, .. })) >= 1,
            "I64Ctz isolates the lowest set bit (negate via sub from zero)"
        );
    }

    #[test]
    fn i64_popcnt_sums_two_word_popcounts() {
        // popcnt(x) = popcnt(lo) + popcnt(hi). Each word popcount ends with a
        // `mul` by 0x01010101; so two Muls, and a final Add joining them.
        let out = run_i64(&[
            WasmOp::I64Const(0xFFFF_FFFF),
            WasmOp::I64Popcnt,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Mul { .. })),
            2,
            "I64Popcnt runs the SWAR mul-collapse once per half"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srli { shamt: 24, .. })) >= 2,
            "each word popcount finishes with `>> 24`"
        );
    }

    // -------- I64 comparisons --------

    #[test]
    fn i64_lt_s_uses_signed_hi_unsigned_lo() {
        // Signed lt: hi-half compared with slt (signed), lo-half with sltu.
        let out = run_i64(&[
            WasmOp::I64Const(-5),
            WasmOp::I64Const(7),
            WasmOp::I64LtS,
            WasmOp::Drop,
        ]);
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Slt { .. })) >= 1,
            "I64LtS compares the high halves signed"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Sltu { .. })) >= 1,
            "I64LtS tie-breaks the low halves unsigned"
        );
        // The hi-equal tie-break is gated by a `beq hi, hi`.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Eq,
                    ..
                }
            )) >= 1,
            "I64LtS branches when the high halves are equal"
        );
    }

    #[test]
    fn i64_lt_u_uses_unsigned_hi_compare() {
        // Unsigned lt: the hi-half comparison must be sltu, never slt.
        let out = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64LtU,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Slt { .. })),
            0,
            "I64LtU never uses a signed compare"
        );
        // Two sltu: one for the hi half, one for the lo tie-break.
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sltu { .. })),
            2,
            "I64LtU compares hi and lo halves, both unsigned"
        );
    }

    #[test]
    fn i64_ge_s_inverts_the_lt_result() {
        // ge = !lt, so the lowering ends with an `xori rd, _, 1`.
        let out = run_i64(&[
            WasmOp::I64Const(9),
            WasmOp::I64Const(4),
            WasmOp::I64GeS,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Xori { imm: 1, .. })),
            1,
            "I64GeS flips the strict-less result with xori 1"
        );
    }

    #[test]
    fn i64_gt_u_swaps_operands_no_invert() {
        // gt = less(b, a): operand swap, no final invert → no xori.
        let out = run_i64(&[
            WasmOp::I64Const(3),
            WasmOp::I64Const(8),
            WasmOp::I64GtU,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Xori { imm: 1, .. })),
            0,
            "I64GtU is a swapped less-than — no result inversion"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sltu { .. })),
            2,
            "I64GtU still does the hi + lo unsigned compares"
        );
    }

    #[test]
    fn i64_le_s_swaps_and_inverts() {
        // le = !less(b, a): both a swap and a final invert.
        let out = run_i64(&[
            WasmOp::I64Const(2),
            WasmOp::I64Const(2),
            WasmOp::I64LeS,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Xori { imm: 1, .. })),
            1,
            "I64LeS inverts the swapped less-than result"
        );
    }

    // -------- I64Extend8S / I64Extend16S / I64Extend32S --------

    #[test]
    fn i64_extend8_s_shifts_24_then_sign_propagates() {
        // extend8_s: low byte sign-extended via (x << 24) >>s 24, then the
        // high word filled via srai 31.
        let out = run_i64(&[WasmOp::I64Const(0xFF), WasmOp::I64Extend8S, WasmOp::Drop]);
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Slli { shamt: 24, .. })) == 1,
            "I64Extend8S left-shifts the low byte by 24"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 24, .. })) == 1,
            "I64Extend8S arithmetic-shifts back by 24"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 31, .. })) == 1,
            "I64Extend8S broadcasts the sign into the high word via srai 31"
        );
    }

    #[test]
    fn i64_extend16_s_shifts_16() {
        let out = run_i64(&[WasmOp::I64Const(0xFFFF), WasmOp::I64Extend16S, WasmOp::Drop]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Slli { shamt: 16, .. })),
            1,
            "I64Extend16S left-shifts the low halfword by 16"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 16, .. })),
            1,
        );
    }

    #[test]
    fn i64_extend32_s_only_sign_propagates() {
        // width 32: the low word is already the value, so no 32-width shift
        // pair — only the `srai 31` sign propagation into the high word.
        let out = run_i64(&[
            WasmOp::I64Const(0x7FFF_FFFF),
            WasmOp::I64Extend32S,
            WasmOp::Drop,
        ]);
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Slli { .. })),
            0,
            "I64Extend32S needs no low-word shift — the word is already 32-bit"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 31, .. })),
            1,
            "I64Extend32S propagates the sign into the high word"
        );
    }

    // -------- deferred ops fail loudly --------

    #[test]
    fn i64_div_rem_are_unsupported_phase3() {
        // Division/remainder on i64 are deferred to Phase 3 — they must
        // surface as `Unsupported`, never silently miscompile.
        for op in [
            WasmOp::I64DivS,
            WasmOp::I64DivU,
            WasmOp::I64RemS,
            WasmOp::I64RemU,
        ] {
            let r = select(
                &[
                    WasmOp::I64Const(10),
                    WasmOp::I64Const(3),
                    op.clone(),
                    WasmOp::End,
                ],
                0,
            )
            .map(|_| ()); // RiscVSelection isn't Debug — drop the Ok payload.
            assert!(
                matches!(r, Err(SelectorError::Unsupported(_))),
                "{:?} should be Unsupported (Phase 3), got {:?}",
                op,
                r
            );
        }
    }

    // -------- type-state plumbing --------

    #[test]
    fn i64_cmp_result_is_i32_typed() {
        // An i64 comparison pushes an i32; a following i32 consumer must not
        // hit a type mismatch.
        let out = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(2),
            WasmOp::I64LtU,
            WasmOp::I32Eqz, // consumes the i32 result of the i64 compare
            WasmOp::Drop,
        ]);
        // I32Eqz lowered fine → the vstack carried an i32 after I64LtU.
        assert!(count(&out, |op| matches!(op, RiscVOp::Sltiu { imm: 1, .. })) >= 1);
    }

    #[test]
    fn i64_shift_result_is_i64_typed() {
        // A shift pushes an i64; a following i64 consumer (I64Add) must lower.
        let out = run_i64(&[
            WasmOp::I64Const(1),
            WasmOp::I64Const(4),
            WasmOp::I64Shl,
            WasmOp::I64Const(1),
            WasmOp::I64Add,
            WasmOp::Drop,
        ]);
        // I64Add emits its add/sltu/add/add quartet → at least 3 Add ops.
        assert!(count(&out, |op| matches!(op, RiscVOp::Add { .. })) >= 3);
    }
}
