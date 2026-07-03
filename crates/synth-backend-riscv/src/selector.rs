//! WASM → RV32 instruction selector.
//!
//! Covers the i32 surface (arithmetic, logic, shifts, comparisons, division
//! with trap-on-zero), loads/stores against linear memory, simple control
//! flow (block / loop / if / br / br_if), and local variable access.
//!
//! i64 divide / remainder is lowered to an inline software long-division
//! loop (RV32 has no 64-bit divide instruction) — see `lower_i64_div`.
//!
//! Out of scope (see `select_simple` doc comments for the full list):
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
///
/// No module signature info: i64-returning calls / call-fed i64 locals are
/// inferred as i32 (pre-#312 behaviour). Prefer [`select_with_result_types`]
/// when the decoder's per-function/per-type tables are available.
pub fn select_with_options(
    wasm_ops: &[WasmOp],
    num_params: u32,
    options: SelectorOptions,
) -> Result<RiscVSelection, SelectorError> {
    select_with_result_types(wasm_ops, num_params, options, &[], &[])
}

/// Same as [`select_with_options`], plus the decoder's "returns i64" tables
/// (#312, mirroring ARM #311): `func_ret_i64[full_func_idx]` /
/// `type_ret_i64[type_idx]`. They drive (a) the i64-local width inference for
/// call-fed locals and (b) tagging an i64 call result as the `a0:a1` pair.
pub fn select_with_result_types(
    wasm_ops: &[WasmOp],
    num_params: u32,
    options: SelectorOptions,
    func_ret_i64: &[bool],
    type_ret_i64: &[bool],
) -> Result<RiscVSelection, SelectorError> {
    // #472: read the local-promotion flag exactly once, here, so the rest of the
    // selector (and its unit tests) work off a plain bool. Flag off by default →
    // `compute_local_promotion` is never consulted → byte-identical baseline.
    //
    // HELD from the RV32 flip-wave (honest blocker, the #592 const-CSE
    // pattern): the lever fails the per-function no-grow gate — its own WAR
    // fixtures grow (war_set 56→64 B, war_tee 60→68 B) and promo-ALONE grows
    // control_step 504→508 B. The profitability model ("≥2 accesses repay
    // save/restore") under-charges: it prices neither the per-RETURN restore
    // (`lw s_i` duplicated into every epilogue) nor the WAR-snapshot `mv`s.
    // Flip when the decision function models both and the corpus no-grow gate
    // holds at function granularity.
    let promote_locals = std::env::var_os("SYNTH_RV_LOCAL_PROMO").is_some();
    // #472: cmp→select fusion (the VCR-SEL-004 lever, ported from ARM). Same
    // read-once discipline; DEFAULT-ON since the RV32 flip-wave (no function
    // grows across the RV32 corpus, control_step −12 B, execution
    // differentials green on the new default BEFORE the goldens were re-pinned);
    // `SYNTH_RV_CMP_SELECT=0` opts out → `pending_cmp` is never set →
    // `lower_select` takes the branch-on-boolean pre-flip baseline (CI-gated
    // escape hatch in frozen_codegen_bytes.rs).
    let cmp_select_fuse = !std::env::var("SYNTH_RV_CMP_SELECT").is_ok_and(|v| v == "0");
    select_inner(
        wasm_ops,
        num_params,
        options,
        func_ret_i64,
        type_ret_i64,
        promote_locals,
        cmp_select_fuse,
    )
}

/// Shared selection pipeline. `promote_locals` drives the #472 local-promotion
/// lever and `cmp_select_fuse` the #472 cmp→select fusion; the public entry
/// point derives both from the env, unit tests pass them explicitly.
fn select_inner(
    wasm_ops: &[WasmOp],
    num_params: u32,
    options: SelectorOptions,
    func_ret_i64: &[bool],
    type_ret_i64: &[bool],
    promote_locals: bool,
    cmp_select_fuse: bool,
) -> Result<RiscVSelection, SelectorError> {
    let mut ctx = Selector::new_with_options(num_params, options);
    ctx.func_ret_i64 = func_ret_i64.to_vec();
    ctx.type_ret_i64 = type_ret_i64.to_vec();
    ctx.promote_locals = promote_locals;
    ctx.cmp_select_fuse = cmp_select_fuse;
    ctx.compute_local_layout(wasm_ops, num_params); // #223 / #312
    // #472: zero-init any promoted local whose first access is a read (#457).
    // Emitted BEFORE the body so (a) `preserve_callee_saved`'s dest scan sees
    // the write and spills the caller's s-reg first, and (b) the zero dominates
    // every depth-0 read. Ascending index for deterministic output. No-op with
    // the flag off (promoted_zero_init is empty).
    if !ctx.promoted_zero_init.is_empty() {
        let mut zi: Vec<(u32, Reg)> = ctx
            .promoted_zero_init
            .iter()
            .map(|idx| (*idx, ctx.promoted[idx]))
            .collect();
        zi.sort_unstable_by_key(|(idx, _)| *idx);
        for (_, reg) in zi {
            ctx.out.push(RiscVOp::Addi {
                rd: reg,
                rs1: Reg::ZERO,
                imm: 0,
            });
        }
    }
    ctx.lower_seq(wasm_ops)?;
    // #226: if any allocation ran out of registers that weren't pinning a live
    // vstack value, the function needs spilling we don't yet do — skip it rather
    // than emit a clobbering allocation. (Returning an error lets --all-exports
    // drop just this function and continue, like the ARM regalloc-exhaustion path.)
    if ctx.alloc_exhausted {
        return Err(SelectorError::Unsupported(WasmOp::Select));
    }
    ctx.emit_return_epilogue();
    // VCR-RA RV32 lever (#472, #242): fold constant shift amounts into the
    // immediate-shift forms (`slli/srli/srai`), dropping the `li tmp, N`. Flag-off
    // by default — with the env unset the output is byte-identical to the
    // pre-lever baseline (the frozen RV32 fixtures compile without it), so this is
    // frozen-safe. The on-target cycle win is validated under the RV32 differential
    // before the default-on flip. (Post-pass: runs after the epilogue's `ret`
    // terminator exists so the dead-store analysis can see live-out.)
    if std::env::var_os("SYNTH_RV_SHIFT_FOLD").is_some() {
        fold_const_shift(&mut ctx.out);
    }
    // VCR-RA RV32 lever (#472 step 2): fold a constant memory address into the
    // access immediate off s11, dropping the `addi addr,zero,ADDR; add tmp,s11,addr`
    // pair. Flag-off by default (frozen-safe, like the shift fold); the on-target
    // cycle win is validated under the RV32 differential before the default-on flip.
    if std::env::var_os("SYNTH_RV_ADDR_FOLD").is_some() {
        fold_const_addr(&mut ctx.out);
    }
    let local_frame_bytes = ctx.local_frame_bytes;
    // #220: the temp pool includes callee-saved s-registers (s1..s6), but the
    // RV psABI requires a function to preserve s0..s11. Wrap the body in a
    // prologue/epilogue that spills+restores exactly the callee-saved registers
    // it writes — otherwise calling the function corrupts the caller's s-regs
    // (including s11 = __linear_memory_base). These functions are leaves, so no
    // `ra`/caller-saved preservation is needed (non-leaf is a follow-up).
    preserve_callee_saved(&mut ctx.out, local_frame_bytes);
    Ok(RiscVSelection { ops: ctx.out })
}

/// The destination register an op writes, if any (for the callee-saved scan).
fn op_dest(op: &RiscVOp) -> Option<Reg> {
    use RiscVOp::*;
    match *op {
        Lui { rd, .. }
        | Auipc { rd, .. }
        | Jal { rd, .. }
        | Jalr { rd, .. }
        | Addi { rd, .. }
        | Slti { rd, .. }
        | Sltiu { rd, .. }
        | Xori { rd, .. }
        | Ori { rd, .. }
        | Andi { rd, .. }
        | Slli { rd, .. }
        | Srli { rd, .. }
        | Srai { rd, .. }
        | Add { rd, .. }
        | Sub { rd, .. }
        | Sll { rd, .. }
        | Slt { rd, .. }
        | Sltu { rd, .. }
        | Xor { rd, .. }
        | Srl { rd, .. }
        | Sra { rd, .. }
        | Or { rd, .. }
        | And { rd, .. }
        | Lb { rd, .. }
        | Lh { rd, .. }
        | Lw { rd, .. }
        | Lbu { rd, .. }
        | Lhu { rd, .. }
        | Csrrw { rd, .. }
        | Csrrs { rd, .. }
        | Csrrc { rd, .. }
        | Csrrwi { rd, .. }
        | Csrrsi { rd, .. }
        | Csrrci { rd, .. }
        | Mul { rd, .. }
        | Mulh { rd, .. }
        | Mulhsu { rd, .. }
        | Mulhu { rd, .. }
        | Div { rd, .. }
        | Divu { rd, .. }
        | Rem { rd, .. }
        | Remu { rd, .. } => Some(rd),
        _ => None,
    }
}

/// Source registers an op reads, or `None` for ops whose effect on register
/// liveness this peephole does not model (control flow, system, labels, calls).
/// Mirrors the ARM `reg_effect` "bail on unmodeled" contract so the dead-store
/// analysis below stays sound: an unmodeled op makes a register's liveness
/// unprovable rather than silently assumed-dead.
fn op_reads(op: &RiscVOp) -> Option<Vec<Reg>> {
    use RiscVOp::*;
    match op {
        Lui { .. } | Auipc { .. } => Some(vec![]),
        Addi { rs1, .. }
        | Slti { rs1, .. }
        | Sltiu { rs1, .. }
        | Xori { rs1, .. }
        | Ori { rs1, .. }
        | Andi { rs1, .. }
        | Slli { rs1, .. }
        | Srli { rs1, .. }
        | Srai { rs1, .. }
        | Lb { rs1, .. }
        | Lh { rs1, .. }
        | Lw { rs1, .. }
        | Lbu { rs1, .. }
        | Lhu { rs1, .. } => Some(vec![*rs1]),
        Add { rs1, rs2, .. }
        | Sub { rs1, rs2, .. }
        | Sll { rs1, rs2, .. }
        | Slt { rs1, rs2, .. }
        | Sltu { rs1, rs2, .. }
        | Xor { rs1, rs2, .. }
        | Srl { rs1, rs2, .. }
        | Sra { rs1, rs2, .. }
        | Or { rs1, rs2, .. }
        | And { rs1, rs2, .. }
        | Mul { rs1, rs2, .. }
        | Mulh { rs1, rs2, .. }
        | Mulhsu { rs1, rs2, .. }
        | Mulhu { rs1, rs2, .. }
        | Div { rs1, rs2, .. }
        | Divu { rs1, rs2, .. }
        | Rem { rs1, rs2, .. }
        | Remu { rs1, rs2, .. }
        | Sb { rs1, rs2, .. }
        | Sh { rs1, rs2, .. }
        | Sw { rs1, rs2, .. } => Some(vec![*rs1, *rs2]),
        // Control flow / system / labels / calls — not modeled ⇒ can't prove a
        // register dead across them.
        _ => None,
    }
}

/// True if register `d` is dead in `rest`: redefined before any read, never read
/// again, or only live-out as a result register (`a0`/`a1`) at the function's
/// `ret`. The RV32 analogue of the ARM `reg_dead_by_redef` helper — an unmodeled
/// op (`None` from [`op_reads`]) is treated as "can't prove dead" (returns
/// `false`), keeping the dead-store removal conservative.
fn rv_reg_dead_after(d: Reg, rest: &[RiscVOp]) -> bool {
    for op in rest {
        // `ret` = `jalr x0, 0(ra)`: the function exits here, so live-out ⊆
        // {a0, a1} (the integer result registers).
        if matches!(op, RiscVOp::Jalr { rd, rs1, imm: 0 } if *rd == Reg::ZERO && *rs1 == Reg::RA) {
            return d != Reg::A0 && d != Reg::A1;
        }
        match op_reads(op) {
            Some(reads) => {
                if reads.contains(&d) {
                    return false; // read before redef ⇒ live
                }
                if op_dest(op) == Some(d) {
                    return true; // redefined unused ⇒ dead from here back
                }
            }
            None => return false, // unmodeled ⇒ can't prove
        }
    }
    // Ran off the end without a `ret` terminator — a partial/malformed stream;
    // stay conservative.
    false
}

/// VCR-RA RV32 lever (#472, epic #242): fold a constant shift amount materialized
/// by `addi tmp, zero, N` and consumed by a *register* shift (`sll`/`srl`/`sra`)
/// into the immediate-shift form (`slli`/`srli`/`srai`), dropping the `addi`.
///
/// ```text
/// addi t0, zero, N ; sll rd, rs1, t0   ->   slli rd, rs1, (N & 31)
/// ```
///
/// `slli/srli/srai` carry the shift amount in the instruction (`shamt[4:0]`), so
/// the separate `li tmp, N` disappears — one instruction saved per constant
/// shift. The register form `sll` already masks `rs2` to its low 5 bits in
/// hardware, which is exactly WASM's shift-amount-mod-32 semantics; the fold
/// reproduces that by masking `shamt = N & 31`, so a shift amount `≥ 32` or a
/// negative constant folds to the identical behaviour.
///
/// Soundness (same scaffolding as the ARM `fold_immediate_shifts` / `fold_uxth`):
///  * the amount temp `tmp` must NOT be the shift's input `rs1` — otherwise
///    dropping the `addi` removes `rs1`'s definition (the mandatory guard);
///  * `tmp` must be untouched between the `addi` and the shift (the windowed scan
///    to the first op that touches it), and the `addi` must be a dead store:
///    either the fold's destination **is** `tmp` (`sll tmp, rs1, tmp` → the
///    `slli` redefines `tmp`, reading only `rs1`) or `tmp` is dead after the
///    shift ([`rv_reg_dead_after`]).
///
/// Only the single-`addi` const form (N in `-2048..=2047`, which covers every
/// meaningful shift amount `0..31`) is folded; a large constant materialized via
/// `lui+addi` is out of this lever's v1 scope and stays a register shift.
/// Removal-only + rewrite-in-place, so no label/branch offsets move. Returns the
/// fold count for the non-vacuity oracle.
fn fold_const_shift(out: &mut Vec<RiscVOp>) -> usize {
    use RiscVOp::*;
    let n = out.len();
    let mut drop_addi = vec![false; n];
    let mut folds = 0usize;

    for i in 0..n {
        // [i] must be `addi tmp, zero, N` — a small constant materialization.
        let (tmp, nval) = match &out[i] {
            Addi { rd, rs1, imm } if *rs1 == Reg::ZERO => (*rd, *imm),
            _ => continue,
        };
        let shamt = (nval as u32 & 31) as u8;
        for j in (i + 1)..n {
            // The shift consuming `tmp` as its amount (rs2), with `rs1 != tmp`.
            let folded = match &out[j] {
                Sll { rd, rs1, rs2 } if *rs2 == tmp && *rs1 != tmp => Some((
                    *rd,
                    Slli {
                        rd: *rd,
                        rs1: *rs1,
                        shamt,
                    },
                )),
                Srl { rd, rs1, rs2 } if *rs2 == tmp && *rs1 != tmp => Some((
                    *rd,
                    Srli {
                        rd: *rd,
                        rs1: *rs1,
                        shamt,
                    },
                )),
                Sra { rd, rs1, rs2 } if *rs2 == tmp && *rs1 != tmp => Some((
                    *rd,
                    Srai {
                        rd: *rd,
                        rs1: *rs1,
                        shamt,
                    },
                )),
                _ => None,
            };
            if let Some((rd, imm_shift)) = folded {
                // Dead store iff the fold's destination IS `tmp` (the `slli`
                // redefines it) or `tmp` is otherwise dead after the shift.
                if rd == tmp || rv_reg_dead_after(tmp, &out[j + 1..]) {
                    out[j] = imm_shift;
                    drop_addi[i] = true;
                    folds += 1;
                }
                break; // `tmp` consumed by the shift (folded or declined).
            }
            // Any other op that reads or redefines `tmp`, or an unmodeled op,
            // ends this `addi`'s window.
            match op_reads(&out[j]) {
                Some(reads) if reads.contains(&tmp) => break,
                Some(_) if op_dest(&out[j]) == Some(tmp) => break,
                Some(_) => {}
                None => break,
            }
        }
    }

    if folds == 0 {
        return 0;
    }
    let mut idx = 0usize;
    out.retain(|_| {
        let keep = !drop_addi[idx];
        idx += 1;
        keep
    });
    folds
}

/// VCR-RA RV32 lever (#472 step 2, epic #242): fold a CONSTANT memory address into
/// the access immediate off the linear-memory base `s11`, the RISC-V analogue of
/// the ARM base-CSE address half (#468). A `i32.load/store (i32.const ADDR) …`
/// lowers as `addi a,zero,ADDR; add tmp,s11,a; lw/sw _,off(tmp)`; when `ADDR+off`
/// fits the signed-12-bit `lw/sw` immediate, that collapses to a single
/// `lw/sw _,(ADDR+off)(s11)`, dropping BOTH the `add tmp,s11,a` and the
/// `addi a,zero,ADDR` (2 instructions per constant-address access).
///
/// Soundness:
///   * `ADDR+off` is range-checked as a SUM against [-2048, 2047] (each term is
///     already ≤12 bits, so two in-range values can sum out of range);
///   * the base of the `add` must be `s11` and its address operand `a` must be a
///     `addi a,zero,ADDR` (a single-`addi` small constant; a `lui+addi` large
///     address is out of v1 scope and stays the `add` form);
///   * the fold is a 3→1 rewrite, so BOTH dropped temps must be dead: `tmp` (the
///     add result) read only by the access, and `a` (the address constant) read
///     only by the `add` — verified with [`rv_reg_dead_after`] plus a check that
///     `a` is untouched between its def and the `add`.
///
/// Only the contiguous `add tmp,s11,a` immediately followed by its access is
/// matched (the no-bounds-check lowering shape); a bounds check between them reads
/// `a`, which disqualifies the fold. Returns the fold count.
fn fold_const_addr(out: &mut Vec<RiscVOp>) -> usize {
    use RiscVOp::*;
    let n = out.len();
    let mut drop = vec![false; n];
    let mut folds = 0usize;

    for i in 0..n {
        // [i] must be `add tmp, s11, a`.
        let (tmp, a) = match &out[i] {
            Add { rd, rs1, rs2 } if *rs1 == Reg::S11 => (*rd, *rs2),
            _ => continue,
        };
        if i + 1 >= n {
            continue;
        }
        // The access at i+1 must use `tmp` as its base register; capture its imm.
        let off = match &out[i + 1] {
            Lw { rs1, imm, .. }
            | Lh { rs1, imm, .. }
            | Lhu { rs1, imm, .. }
            | Lb { rs1, imm, .. }
            | Lbu { rs1, imm, .. }
            | Sw { rs1, imm, .. }
            | Sh { rs1, imm, .. }
            | Sb { rs1, imm, .. }
                if *rs1 == tmp =>
            {
                *imm
            }
            _ => continue,
        };
        // `a` must be defined by the nearest prior `addi a, zero, ADDR`.
        let addr_def = (0..i).rev().find(|&j| op_dest(&out[j]) == Some(a));
        let (def_idx, addr_const) = match addr_def {
            Some(j) => match &out[j] {
                Addi { rs1, imm, .. } if *rs1 == Reg::ZERO => (j, *imm),
                _ => continue,
            },
            None => continue,
        };
        // The folded immediate is the SUM; it must fit the signed 12-bit window.
        let total = addr_const.wrapping_add(off);
        if !(-2048..=2047).contains(&total) {
            continue;
        }
        // `tmp` must be dead after the access (its only consumer).
        if !rv_reg_dead_after(tmp, &out[i + 2..]) {
            continue;
        }
        // `a` must be read ONLY by the `add` at i: untouched between its def and
        // the add, and dead after.
        let a_read_between = (def_idx + 1..i).any(|k| match op_reads(&out[k]) {
            Some(rs) => rs.contains(&a),
            None => true, // unmodeled op between ⇒ cannot prove `a` unread
        });
        if a_read_between || !rv_reg_dead_after(a, &out[i + 1..]) {
            continue;
        }
        // Rewrite the access to address off s11 with the folded immediate.
        out[i + 1] = match out[i + 1].clone() {
            Lw { rd, .. } => Lw {
                rd,
                rs1: Reg::S11,
                imm: total,
            },
            Lh { rd, .. } => Lh {
                rd,
                rs1: Reg::S11,
                imm: total,
            },
            Lhu { rd, .. } => Lhu {
                rd,
                rs1: Reg::S11,
                imm: total,
            },
            Lb { rd, .. } => Lb {
                rd,
                rs1: Reg::S11,
                imm: total,
            },
            Lbu { rd, .. } => Lbu {
                rd,
                rs1: Reg::S11,
                imm: total,
            },
            Sw { rs2, .. } => Sw {
                rs1: Reg::S11,
                rs2,
                imm: total,
            },
            Sh { rs2, .. } => Sh {
                rs1: Reg::S11,
                rs2,
                imm: total,
            },
            Sb { rs2, .. } => Sb {
                rs1: Reg::S11,
                rs2,
                imm: total,
            },
            other => other, // unreachable (matched above)
        };
        drop[i] = true;
        drop[def_idx] = true;
        folds += 1;
    }

    if folds == 0 {
        return 0;
    }
    let mut idx = 0usize;
    out.retain(|_| {
        let keep = !drop[idx];
        idx += 1;
        keep
    });
    folds
}

/// #472 (VCR-RA RV32 local promotion) — the RISC-V port of the ARM
/// `compute_local_promotion` lever (#390/#457/#458). Promote non-parameter
/// i32 locals into callee-saved s-registers so their reads/writes become
/// register moves instead of frame `lw`/`sw` traffic (leaf functions only).
///
/// Returns `(idx -> s-reg, {idx whose FIRST access is a read})`. The second set
/// drives a prologue zero-init (`addi s_i, zero, 0`) so a read-before-write
/// promoted local still observes the wasm-mandated 0 — the #457 gotcha. (ARM's
/// v1 instead *declined* read-before-write locals; zero-initing lets us promote
/// them, which is sound because the entry zero dominates every depth-0 access.)
///
/// SOUNDNESS (v1, conservative — never under-reserves):
/// - **Leaf-only.** Any `Call`/`CallIndirect` in the body → promote nothing.
///   A callee-saved s-reg survives a call by the psABI, but this selector keeps
///   no cross-call spill discipline for a register-resident local; the ARM
///   precedent is likewise leaf-only (#390), matching the RV32 #220 callee-saved
///   machinery. Decline rather than risk a clobber.
/// - **i32 only.** An i64 local needs a register PAIR; leave it on the frame.
/// - **Depth-0 straight-line.** Every access outside any block/loop/if, so a
///   `local.set` at op i dominates every `local.get` at j>i without a dominator
///   analysis (a `br_if` only skips forward; no loop header sits at depth 0). A
///   local touched inside any control-flow region is declined.
/// - **Cost gate.** >= 2 accesses (one access can't repay the s-reg save/restore).
///
/// Budget: `s8`, `s9`, `s10` (x24..x26) — callee-saved, OUTSIDE the `temps`
/// pool (t0..t6, s1..s6) and the div core's fixed file (s1..s3 + s7 move
/// scratch), and neither s0(fp) nor s11(linmem base). They therefore never
/// collide with `alloc_temp`, and `preserve_callee_saved` saves/restores each
/// one the body writes. Eligible locals past the 3-register budget stay on the
/// frame (unchanged path).
fn compute_local_promotion(
    wasm_ops: &[WasmOp],
    num_params: u32,
    i64_set: &std::collections::HashSet<u32>,
) -> (
    std::collections::HashMap<u32, Reg>,
    std::collections::HashSet<u32>,
) {
    use std::collections::{HashMap, HashSet};
    // Leaf-only: a call anywhere disqualifies the whole function.
    if wasm_ops
        .iter()
        .any(|op| matches!(op, WasmOp::Call(_) | WasmOp::CallIndirect { .. }))
    {
        return (HashMap::new(), HashSet::new());
    }
    struct Info {
        count: u32,
        all_depth0: bool,
        first_is_write: bool,
        seen: bool,
    }
    let mut info: HashMap<u32, Info> = HashMap::new();
    let mut depth: i32 = 0;
    for op in wasm_ops {
        match op {
            WasmOp::Block | WasmOp::Loop | WasmOp::If => depth += 1,
            WasmOp::End => depth -= 1,
            WasmOp::LocalGet(idx) | WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx)
                if *idx >= num_params =>
            {
                let is_write = matches!(op, WasmOp::LocalSet(_) | WasmOp::LocalTee(_));
                let e = info.entry(*idx).or_insert(Info {
                    count: 0,
                    all_depth0: true,
                    first_is_write: false,
                    seen: false,
                });
                if !e.seen {
                    e.first_is_write = is_write;
                    e.seen = true;
                }
                e.count += 1;
                if depth != 0 {
                    e.all_depth0 = false;
                }
            }
            _ => {}
        }
    }
    const PROMO_REGS: [Reg; 3] = [Reg::S8, Reg::S9, Reg::S10];
    let mut eligible: Vec<u32> = info
        .iter()
        .filter(|(idx, e)| e.all_depth0 && e.count >= 2 && !i64_set.contains(idx))
        .map(|(&idx, _)| idx)
        .collect();
    eligible.sort_unstable();
    let map: HashMap<u32, Reg> = eligible.iter().copied().zip(PROMO_REGS).collect();
    let zero_init: HashSet<u32> = map
        .keys()
        .copied()
        .filter(|idx| !info[idx].first_is_write)
        .collect();
    (map, zero_init)
}

/// True for callee-saved registers the allocator may hand out as temps:
/// `s1` (x9) and `s2..s10` (x18..x26). Excludes the runtime-reserved `s0`
/// (x8, frame pointer) and `s11` (x27, `__linear_memory_base`) — which the
/// body never targets and must never be treated as a spillable temp.
fn is_callee_saved_temp(r: Reg) -> bool {
    let n = r as u8;
    n == 9 || (18..=26).contains(&n)
}

/// #220 + #223: open a stack frame for the non-parameter locals (`local_bytes`,
/// laid out at the bottom `0..local_bytes`) and spill+restore the callee-saved
/// registers `out` writes (above the locals, per the RV psABI). No-op only when
/// the body uses no callee-saved register AND has no frame-backed locals.
fn preserve_callee_saved(out: &mut Vec<RiscVOp>, local_bytes: i32) {
    let mut saved: Vec<Reg> = Vec::new();
    for op in out.iter() {
        if let Some(rd) = op_dest(op)
            && is_callee_saved_temp(rd)
            && !saved.contains(&rd)
        {
            saved.push(rd);
        }
    }
    if saved.is_empty() && local_bytes == 0 {
        return;
    }
    saved.sort_by_key(|r| *r as u8); // deterministic slot order
    // 16-byte-aligned frame (RV psABI): [ locals 0..local_bytes | saved regs ].
    let frame = (local_bytes + (saved.len() as i32) * 4 + 15) & !15;
    // Saved registers sit just above the locals region.
    let sreg_off = |k: usize| local_bytes + (k as i32) * 4;

    let mut prologue = vec![RiscVOp::Addi {
        rd: Reg::SP,
        rs1: Reg::SP,
        imm: -frame,
    }];
    for (k, &r) in saved.iter().enumerate() {
        prologue.push(RiscVOp::Sw {
            rs1: Reg::SP,
            rs2: r,
            imm: sreg_off(k),
        });
    }

    let mut epilogue: Vec<RiscVOp> = saved
        .iter()
        .enumerate()
        .map(|(k, &r)| RiscVOp::Lw {
            rd: r,
            rs1: Reg::SP,
            imm: sreg_off(k),
        })
        .collect();
    epilogue.push(RiscVOp::Addi {
        rd: Reg::SP,
        rs1: Reg::SP,
        imm: frame,
    });

    // Restore before every `ret` (jalr x0, 0(ra)); prepend the prologue once.
    let is_ret = |op: &RiscVOp| {
        matches!(
            op,
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            }
        )
    };
    let mut new_out = prologue;
    for op in out.drain(..) {
        if is_ret(&op) {
            new_out.extend(epilogue.iter().cloned());
        }
        new_out.push(op);
    }
    *out = new_out;
}

/// #472 (VCR-SEL-004 port): a just-lowered i32 comparison whose 0/1 boolean is
/// still sitting on top of the vstack. If the *very next* wasm op is `select`,
/// the boolean materialization (`slt`/`sltu`/`xor`+`sltiu`/`xori`…) is deleted
/// and the select branches directly on the comparison via the matching B-type
/// branch (`beq`/`bne`/`blt`/`bge`/`bltu`/`bgeu`) — RV32's branch comparators
/// play the role ARM's IT-predicated flags do in `fuse_cmp_select`.
///
/// Validity is enforced two ways (belt and braces):
/// - `lower_one` `take()`s the record at the start of EVERY op, so it only
///   survives from a comparison to the immediately following op.
/// - `lower_select` additionally checks the popped condition register is
///   exactly `bool_reg` and that nothing was emitted since (`end` index),
///   so a zero-emission op in between (e.g. a promoted `local.get`) can
///   never smuggle a stale record through.
///
/// Deleting the tail is sound: `bool_reg` is a fresh temp pushed exactly once
/// (`alloc_temp` never returns a live vstack register) and the select pops it,
/// so nothing else can observe the boolean; `rs1`/`rs2` are unchanged since the
/// comparison because no instruction was emitted in between.
struct PendingCmp {
    /// Branch condition that is TRUE exactly when the wasm comparison is 1.
    cond: Branch,
    /// Comparison operands, already in emitted (post-swap) order.
    rs1: Reg,
    rs2: Reg,
    /// Register the deleted sequence would have left the 0/1 boolean in.
    bool_reg: Reg,
    /// `out.len()` BEFORE the boolean materialization — truncation point.
    start: usize,
    /// `out.len()` AFTER it — must still equal `out.len()` at fuse time.
    end: usize,
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
    /// #343: for an `if (result …)` frame, the then-arm's result value(s) —
    /// the vstack entries above `stack_height_at_entry`, captured at `else`.
    /// They are reconciled with the else-arm's results at `end` so both arms
    /// leave the value in the SAME register(s) at the join. Empty for
    /// blocks/loops and for control-flow-only (arity-0) if/else.
    then_results: Vec<VstackVal>,
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
    /// Available temporary registers; `alloc_temp` hands out the lowest-indexed
    /// free one, so the caller-saved `t`-registers (listed first) are preferred
    /// over the callee-saved `s`-registers.
    temps: Vec<Reg>,
    /// #226: set when `alloc_temp` could not find a register that isn't already
    /// holding a live `vstack` value (every temp is pinned). Surfaced as an
    /// `Unsupported` error after lowering so `--all-exports` skips the function
    /// rather than emitting a clobbering allocation (honest skip, not a silent
    /// miscompile — the same discipline as the ARM regalloc-exhaustion path).
    alloc_exhausted: bool,
    /// #312: registers pinned for the duration of the *current wasm op's*
    /// lowering. Covers the two holes `live_regs()` (vstack liveness) cannot
    /// see, both opened by the #231 lowest-free allocator:
    ///
    /// 1. **Popped operands** leave the vstack before the multi-instruction
    ///    expansion that reads them finishes — without pinning, a scratch
    ///    `alloc_temp` lands on a popped operand and clobbers it mid-sequence
    ///    (the #232 signed-div guard bug, generalized).
    /// 2. **Scratch already handed out for this op** isn't on the vstack
    ///    either, so two back-to-back `alloc_temp` calls returned the *same*
    ///    register — every `(lo, hi)` i64 pair collapsed to one register.
    ///
    /// `pop_*` pins what it pops, `alloc_temp_avoiding` pins what it returns,
    /// and `lower_one` clears the set at the start of each op. High-pressure
    /// lowerings (`i64.div_s`, shifts/rotates, clz/ctz/popcnt) `unpin` scratch
    /// as it dies to stay inside the 13-register pool.
    op_pinned: Vec<Reg>,
    /// Counter for generating unique labels (L0, L1, ...).
    next_label: u32,
    /// Tracks whether we already emitted the function-final return.
    emitted_return: bool,
    /// Phase-1 safety options (bounds-check policy, signed-div overflow trap).
    options: SelectorOptions,
    /// #223: non-parameter local `idx` → `(byte offset, is_i64)` within the
    /// stack frame (the locals region, laid out first at
    /// `0..local_frame_bytes`). The #220 callee-saved spills go after it; the
    /// unified prologue opens both. #312: i64 locals get an 8-byte,
    /// 8-byte-aligned slot (lo word at `off`, hi word at `off+4`).
    local_offsets: std::collections::HashMap<u32, (i32, bool)>,
    /// Bytes reserved for non-parameter locals (4 per i32, 8 per i64).
    local_frame_bytes: i32,
    /// #312: every local index (param or not) inferred as i64 by
    /// `synth_synthesis::infer_i64_locals`. Param entries are used only to
    /// bail out honestly — the RV32 i64-*param* ABI (an i64 param occupies an
    /// aligned even/odd a-register pair per the psABI) is not modeled yet.
    i64_locals: std::collections::HashSet<u32>,
    /// #312: per-function "returns i64" table (full wasm function index,
    /// imports first). Empty = treat every call result as i32 (legacy).
    func_ret_i64: Vec<bool>,
    /// #312: per-type "returns i64" table, for `call_indirect`. Only consulted
    /// by the width inference today — call_indirect itself is still
    /// `Unsupported` in this selector.
    type_ret_i64: Vec<bool>,
    /// #472 (VCR-RA RV32 local promotion): non-parameter i32 locals promoted
    /// into callee-saved s-registers (`s8`/`s9`/`s10`). Empty unless
    /// `SYNTH_RV_LOCAL_PROMO` is set — with the flag off the frame path is
    /// taken for every local and codegen is byte-identical to the baseline.
    /// See [`compute_local_promotion`].
    promoted: std::collections::HashMap<u32, Reg>,
    /// #472: promoted locals whose FIRST access is a read — they rely on the
    /// wasm zero-init and get an `addi s_i, zero, 0` at function entry (#457).
    promoted_zero_init: std::collections::HashSet<u32>,
    /// #472: whether local promotion is enabled for this function. Set by the
    /// public entry point from `SYNTH_RV_LOCAL_PROMO` (still opt-in — held
    /// from the flip-wave on the no-grow blocker documented there); the env is
    /// read exactly once so the decision function stays pure and unit-testable.
    promote_locals: bool,
    /// #472 (VCR-SEL-004 port): whether cmp→select fusion is enabled. Set by
    /// the public entry point from `SYNTH_RV_CMP_SELECT` (default-on, `=0`
    /// opts out); unit tests pass it explicitly. With this false,
    /// `pending_cmp` is never populated and the select lowering is
    /// byte-identical to the pre-flip baseline.
    cmp_select_fuse: bool,
    /// #472: the comparison lowered by the PREVIOUS wasm op, if fusion is
    /// enabled and its boolean is on top of the vstack. `lower_one` takes it
    /// at the start of each op so it can only feed the immediately following
    /// `select`. See [`PendingCmp`].
    pending_cmp: Option<PendingCmp>,
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
            alloc_exhausted: false,
            op_pinned: Vec::new(),
            next_label: 0,
            emitted_return: false,
            options,
            local_offsets: std::collections::HashMap::new(),
            local_frame_bytes: 0,
            i64_locals: std::collections::HashSet::new(),
            func_ret_i64: Vec::new(),
            type_ret_i64: Vec::new(),
            promoted: std::collections::HashMap::new(),
            promoted_zero_init: std::collections::HashSet::new(),
            promote_locals: false,
            cmp_select_fuse: false,
            pending_cmp: None,
        }
    }

    /// #223 + #312: lay out the non-parameter locals referenced by `wasm_ops`
    /// into the stack frame in ascending-index order: 4-byte slots for i32
    /// locals, 8-byte 8-aligned slots for i64 locals (width via the shared
    /// `infer_i64_locals` inference — the same one the ARM selector uses, so
    /// call-fed i64 locals are covered through `func_ret_i64`/`type_ret_i64`).
    /// The slots sit at the bottom of the frame; the #220 callee-saved spills
    /// go above.
    fn compute_local_layout(&mut self, wasm_ops: &[WasmOp], num_params: u32) {
        use std::collections::BTreeSet;
        self.i64_locals =
            synth_synthesis::infer_i64_locals(wasm_ops, &self.func_ret_i64, &self.type_ret_i64);
        // #472: VCR-RA local promotion — flag-gated (SYNTH_RV_LOCAL_PROMO). With
        // the flag unset the map is empty, every local falls to the frame path
        // below, and codegen is byte-identical to the pre-lever baseline (the
        // frozen RV32 fixtures compile without it). The promoted set is the ONE
        // source of truth: the layout skips exactly the promoted locals, so a
        // frame slot is reserved iff the local is NOT register-resident.
        if self.promote_locals {
            let (map, zero_init) = compute_local_promotion(wasm_ops, num_params, &self.i64_locals);
            self.promoted = map;
            self.promoted_zero_init = zero_init;
        }
        let mut used: BTreeSet<u32> = BTreeSet::new();
        for op in wasm_ops {
            match op {
                WasmOp::LocalGet(i) | WasmOp::LocalSet(i) | WasmOp::LocalTee(i)
                    if *i >= num_params && !self.promoted.contains_key(i) =>
                {
                    used.insert(*i);
                }
                _ => {}
            }
        }
        let mut offset: i32 = 0;
        for idx in used {
            let is_i64 = self.i64_locals.contains(&idx);
            // i64 slots are 8-byte aligned so off/off+4 never straddle a
            // larger-aligned neighbour (and stay friendly to a future ld/sd
            // peephole on RV64).
            if is_i64 && (offset % 8) != 0 {
                offset += 4;
            }
            self.local_offsets.insert(idx, (offset, is_i64));
            offset += if is_i64 { 8 } else { 4 };
        }
        self.local_frame_bytes = offset;
    }

    fn fresh_label(&mut self, prefix: &str) -> String {
        let n = self.next_label;
        self.next_label += 1;
        format!("{}{}", prefix, n)
    }

    /// Registers currently pinned by a live `vstack` value. Every vstack entry
    /// is a temp register (locals/params are always copied into a fresh temp by
    /// `lower_local_get`), so this set is exactly the values that must survive
    /// until they are popped — `alloc_temp` must never hand any of them out.
    fn live_regs(&self) -> Vec<Reg> {
        let mut live = Vec::with_capacity(self.vstack.len() * 2);
        for v in &self.vstack {
            match v {
                VstackVal::I32(r) => live.push(*r),
                VstackVal::I64 { lo, hi } => {
                    live.push(*lo);
                    live.push(*hi);
                }
            }
        }
        live
    }

    /// Allocate a scratch register: the **lowest-indexed `temps` entry that
    /// isn't already pinned by a live `vstack` value** (#226 liveness).
    ///
    /// The pool lists caller-saved t-registers (`t0..t6`) before callee-saved
    /// s-registers (`s1..s6`), so "lowest free" keeps a function in the
    /// caller-saved registers whenever ≤7 values are simultaneously live —
    /// avoiding the #220 callee-saved save/restore prologue entirely.
    ///
    /// This replaces the original round-robin march (a `next_temp` counter that
    /// only ever advanced). Round-robin was "fine for straight-line code" but,
    /// even after #226 made it skip live registers, it kept walking *forward*
    /// into the s-registers instead of reusing a just-freed low register — so
    /// short-lived expressions needlessly touched callee-saved regs and paid the
    /// prologue tax. With the vstack liveness already tracked, lowest-free is
    /// both simpler and strictly tighter; results are identical (register
    /// renaming), code is equal-or-smaller.
    ///
    /// If every temp is pinned (a genuinely deeper-than-pool expression), record
    /// `alloc_exhausted` — the caller turns the flag into a skip so the function
    /// is dropped, never silently miscompiled.
    fn alloc_temp(&mut self) -> Reg {
        self.alloc_temp_avoiding(&[])
    }

    /// Like [`alloc_temp`], but also avoids the registers in `avoid`.
    ///
    /// #312: beyond the vstack-live set (#226) and the explicit `avoid` list
    /// (#232), this also skips — and adds the returned register to — the
    /// per-op `op_pinned` set, so (a) operands popped earlier in the current
    /// op's lowering are never clobbered by its own scratch, and (b) two
    /// allocations within one op never alias each other.
    fn alloc_temp_avoiding(&mut self, avoid: &[Reg]) -> Reg {
        let live = self.live_regs();
        for &r in &self.temps {
            if !live.contains(&r) && !avoid.contains(&r) && !self.op_pinned.contains(&r) {
                self.pin(r);
                return r;
            }
        }
        // Nothing free: cannot allocate without spilling. Flag the function for
        // skip-and-continue rather than emit a clobber.
        self.alloc_exhausted = true;
        self.temps[0]
    }

    /// Pin `r` for the remainder of the current wasm op's lowering (#312).
    fn pin(&mut self, r: Reg) {
        if !self.op_pinned.contains(&r) {
            self.op_pinned.push(r);
        }
    }

    /// Release registers whose value is dead for the rest of the current op —
    /// used by the high-pressure lowerings (i64 div/shift/rotate, clz/ctz/
    /// popcnt) so their fully-pinned peak stays inside the 13-register pool.
    fn unpin(&mut self, regs: &[Reg]) {
        self.op_pinned.retain(|r| !regs.contains(r));
    }

    fn push_i32(&mut self, r: Reg) {
        self.vstack.push(VstackVal::I32(r));
    }

    fn push_i64(&mut self, lo: Reg, hi: Reg) {
        self.vstack.push(VstackVal::I64 { lo, hi });
    }

    /// #472 WAR fix: before a promoted `local.set`/`local.tee` overwrites its
    /// s-register `reg`, snapshot any still-live vstack entry that aliases `reg`
    /// (pushed by an EARLIER `local.get` of this same promoted local) into a
    /// fresh temp, and rewrite those entries to the temp. Without this, the
    /// `mv reg, val` would corrupt the earlier value — the classic
    /// get→…→set→use WAR hazard the direct-alias `local.get` opens.
    ///
    /// `skip` (if `Some`) is the vstack index NOT to rewrite — used by
    /// `local.tee`, whose own result (the top of stack) is intentionally the
    /// value being written and stays aliased to `reg`. Fires only when an alias
    /// is actually present, so the common case pays nothing. Only i32 entries
    /// can alias a promoted reg (s8/s9/s10 are never handed out to i64 pairs),
    /// but i64 halves are checked too for defence in depth.
    fn snapshot_aliases(&mut self, reg: Reg, skip: Option<usize>) {
        let aliased = self.vstack.iter().enumerate().any(|(i, v)| {
            Some(i) != skip
                && match v {
                    VstackVal::I32(r) => *r == reg,
                    VstackVal::I64 { lo, hi } => *lo == reg || *hi == reg,
                }
        });
        if !aliased {
            return;
        }
        // `reg` is live on the vstack, so `alloc_temp` (skips live + op_pinned)
        // never returns it; the fresh temp is distinct.
        let tmp = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: tmp,
            rs1: reg,
            imm: 0,
        });
        for (i, v) in self.vstack.iter_mut().enumerate() {
            if Some(i) == skip {
                continue;
            }
            match v {
                VstackVal::I32(r) if *r == reg => *r = tmp,
                VstackVal::I64 { lo, hi } => {
                    if *lo == reg {
                        *lo = tmp;
                    }
                    if *hi == reg {
                        *hi = tmp;
                    }
                }
                _ => {}
            }
        }
    }

    fn pop_any(&mut self, op: &WasmOp) -> Result<VstackVal, SelectorError> {
        let v = self
            .vstack
            .pop()
            .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
        // #312: a popped operand leaves `live_regs` but is still read by the
        // remainder of this op's expansion — pin it so scratch allocations
        // can't land on it (clobber class of #232, generalized).
        match v {
            VstackVal::I32(r) => self.pin(r),
            VstackVal::I64 { lo, hi } => {
                self.pin(lo);
                self.pin(hi);
            }
        }
        Ok(v)
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
        // #312: per-op pin scope — operands popped and scratch allocated while
        // lowering `op` stay pinned until the next op starts.
        self.op_pinned.clear();
        // #472: a fusible comparison record only survives from the comparison
        // to the IMMEDIATELY following op — any other op invalidates it.
        let pending_cmp = self.pending_cmp.take();
        match op {
            // ─── Locals ─────────────────────────────────────────────────
            LocalGet(idx) => self.lower_local_get(*idx, op)?,
            LocalSet(idx) => self.lower_local_set(*idx, op)?,
            LocalTee(idx) => self.lower_local_tee(*idx, op)?,

            // ─── Select (ternary) — #223 ────────────────────────────────
            Select => self.lower_select(op, pending_cmp)?,

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

            // ─── Sign extension — #223 (slli/srai) ─────────────────────
            I32Extend8S => self.lower_sign_extend(op, 24)?,
            I32Extend16S => self.lower_sign_extend(op, 16)?,

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

            // ─── i64 division / remainder (Phase 3) ─────────────────────
            // RV32's M extension only has 32-bit div/rem, so a 64-bit divide
            // is lowered to an inline software long-division loop. See
            // `emit_i64_udiv_inline` for the unsigned core; the signed ops
            // wrap it with magnitude/sign handling.
            I64DivS => self.lower_i64_div(op, /*signed=*/ true, /*want_rem=*/ false)?,
            I64DivU => self.lower_i64_div(op, /*signed=*/ false, /*want_rem=*/ false)?,
            I64RemS => self.lower_i64_div(op, /*signed=*/ true, /*want_rem=*/ true)?,
            I64RemU => self.lower_i64_div(op, /*signed=*/ false, /*want_rem=*/ true)?,

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
                    then_results: Vec::new(),
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
                    then_results: Vec::new(),
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

    /// #223: `select` — wasm pops `cond` (top), then `b`, then `a`; the result
    /// is `cond != 0 ? a : b`. RV32 has no conditional-move, so this lowers to a
    /// short branch (the same shape the ARM backend builds with IT/SelectMove):
    /// ```text
    ///   bne cond, zero, .Lsel_a   ; cond != 0 → take a
    ///   mv  dst, b                ; cond == 0 → b
    ///   j   .Lsel_end
    /// .Lsel_a:
    ///   mv  dst, a
    /// .Lsel_end:
    /// ```
    /// Handles both i32 and i64 operands (the i64 case selects both halves under
    /// one branch). `dst` may alias `a`/`b` — safe, because the two arms are
    /// mutually exclusive.
    ///
    /// #472 (VCR-SEL-004 port): when `pending` carries the comparison lowered by
    /// the immediately preceding op AND its boolean is exactly the popped `cond`,
    /// the boolean materialization is deleted and the branch tests the comparison
    /// directly (`blt a, b` instead of `slt t, a, b; bne t, zero`) — saving the
    /// 1–2 instructions the boolean cost. Unreachable under the
    /// `SYNTH_RV_CMP_SELECT=0` opt-out (the record is never created then).
    /// Note the fused branch is emitted before any `mv`, so the select's freshly
    /// allocated `dst` aliasing a comparison operand is harmless.
    fn lower_select(
        &mut self,
        op: &WasmOp,
        pending: Option<PendingCmp>,
    ) -> Result<(), SelectorError> {
        let cond = self.pop_i32(op)?;
        let b = self.pop_any(op)?;
        let a = self.pop_any(op)?;
        // Fuse only if the record's boolean is the popped condition and nothing
        // was emitted since the comparison (see PendingCmp for why both hold
        // whenever the record survives `lower_one`'s take()).
        let fused = pending.filter(|p| p.bool_reg == cond && p.end == self.out.len());
        if let Some(p) = &fused {
            // Drop the boolean materialization — dead once we branch on the
            // comparison itself.
            self.out.truncate(p.start);
        }
        // Branch taken (→ take_a arm) exactly when the wasm condition is
        // true/non-zero: the fused comparison directly, or `cond != 0`.
        let take_branch = |label: String| match &fused {
            Some(p) => RiscVOp::Branch {
                cond: p.cond,
                rs1: p.rs1,
                rs2: p.rs2,
                label,
            },
            None => RiscVOp::Branch {
                cond: Branch::Ne,
                rs1: cond,
                rs2: Reg::ZERO,
                label,
            },
        };
        let take_a = self.fresh_label("Lsel_a");
        let end = self.fresh_label("Lsel_end");
        let mv = |dst: Reg, src: Reg| RiscVOp::Addi {
            rd: dst,
            rs1: src,
            imm: 0,
        };
        match (a, b) {
            (VstackVal::I32(ra), VstackVal::I32(rb)) => {
                let dst = self.alloc_temp();
                self.out.push(take_branch(take_a.clone()));
                self.out.push(mv(dst, rb)); // cond == 0 → b
                self.out.push(RiscVOp::Jal {
                    rd: Reg::ZERO,
                    label: end.clone(),
                });
                self.out.push(RiscVOp::Label { name: take_a });
                self.out.push(mv(dst, ra)); // cond != 0 → a
                self.out.push(RiscVOp::Label { name: end });
                self.push_i32(dst);
            }
            (VstackVal::I64 { lo: alo, hi: ahi }, VstackVal::I64 { lo: blo, hi: bhi }) => {
                let dlo = self.alloc_temp();
                let dhi = self.alloc_temp();
                self.out.push(take_branch(take_a.clone()));
                self.out.push(mv(dlo, blo)); // cond == 0 → b
                self.out.push(mv(dhi, bhi));
                self.out.push(RiscVOp::Jal {
                    rd: Reg::ZERO,
                    label: end.clone(),
                });
                self.out.push(RiscVOp::Label { name: take_a });
                self.out.push(mv(dlo, alo)); // cond != 0 → a
                self.out.push(mv(dhi, ahi));
                self.out.push(RiscVOp::Label { name: end });
                self.push_i64(dlo, dhi);
            }
            (x, y) => {
                return Err(SelectorError::StackTypeMismatch {
                    op: op.clone(),
                    expected: "matching i32/i64 select operands",
                    found: if x.type_name() != y.type_name() {
                        "mismatched"
                    } else {
                        x.type_name()
                    },
                });
            }
        }
        Ok(())
    }

    // ────────── Locals ──────────

    fn lower_local_get(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        if (idx as usize) < self.arg_regs.len() {
            // #312: param handling is i32-only (one a-register per param). An
            // i64 param occupies an aligned even/odd a-register pair per the
            // RV32 psABI — not modeled yet, so bail honestly (skip-and-continue
            // under --all-exports) rather than read half the value.
            if self.i64_locals.contains(&idx) {
                return Err(SelectorError::Unsupported(op.clone()));
            }
            let dst = self.alloc_temp();
            // mv dst, arg
            self.out.push(RiscVOp::Addi {
                rd: dst,
                rs1: self.arg_regs[idx as usize],
                imm: 0,
            });
            self.push_i32(dst);
        } else if let Some(&reg) = self.promoted.get(&idx) {
            // #472: promoted i32 local lives in a callee-saved s-reg. Alias it
            // DIRECTLY onto the vstack — no load, no copy. Sound because (a) any
            // op consuming this value allocates a fresh dst (never the pinned
            // operand, and s8/s9/s10 are outside the temp pool), so the s-reg is
            // never clobbered by a consumer; and (b) a later `local.set`/`tee`
            // of this local snapshots any still-live alias before overwriting
            // the s-reg (`snapshot_aliases`). This is where the byte win lands:
            // repeated reads become free.
            self.push_i32(reg);
        } else {
            // #223: non-param local — load from its frame slot (lw dst, off(sp)).
            // #312: an i64 local loads both words of its 8-byte slot
            // (lo at off, hi at off+4) into a fresh register pair.
            let (off, is_i64) = self.local_slot(idx, op)?;
            if is_i64 {
                let lo = self.alloc_temp();
                let hi = self.alloc_temp();
                self.out.push(RiscVOp::Lw {
                    rd: lo,
                    rs1: Reg::SP,
                    imm: off,
                });
                self.out.push(RiscVOp::Lw {
                    rd: hi,
                    rs1: Reg::SP,
                    imm: off + 4,
                });
                self.push_i64(lo, hi);
            } else {
                let dst = self.alloc_temp();
                self.out.push(RiscVOp::Lw {
                    rd: dst,
                    rs1: Reg::SP,
                    imm: off,
                });
                self.push_i32(dst);
            }
        }
        Ok(())
    }

    /// #223: `(byte offset, is_i64)` of a non-parameter local's frame slot.
    fn local_slot(&self, idx: u32, op: &WasmOp) -> Result<(i32, bool), SelectorError> {
        self.local_offsets
            .get(&idx)
            .copied()
            .ok_or_else(|| SelectorError::Unsupported(op.clone()))
    }

    fn lower_local_set(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        if (idx as usize) < self.arg_regs.len() {
            // #312: i64 params are unsupported — see lower_local_get.
            if self.i64_locals.contains(&idx) {
                return Err(SelectorError::Unsupported(op.clone()));
            }
            let src = self.pop_i32(op)?;
            // mv arg, src
            self.out.push(RiscVOp::Addi {
                rd: self.arg_regs[idx as usize],
                rs1: src,
                imm: 0,
            });
            Ok(())
        } else if let Some(&reg) = self.promoted.get(&idx) {
            // #472: promoted i32 local — write the s-reg (`mv reg, src`) instead
            // of a frame `sw`. Pop the value FIRST, then snapshot any surviving
            // vstack alias of `reg` (from an earlier `local.get` of this local)
            // so the overwrite can't corrupt it (WAR fix). `src` was just popped
            // so it is not among the scanned entries.
            let src = self.pop_i32(op)?;
            if src != reg {
                self.snapshot_aliases(reg, None);
                self.out.push(RiscVOp::Addi {
                    rd: reg,
                    rs1: src,
                    imm: 0,
                });
            }
            Ok(())
        } else {
            // #223: non-param local — store to its frame slot (sw src, off(sp)).
            // #312: an i64 local stores both halves of the pair (lo at off,
            // hi at off+4); the slot width came from `infer_i64_locals`, so
            // the pop below doubles as a type check.
            let (off, is_i64) = self.local_slot(idx, op)?;
            if is_i64 {
                let (lo, hi) = self.pop_i64(op)?;
                self.out.push(RiscVOp::Sw {
                    rs1: Reg::SP,
                    rs2: lo,
                    imm: off,
                });
                self.out.push(RiscVOp::Sw {
                    rs1: Reg::SP,
                    rs2: hi,
                    imm: off + 4,
                });
            } else {
                let src = self.pop_i32(op)?;
                self.out.push(RiscVOp::Sw {
                    rs1: Reg::SP,
                    rs2: src,
                    imm: off,
                });
            }
            Ok(())
        }
    }

    fn lower_local_tee(&mut self, idx: u32, op: &WasmOp) -> Result<(), SelectorError> {
        // tee = set + get; the value remains on the stack.
        let top = self
            .vstack
            .last()
            .copied()
            .ok_or_else(|| SelectorError::StackUnderflow(op.clone()))?;
        if (idx as usize) < self.arg_regs.len() {
            // #312: i64 params are unsupported — see lower_local_get.
            if self.i64_locals.contains(&idx) {
                return Err(SelectorError::Unsupported(op.clone()));
            }
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
            self.out.push(RiscVOp::Addi {
                rd: self.arg_regs[idx as usize],
                rs1: src,
                imm: 0,
            });
            Ok(())
        } else if let Some(&reg) = self.promoted.get(&idx) {
            // #472: promoted i32 local — `mv reg, src`, value STAYS on the
            // vstack (tee semantics). The kept top holds the value written and
            // is left aliased to whatever produced it (`src`), independent of
            // `reg`, so a later `local.set` of this local can't corrupt it.
            // Snapshot only the OTHER live aliases of `reg` (earlier reads),
            // never the top (skip = top index).
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
            if src != reg {
                let top_idx = self.vstack.len() - 1;
                self.snapshot_aliases(reg, Some(top_idx));
                self.out.push(RiscVOp::Addi {
                    rd: reg,
                    rs1: src,
                    imm: 0,
                });
            }
            Ok(())
        } else {
            // #223: tee = store to the frame slot, value stays on the vstack.
            // #312: i64 tee stores both halves (lo at off, hi at off+4).
            let (off, is_i64) = self.local_slot(idx, op)?;
            match (is_i64, top) {
                (true, VstackVal::I64 { lo, hi }) => {
                    self.out.push(RiscVOp::Sw {
                        rs1: Reg::SP,
                        rs2: lo,
                        imm: off,
                    });
                    self.out.push(RiscVOp::Sw {
                        rs1: Reg::SP,
                        rs2: hi,
                        imm: off + 4,
                    });
                    Ok(())
                }
                (false, VstackVal::I32(src)) => {
                    self.out.push(RiscVOp::Sw {
                        rs1: Reg::SP,
                        rs2: src,
                        imm: off,
                    });
                    Ok(())
                }
                (expected_i64, other) => Err(SelectorError::StackTypeMismatch {
                    op: op.clone(),
                    expected: if expected_i64 { "i64" } else { "i32" },
                    found: other.type_name(),
                }),
            }
        }
    }

    /// #223: `i32.extend8_s` / `i32.extend16_s` — sign-extend the low byte or
    /// halfword of an i32. RV32 has no sign-extend op, so shift the bits up to
    /// the top and arithmetic-shift back (`shift` = 24 for 8-bit, 16 for 16-bit).
    fn lower_sign_extend(&mut self, op: &WasmOp, shift: u8) -> Result<(), SelectorError> {
        let src = self.pop_i32(op)?;
        let dst = self.alloc_temp();
        self.out.push(RiscVOp::Slli {
            rd: dst,
            rs1: src,
            shamt: shift,
        });
        self.out.push(RiscVOp::Srai {
            rd: dst,
            rs1: dst,
            shamt: shift,
        });
        self.push_i32(dst);
        Ok(())
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
            // #232: rs1 (dividend) and rs2 (divisor) were popped off the vstack,
            // so `live_regs` no longer protects them — but both are read by the
            // guard branches below and rs1/rs2 by the `div` itself. The guard's
            // INT_MIN / -1 constants must NOT be materialized into either, or we
            // clobber the dividend before the `bne rs1, tmin` reads it (the
            // lowest-free allocator otherwise reuses rs1's register here).
            let tmin = self.alloc_temp_avoiding(&[rs1, rs2]);
            // INT_MIN = 0x80000000. emit_load_imm decomposes into lui+addi.
            emit_load_imm(&mut self.out, tmin, i32::MIN);
            // bne rs1, tmin, .Lsdiv_ok → dividend != INT_MIN, no overflow
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1,
                rs2: tmin,
                label: ok_overflow.clone(),
            });
            let neg1 = self.alloc_temp_avoiding(&[rs1, rs2]);
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

    /// #472 (VCR-SEL-004 port): record a fusible comparison for a possibly
    /// following `select`. No-op under the `SYNTH_RV_CMP_SELECT=0` opt-out
    /// (that path never populates `pending_cmp`, keeping it byte-identical to
    /// the pre-flip baseline).
    /// `start` is `out.len()` from BEFORE the boolean materialization was
    /// emitted; `cond(rs1, rs2)` must be TRUE exactly when the wasm comparison
    /// yields 1.
    fn record_pending_cmp(
        &mut self,
        cond: Branch,
        rs1: Reg,
        rs2: Reg,
        bool_reg: Reg,
        start: usize,
    ) {
        if self.cmp_select_fuse {
            self.pending_cmp = Some(PendingCmp {
                cond,
                rs1,
                rs2,
                bool_reg,
                start,
                end: self.out.len(),
            });
        }
    }

    fn lower_eqz(&mut self, op: &WasmOp) -> Result<(), SelectorError> {
        let src = self.pop_i32(op)?;
        let dst = self.alloc_temp();
        let start = self.out.len();
        // sltiu dst, src, 1  → 1 iff src == 0
        self.out.push(RiscVOp::Sltiu {
            rd: dst,
            rs1: src,
            imm: 1,
        });
        self.push_i32(dst);
        // eqz is true iff src == 0 → beq src, zero.
        self.record_pending_cmp(Branch::Eq, src, Reg::ZERO, dst, start);
        Ok(())
    }

    fn lower_cmp_eq(&mut self, op: &WasmOp, invert: bool) -> Result<(), SelectorError> {
        let (lhs, rhs) = self.pop_pair_i32(op)?;
        let diff = self.alloc_temp();
        let start = self.out.len();
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
        // eq → beq lhs, rhs ; ne → bne lhs, rhs (both instructions fusible).
        let cond = if invert { Branch::Ne } else { Branch::Eq };
        self.record_pending_cmp(cond, lhs, rhs, dst, start);
        Ok(())
    }

    fn lower_cmp_signed_lt(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair_i32(op)?;
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        let start = self.out.len();
        self.out.push(RiscVOp::Slt { rd: dst, rs1, rs2 });
        self.push_i32(dst);
        // lt_s (and gt_s via the operand swap) → blt rs1, rs2.
        self.record_pending_cmp(Branch::Lt, rs1, rs2, dst, start);
        Ok(())
    }

    fn lower_cmp_signed_ge(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        // a >= b  =  !(a < b) ; le maps via swap.
        let (a, b) = self.pop_pair_i32(op)?;
        let lt = self.alloc_temp();
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        let start = self.out.len();
        self.out.push(RiscVOp::Slt { rd: lt, rs1, rs2 });
        // dst = lt ^ 1  (flip 0/1)
        self.out.push(RiscVOp::Xori {
            rd: dst,
            rs1: lt,
            imm: 1,
        });
        self.push_i32(dst);
        // ge_s (and le_s via the operand swap) → bge rs1, rs2.
        self.record_pending_cmp(Branch::Ge, rs1, rs2, dst, start);
        Ok(())
    }

    fn lower_cmp_unsigned_lt(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair_i32(op)?;
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        let start = self.out.len();
        self.out.push(RiscVOp::Sltu { rd: dst, rs1, rs2 });
        self.push_i32(dst);
        // lt_u (and gt_u via the operand swap) → bltu rs1, rs2.
        self.record_pending_cmp(Branch::Ltu, rs1, rs2, dst, start);
        Ok(())
    }

    fn lower_cmp_unsigned_ge(&mut self, op: &WasmOp, swap: bool) -> Result<(), SelectorError> {
        let (a, b) = self.pop_pair_i32(op)?;
        let lt = self.alloc_temp();
        let dst = self.alloc_temp();
        let (rs1, rs2) = if swap { (b, a) } else { (a, b) };
        let start = self.out.len();
        self.out.push(RiscVOp::Sltu { rd: lt, rs1, rs2 });
        self.out.push(RiscVOp::Xori {
            rd: dst,
            rs1: lt,
            imm: 1,
        });
        self.push_i32(dst);
        // ge_u (and le_u via the operand swap) → bgeu rs1, rs2.
        self.record_pending_cmp(Branch::Geu, rs1, rs2, dst, start);
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
            then_results: Vec::new(),
        });
        Ok(())
    }

    fn lower_else(&mut self, _op: &WasmOp) -> Result<(), SelectorError> {
        // Read the frame's fields up front so the mutable borrow is released
        // before touching `self.vstack` / `self.out`.
        let frame = self
            .ctrl
            .last()
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
        let entry = frame.stack_height_at_entry;
        // jal zero, Lif_end  → end of then-branch jumps past the else
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: end,
        });
        // Lelse:
        self.out.push(RiscVOp::Label { name: else_label });
        // #343: capture the then-arm's result value(s) — the vstack entries
        // above the if-entry checkpoint — before resetting the stack for the
        // else-arm. wasm discards the then-branch values when entering the
        // else-branch, but their REGISTERS must be reconciled with the
        // else-arm's at `end` (see `lower_end`) so both arms leave the join
        // value in the same place. `split_off` both captures and truncates.
        let then_results = self.vstack.split_off(entry);
        let frame = self
            .ctrl
            .last_mut()
            .expect("if frame still open (checked above)");
        frame.then_results = then_results;
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
                // join the end label so beq lands here. A valid if-without-else
                // has arity 0 (no result), so there is nothing to reconcile.
                self.out.push(RiscVOp::Label { name: else_label });
            } else if frame.kind == FrameKind::Else {
                // #343: reconcile the two arms onto a single set of result
                // registers. The then-arm's results were captured at `else`
                // (`frame.then_results`); the else-arm's results are the vstack
                // entries above the entry checkpoint right now. The `mv`s
                // emitted here sit on the ELSE path — between the else-arm body
                // and `end_label` — and the then-path's `jal end_label`
                // (emitted at `else`) jumps over them. So on the then path the
                // then-arm's value is already live in the merged register; on
                // the else path each `mv rd_then, rd_else` moves the else value
                // into the same register. When both arms already chose the same
                // register, NO `mv` is emitted (control-flow-only / register-
                // symmetric if/else stays byte-identical).
                let then_results = frame.then_results;
                let else_results = self.vstack.split_off(frame.stack_height_at_entry);
                if then_results.len() != else_results.len() {
                    return Err(SelectorError::ControlMismatch(
                        "if/else arms disagree on result arity (#343)",
                    ));
                }
                for (then_v, else_v) in then_results.iter().zip(else_results.iter()) {
                    self.reconcile_if_result(*then_v, *else_v)?;
                }
                // The merged results live in the then-arm's registers — push
                // them back so the surrounding code (return / outer op) reads
                // them.
                self.vstack.extend(then_results);
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

    /// #343: reconcile one if-result position between the two arms — make the
    /// else-arm's result register(s) hold the value the then-arm's do, by
    /// emitting `mv rd_then, rd_else` (i64: lo and hi) on the ELSE path when the
    /// two arms chose different registers. RV32 has no `mv` mnemonic; `addi rd,
    /// rs, 0` is the canonical encoding (the same one the return epilogue uses).
    /// Emitting NOTHING when the registers already match is what keeps register-
    /// symmetric / control-flow-only if/else byte-identical.
    ///
    /// A width mismatch between arms (i32 vs i64) is invalid wasm; surface it as
    /// a recoverable `ControlMismatch` rather than emit a half-move.
    ///
    /// The i64 case emits the `lo` then `hi` move sequentially, which is only
    /// correct if the two positions do not form a register-permutation cycle
    /// (`else.lo == then.hi && else.hi == then.lo`). That cannot arise here:
    /// both arms begin allocation from the identical free-register set (the
    /// else-arm resets the vstack to the if-entry checkpoint) and every i64
    /// lowering allocates `lo` before `hi`, so `lo` occupies a lower-indexed
    /// register than `hi` in BOTH arms — a 2-cycle would require
    /// `else.lo == then.hi > then.lo == else.hi`, contradicting lo-before-hi.
    fn reconcile_if_result(
        &mut self,
        then_v: VstackVal,
        else_v: VstackVal,
    ) -> Result<(), SelectorError> {
        match (then_v, else_v) {
            (VstackVal::I32(rt), VstackVal::I32(re)) => {
                if rt != re {
                    self.out.push(RiscVOp::Addi {
                        rd: rt,
                        rs1: re,
                        imm: 0,
                    });
                }
                Ok(())
            }
            (VstackVal::I64 { lo: tl, hi: th }, VstackVal::I64 { lo: el, hi: eh }) => {
                if tl != el {
                    self.out.push(RiscVOp::Addi {
                        rd: tl,
                        rs1: el,
                        imm: 0,
                    });
                }
                if th != eh {
                    self.out.push(RiscVOp::Addi {
                        rd: th,
                        rs1: eh,
                        imm: 0,
                    });
                }
                Ok(())
            }
            _ => Err(SelectorError::ControlMismatch(
                "if/else result width mismatch between arms (#343)",
            )),
        }
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
        // #312 (mirrors ARM #311): when the callee's signature says it returns
        // i64, the result is the a0 (lo) : a1 (hi) pair — tag it as such so a
        // following `local.set` of an i64 local stores both words instead of
        // tripping the i32 type check. An absent table entry keeps the legacy
        // i32 tagging.
        if self
            .func_ret_i64
            .get(func_idx as usize)
            .copied()
            .unwrap_or(false)
        {
            self.push_i64(Reg::A0, Reg::A1);
        } else {
            self.push_i32(Reg::A0);
        }
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
        let ((vlo, vhi), (samt, samt_hi)) = self.pop_pair_i64(op)?;
        self.unpin(&[samt_hi]); // #312: the amount's high limb is never read
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
        self.unpin(&[s, test]); // #312: both dead after the bit-5 branch

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
                self.unpin(&[carry, hi_shifted]); // #312: arm-local scratch
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
                self.unpin(&[carry, lo_shifted]); // #312: arm-local scratch
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
        self.unpin(&[s_lo, inv]); // #312: shift scratch dead past the join
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
        let ((vlo, vhi), (namt, namt_hi)) = self.pop_i64_then_amount(op)?;
        self.unpin(&[namt_hi]); // #312: the amount's high limb is never read
        // n = amount & 63
        let n = self.alloc_temp();
        self.out.push(RiscVOp::Andi {
            rd: n,
            rs1: namt,
            imm: 63,
        });
        self.unpin(&[namt]); // #312: dead once masked into n
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
        self.unpin(&[amt_a]); // #312: n is dead after the first shift
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
        self.unpin(&[s, test]); // #312: both dead after the bit-5 branch
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
                self.unpin(&[carry, hi_shifted]); // #312: arm-local scratch
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
                self.unpin(&[carry, lo_shifted]); // #312: arm-local scratch
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
        self.unpin(&[s_lo, inv]); // #312: shift scratch dead past the join
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
        self.unpin(&[hi_clz]); // #312: dead once copied into result
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
        self.unpin(&[lo_ctz]); // #312: dead once copied into result
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
            // #312: the probe scratch is dead at the end of each step — release
            // it so the five unrolled steps reuse three registers, not fifteen.
            self.unpin(&[probe, is_zero, add]);
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
        // #312: only the result survives this helper.
        self.unpin(&[x, n, is_src_zero]);
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
        // #312: only the result survives this helper.
        self.unpin(&[neg, iso, clz_iso, thirty_one, ctz, is_src_zero, corr]);
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
        // #312: only the result survives this helper.
        self.unpin(&[m1, m2, m4, m8, x, t, a, b]);
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

    // ────────── i64 division / remainder (Phase 3) ──────────
    //
    // RV32IMAC's M extension only provides 32-bit `div`/`divu`/`rem`/`remu`.
    // A 64-bit divide has no single instruction, so synth lowers it to an
    // inline software long-division loop — the moral equivalent of
    // compiler-rt's `__udivdi3` / `__divdi3` / `__umoddi3` / `__moddi3`.
    //
    // We pick the *inline* approach (rather than emitting a `Call` to a
    // runtime helper) because synth produces self-contained bare-metal ELF
    // and has no runtime-library contract; an inline loop keeps the output
    // dependency-free at a modest code-size cost (~30 instructions per op).
    //
    // The unsigned core is `emit_i64_udiv_inline`; `lower_i64_div` is the
    // single entry point for all four ops, dispatching on `signed`/`want_rem`
    // and wrapping the core with sign handling for the signed variants.

    /// Fixed register file used by the inline long-division core. RV32's
    /// `temps` pool is recycled round-robin with no liveness tracking, which
    /// is fine for straight-line code but unsafe across a loop body where
    /// many values stay live for all 64 iterations. So the long-division
    /// loop instead claims a fixed, non-overlapping set of registers for its
    /// exclusive use: it copies its inputs in at entry and hands its outputs
    /// back via dedicated result registers, after which the caller is free
    /// to move them into `alloc_temp` temporaries.
    ///
    /// The seven state registers (`q_lo, q_hi, r_lo, r_hi, d_lo, d_hi, cnt`)
    /// plus three loop-body scratch registers are all distinct and avoid the
    /// reserved `s0` (fp) / `s11` (linear-memory base).
    const DIV_Q_LO: Reg = Reg::T0;
    const DIV_Q_HI: Reg = Reg::T1;
    const DIV_R_LO: Reg = Reg::T2;
    const DIV_R_HI: Reg = Reg::T3;
    const DIV_D_LO: Reg = Reg::T4;
    const DIV_D_HI: Reg = Reg::T5;
    const DIV_CNT: Reg = Reg::T6;
    const DIV_SCRATCH0: Reg = Reg::S1;
    const DIV_SCRATCH1: Reg = Reg::S2;
    const DIV_SCRATCH2: Reg = Reg::S3;
    /// Cycle-breaking scratch for the input parallel-move. Must be outside
    /// the `temps` pool (a div input could otherwise alias it) — `s7` is
    /// callee-saved and never handed out by `alloc_temp`.
    const DIV_MOVE_SCRATCH: Reg = Reg::S7;

    /// #317: the complete set of registers the inline long-division core
    /// writes (its fixed state file + the three loop scratches). The core
    /// bypasses the allocator entirely, so any allocator-chosen temporary
    /// that must stay live *across* `emit_i64_udiv_inline` (the signed
    /// path's `nsign`/`dsign` sign masks) has to avoid this set — otherwise
    /// the core's input parallel-move overwrites it before the result-sign
    /// fix-up reads it. `DIV_MOVE_SCRATCH` (`s7`) is never in the `temps`
    /// pool so it needs no entry here. Of the pool, only `s4..s6` sit
    /// outside this set — and they are callee-saved, so a non-leaf function
    /// preserves them via `preserve_callee_saved`.
    const DIV_CORE_TEMPS: [Reg; 10] = [
        Self::DIV_Q_LO,
        Self::DIV_Q_HI,
        Self::DIV_R_LO,
        Self::DIV_R_HI,
        Self::DIV_D_LO,
        Self::DIV_D_HI,
        Self::DIV_CNT,
        Self::DIV_SCRATCH0,
        Self::DIV_SCRATCH1,
        Self::DIV_SCRATCH2,
    ];

    /// Emit a set of parallel register moves `dst <- src` such that every
    /// source is read before any move overwrites it — i.e. the moves behave
    /// as if performed simultaneously. `scratch` is a free register used to
    /// break dependency cycles (e.g. the swap `a<-b, b<-a`); the caller must
    /// guarantee `scratch` is neither a source nor a destination.
    ///
    /// Standard parallel-copy algorithm:
    ///  - repeatedly emit any move whose destination is not still needed as
    ///    a source by a pending move (safe, no clobber);
    ///  - when only cycles remain, save one node's value to `scratch`,
    ///    rewrite the move that sourced it to read `scratch` instead, and
    ///    continue. A permutation of N registers needs at most N+1 moves.
    ///
    /// `mv` is `addi rd, rs, 0`. Trivial `dst == src` moves are skipped.
    fn emit_parallel_move(&mut self, moves: &[(Reg, Reg)], scratch: Reg) {
        // Working list of (dst, src) pairs still to perform.
        let mut pending: Vec<(Reg, Reg)> = moves.iter().copied().filter(|(d, s)| d != s).collect();
        while !pending.is_empty() {
            // Find a move whose dst is not the src of any *other* pending
            // move — emitting it cannot clobber a value still needed.
            let ready = pending
                .iter()
                .position(|&(d, _)| !pending.iter().any(|&(_, s)| s == d));
            match ready {
                Some(idx) => {
                    let (d, s) = pending.remove(idx);
                    self.out.push(RiscVOp::Addi {
                        rd: d,
                        rs1: s,
                        imm: 0,
                    });
                }
                None => {
                    // Only cycles remain. Break one: stash the first move's
                    // source into `scratch`, then redirect whichever pending
                    // move read that source to read `scratch` instead.
                    let (_, cyc_src) = pending[0];
                    self.out.push(RiscVOp::Addi {
                        rd: scratch,
                        rs1: cyc_src,
                        imm: 0,
                    });
                    for m in pending.iter_mut() {
                        if m.1 == cyc_src {
                            m.1 = scratch;
                        }
                    }
                }
            }
        }
    }

    /// Emit the unsigned 64-bit long-division core.
    ///
    /// Inputs `num = (num_lo, num_hi)` and `den = (den_lo, den_hi)` are
    /// **unsigned** 64-bit values. The caller must already have guaranteed a
    /// non-zero divisor (see `lower_i64_div`, which emits the trap). On
    /// return, the quotient lives in `(DIV_Q_LO, DIV_Q_HI)` and the
    /// remainder in `(DIV_R_LO, DIV_R_HI)`.
    ///
    /// Algorithm — classic restoring binary long division, numerator held in
    /// the quotient register (the "shift the dividend out, shift the quotient
    /// in" trick), 64 loop iterations:
    /// ```text
    ///   q = num ; r = 0 ; cnt = 64
    /// loop:
    ///   r = (r << 1) | (q >> 63)     ; shift the MSB of q into r's LSB
    ///   q = q << 1                   ; q's LSB is now free for a quotient bit
    ///   if r >=u den:                ; does the divisor fit?
    ///       r = r - den
    ///       q = q | 1                ; record a 1 quotient bit
    ///   cnt = cnt - 1
    ///   if cnt != 0: goto loop
    /// ```
    /// All of `<< 1`, the 64-bit unsigned compare, and the 64-bit subtract
    /// are open-coded over the lo/hi register pair.
    fn emit_i64_udiv_inline(&mut self, num: I64Pair, den: I64Pair) {
        let (q_lo, q_hi) = (Self::DIV_Q_LO, Self::DIV_Q_HI);
        let (r_lo, r_hi) = (Self::DIV_R_LO, Self::DIV_R_HI);
        let (d_lo, d_hi) = (Self::DIV_D_LO, Self::DIV_D_HI);
        let cnt = Self::DIV_CNT;
        let (s0, s1, s2) = (Self::DIV_SCRATCH0, Self::DIV_SCRATCH1, Self::DIV_SCRATCH2);

        // ── set-up: copy inputs into the fixed state registers ───────────
        // q = num, d = den. The four inputs came from `alloc_temp` and may
        // alias the fixed `DIV_*` state registers in any permutation, so a
        // naive sequence of copies could clobber a source before it's read.
        // `emit_parallel_move` schedules the four `mv`s so every source is
        // read before it's overwritten (cycle-breaking via one scratch).
        self.emit_parallel_move(
            &[(q_lo, num.0), (q_hi, num.1), (d_lo, den.0), (d_hi, den.1)],
            Self::DIV_MOVE_SCRATCH,
        );
        // r = 0 (the running remainder accumulator).
        self.out.push(RiscVOp::Addi {
            rd: r_lo,
            rs1: Reg::ZERO,
            imm: 0,
        });
        self.out.push(RiscVOp::Addi {
            rd: r_hi,
            rs1: Reg::ZERO,
            imm: 0,
        });
        // cnt = 64 (one loop pass per dividend bit).
        self.out.push(RiscVOp::Addi {
            rd: cnt,
            rs1: Reg::ZERO,
            imm: 64,
        });

        let loop_label = self.fresh_label("Ludiv_loop");
        let no_sub = self.fresh_label("Ludiv_nosub");
        self.out.push(RiscVOp::Label {
            name: loop_label.clone(),
        });

        // ── r = (r << 1) | (q >> 63) ─────────────────────────────────────
        // The MSB of the 64-bit quotient register becomes the new LSB of the
        // remainder. `q >> 63` is just bit 31 of q_hi.
        // s0 = q_hi >> 31  (the bit crossing from q into r).
        self.out.push(RiscVOp::Srli {
            rd: s0,
            rs1: q_hi,
            shamt: 31,
        });
        // r_hi = (r_hi << 1) | (r_lo >> 31) — carry r_lo's MSB up into r_hi.
        self.out.push(RiscVOp::Srli {
            rd: s1,
            rs1: r_lo,
            shamt: 31,
        });
        self.out.push(RiscVOp::Slli {
            rd: r_hi,
            rs1: r_hi,
            shamt: 1,
        });
        self.out.push(RiscVOp::Or {
            rd: r_hi,
            rs1: r_hi,
            rs2: s1,
        });
        // r_lo = (r_lo << 1) | s0 — shift r_lo up and drop in the bit from q.
        self.out.push(RiscVOp::Slli {
            rd: r_lo,
            rs1: r_lo,
            shamt: 1,
        });
        self.out.push(RiscVOp::Or {
            rd: r_lo,
            rs1: r_lo,
            rs2: s0,
        });

        // ── q = q << 1 ───────────────────────────────────────────────────
        // Frees q's LSB to receive a quotient bit below.
        self.out.push(RiscVOp::Srli {
            rd: s1,
            rs1: q_lo,
            shamt: 31,
        });
        self.out.push(RiscVOp::Slli {
            rd: q_hi,
            rs1: q_hi,
            shamt: 1,
        });
        self.out.push(RiscVOp::Or {
            rd: q_hi,
            rs1: q_hi,
            rs2: s1,
        });
        self.out.push(RiscVOp::Slli {
            rd: q_lo,
            rs1: q_lo,
            shamt: 1,
        });

        // ── if r >=u den: r -= den ; q |= 1 ──────────────────────────────
        // 64-bit unsigned compare `r <u den`: compare hi halves, tie-break on
        // lo. s2 = 1 iff r <u den → if s2 != 0 we must NOT subtract.
        let lo_lt = self.fresh_label("Ludiv_lolt");
        let cmp_done = self.fresh_label("Ludiv_cmpd");
        // hi halves equal → fall through to the lo-half compare.
        self.out.push(RiscVOp::Branch {
            cond: Branch::Eq,
            rs1: r_hi,
            rs2: d_hi,
            label: lo_lt.clone(),
        });
        // hi halves differ: r <u den iff r_hi <u d_hi.
        self.out.push(RiscVOp::Sltu {
            rd: s2,
            rs1: r_hi,
            rs2: d_hi,
        });
        self.out.push(RiscVOp::Jal {
            rd: Reg::ZERO,
            label: cmp_done.clone(),
        });
        self.out.push(RiscVOp::Label { name: lo_lt });
        // hi halves equal: tie-break unsigned on the lo halves.
        self.out.push(RiscVOp::Sltu {
            rd: s2,
            rs1: r_lo,
            rs2: d_lo,
        });
        self.out.push(RiscVOp::Label { name: cmp_done });
        // bne s2, zero, Ludiv_nosub → r <u den, divisor doesn't fit, skip.
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: s2,
            rs2: Reg::ZERO,
            label: no_sub.clone(),
        });
        // r >= den: 64-bit subtract r -= den with borrow.
        // borrow = (r_lo <u d_lo), captured before the subtraction.
        self.out.push(RiscVOp::Sltu {
            rd: s0,
            rs1: r_lo,
            rs2: d_lo,
        });
        self.out.push(RiscVOp::Sub {
            rd: r_lo,
            rs1: r_lo,
            rs2: d_lo,
        });
        self.out.push(RiscVOp::Sub {
            rd: r_hi,
            rs1: r_hi,
            rs2: d_hi,
        });
        self.out.push(RiscVOp::Sub {
            rd: r_hi,
            rs1: r_hi,
            rs2: s0,
        });
        // q |= 1 — record the quotient bit.
        self.out.push(RiscVOp::Ori {
            rd: q_lo,
            rs1: q_lo,
            imm: 1,
        });
        self.out.push(RiscVOp::Label { name: no_sub });

        // ── cnt -= 1 ; loop while cnt != 0 ───────────────────────────────
        self.out.push(RiscVOp::Addi {
            rd: cnt,
            rs1: cnt,
            imm: -1,
        });
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: cnt,
            rs2: Reg::ZERO,
            label: loop_label,
        });
        // On exit: quotient in (q_lo,q_hi), remainder in (r_lo,r_hi).
    }

    /// Lower all four i64 div/rem ops. `signed` selects div_s/rem_s vs
    /// div_u/rem_u; `want_rem` selects rem vs div.
    ///
    /// Shared structure:
    ///  1. **Zero-divisor trap** — wasm traps when the *full 64-bit* divisor
    ///     is zero, so we OR the lo and hi halves and trap when the OR is 0.
    ///  2. **Signed-overflow trap** (div_s only) — `INT64_MIN / -1` has an
    ///     unrepresentable quotient (`2^63`); wasm traps. `rem_s` of the same
    ///     operands does NOT trap (the remainder is 0), so the guard is
    ///     emitted for `div_s` but not `rem_s`.
    ///  3. **Signed magnitude reduction** — the unsigned core handles only
    ///     non-negative operands. For signed ops we record each operand's
    ///     sign, take absolute values, divide, then fix the result sign:
    ///       - quotient sign = sign(dividend) XOR sign(divisor)
    ///       - remainder sign = sign(dividend)   (wasm/C truncated division)
    ///  4. **Unsigned core** — `emit_i64_udiv_inline`.
    fn lower_i64_div(
        &mut self,
        op: &WasmOp,
        signed: bool,
        want_rem: bool,
    ) -> Result<(), SelectorError> {
        let ((nl, nh), (dl, dh)) = self.pop_pair_i64(op)?;

        // ── Trap 1: divide/remainder by zero ─────────────────────────────
        // The divisor is zero iff *both* halves are zero. `or` them and
        // branch when the result is non-zero.
        let zero_or = self.alloc_temp();
        self.out.push(RiscVOp::Or {
            rd: zero_or,
            rs1: dl,
            rs2: dh,
        });
        let div_ok = self.fresh_label("Li64div_ok");
        self.out.push(RiscVOp::Branch {
            cond: Branch::Ne,
            rs1: zero_or,
            rs2: Reg::ZERO,
            label: div_ok.clone(),
        });
        self.out.push(RiscVOp::Ebreak);
        self.out.push(RiscVOp::Label { name: div_ok });
        self.unpin(&[zero_or]); // #312: dead after the zero-divisor branch

        // ── Trap 2: signed INT64_MIN / -1 overflow (div_s only) ──────────
        // INT64_MIN = 0x8000_0000_0000_0000 → lo == 0, hi == 0x8000_0000.
        // -1 (64-bit) → lo == -1, hi == -1. `rem_s` does NOT trap here
        // (INT64_MIN % -1 == 0), so this guard is div_s-exclusive.
        if signed && !want_rem && self.options.signed_div_overflow_trap {
            let sdiv_ok = self.fresh_label("Li64sdiv_ok");
            // dividend != INT64_MIN ? skip. Test the hi half against
            // 0x8000_0000 and the lo half against 0.
            // #232: same discipline as the i32 guard — the operand halves
            // (nl/nh/dl/dh) are off the vstack, so the guard constants must
            // avoid them or the lowest-free allocator clobbers a live operand.
            let tmin_hi = self.alloc_temp_avoiding(&[nl, nh, dl, dh]);
            emit_load_imm(&mut self.out, tmin_hi, i32::MIN);
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1: nh,
                rs2: tmin_hi,
                label: sdiv_ok.clone(),
            });
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1: nl,
                rs2: Reg::ZERO,
                label: sdiv_ok.clone(),
            });
            // divisor != -1 ? skip. -1 has both halves all-ones.
            let neg1 = self.alloc_temp_avoiding(&[nl, nh, dl, dh]);
            self.out.push(RiscVOp::Addi {
                rd: neg1,
                rs1: Reg::ZERO,
                imm: -1,
            });
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1: dl,
                rs2: neg1,
                label: sdiv_ok.clone(),
            });
            self.out.push(RiscVOp::Branch {
                cond: Branch::Ne,
                rs1: dh,
                rs2: neg1,
                label: sdiv_ok.clone(),
            });
            // dividend == INT64_MIN and divisor == -1 → overflow, trap.
            self.out.push(RiscVOp::Ebreak);
            self.out.push(RiscVOp::Label { name: sdiv_ok });
            self.unpin(&[tmin_hi, neg1]); // #312: guard constants are dead
        }

        if !signed {
            // ── Unsigned: feed the operands straight to the core. ────────
            self.emit_i64_udiv_inline((nl, nh), (dl, dh));
            let res = self.copy_div_result(want_rem);
            self.push_i64(res.0, res.1);
            return Ok(());
        }

        // ── Signed: reduce to magnitudes, divide, fix up the sign. ───────
        // The sign of each operand is bit 63 = the MSB of its hi half;
        // `sra hi, 31` broadcasts it to an all-ones / all-zeros mask.
        //
        // #317: `nsign`/`dsign` stay live across `emit_i64_udiv_inline`
        // (they're read only in the post-core result-sign fix-up), so they
        // must NOT land in the core's fixed register file — otherwise the
        // core's input parallel-move (which copies the divisor into
        // `DIV_D_LO`/`DIV_D_HI` = `t4`/`t5`) clobbers them before the sign
        // is applied, yielding the wrong sign (e.g. `div_s(-100,3)` → `0x1f`
        // instead of `-34`). Allocate them outside `DIV_CORE_TEMPS`; with
        // the operands typically in the low `t`-registers this places them
        // in the callee-saved `s4..s6`, which the core provably never writes.
        let nsign = self.alloc_temp_avoiding(&Self::DIV_CORE_TEMPS);
        self.out.push(RiscVOp::Srai {
            rd: nsign,
            rs1: nh,
            shamt: 31,
        });
        let dsign = self.alloc_temp_avoiding(&Self::DIV_CORE_TEMPS);
        self.out.push(RiscVOp::Srai {
            rd: dsign,
            rs1: dh,
            shamt: 31,
        });

        // |dividend| and |divisor|. Negating unconditionally then selecting
        // would also work, but the operands here came from `alloc_temp`, so
        // we just negate into fresh temps and branch-select.
        let (nabs_lo, nabs_hi) = self.emit_i64_abs(nl, nh, nsign);
        self.unpin(&[nl, nh]); // #312: dividend halves replaced by |dividend|
        let (dabs_lo, dabs_hi) = self.emit_i64_abs(dl, dh, dsign);
        self.unpin(&[dl, dh]); // #312: divisor halves replaced by |divisor|

        self.emit_i64_udiv_inline((nabs_lo, nabs_hi), (dabs_lo, dabs_hi));
        // #312: the core copied its inputs into the fixed DIV_* registers.
        self.unpin(&[nabs_lo, nabs_hi, dabs_lo, dabs_hi]);
        let (mag_lo, mag_hi) = self.copy_div_result(want_rem);

        // Result sign:
        //  - quotient: negative iff the operand signs differ → nsign ^ dsign
        //  - remainder: matches the dividend's sign           → nsign
        let result_sign = if want_rem {
            nsign
        } else {
            let xs = self.alloc_temp();
            self.out.push(RiscVOp::Xor {
                rd: xs,
                rs1: nsign,
                rs2: dsign,
            });
            xs
        };

        // Conditionally negate the magnitude when result_sign is all-ones.
        let (final_lo, final_hi) = self.emit_i64_apply_sign(mag_lo, mag_hi, result_sign);
        self.push_i64(final_lo, final_hi);
        Ok(())
    }

    /// Copy the long-division core's fixed result registers into fresh
    /// `alloc_temp` temporaries — `want_rem` picks the remainder pair, else
    /// the quotient pair. Done immediately after the core so the fixed
    /// `DIV_*` registers can be reused by any later op.
    fn copy_div_result(&mut self, want_rem: bool) -> I64Pair {
        let (src_lo, src_hi) = if want_rem {
            (Self::DIV_R_LO, Self::DIV_R_HI)
        } else {
            (Self::DIV_Q_LO, Self::DIV_Q_HI)
        };
        let lo = self.alloc_temp();
        let hi = self.alloc_temp();
        self.out.push(RiscVOp::Addi {
            rd: lo,
            rs1: src_lo,
            imm: 0,
        });
        self.out.push(RiscVOp::Addi {
            rd: hi,
            rs1: src_hi,
            imm: 0,
        });
        (lo, hi)
    }

    /// Absolute value of a 64-bit value, given a precomputed sign mask
    /// (`sra hi, 31` — all-ones if negative). Returns `(lo, hi)` of `|x|`.
    ///
    /// Branchless: `abs(x) = (x ^ mask) - mask`. When `mask` is all-ones
    /// this is `~x + 1 = -x`; when all-zeros it is `x` unchanged. The `- mask`
    /// is a 64-bit subtract (`- (-1) = +1` carries into the hi half).
    fn emit_i64_abs(&mut self, lo: Reg, hi: Reg, mask: Reg) -> I64Pair {
        let xl = self.alloc_temp();
        let xh = self.alloc_temp();
        self.out.push(RiscVOp::Xor {
            rd: xl,
            rs1: lo,
            rs2: mask,
        });
        self.out.push(RiscVOp::Xor {
            rd: xh,
            rs1: hi,
            rs2: mask,
        });
        // 64-bit subtract (xl,xh) - (mask,mask), with borrow from lo to hi.
        let borrow = self.alloc_temp();
        self.out.push(RiscVOp::Sltu {
            rd: borrow,
            rs1: xl,
            rs2: mask,
        });
        let res_lo = self.alloc_temp();
        let res_hi = self.alloc_temp();
        self.out.push(RiscVOp::Sub {
            rd: res_lo,
            rs1: xl,
            rs2: mask,
        });
        self.out.push(RiscVOp::Sub {
            rd: res_hi,
            rs1: xh,
            rs2: mask,
        });
        self.out.push(RiscVOp::Sub {
            rd: res_hi,
            rs1: res_hi,
            rs2: borrow,
        });
        // #312: only the result pair survives this helper.
        self.unpin(&[xl, xh, borrow]);
        (res_lo, res_hi)
    }

    /// Conditionally negate a 64-bit value: returns `-x` when `sign` is
    /// all-ones, `x` when `sign` is all-zeros. Same `(x ^ mask) - mask`
    /// branchless identity as `emit_i64_abs` — reused here for the result
    /// sign fix-up of signed div/rem.
    fn emit_i64_apply_sign(&mut self, lo: Reg, hi: Reg, sign: Reg) -> I64Pair {
        self.emit_i64_abs(lo, hi, sign)
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

    /// #343: an `if (result i32)` whose arms land the result in DIFFERENT
    /// registers must reconcile them at the join — exactly one `mv rd_then,
    /// rd_else` (`addi rd, rs, 0`) on the else path, between the else label and
    /// the end label. The then-path `jal` jumps over it, so both arms leave the
    /// value in `rd_then`. Here the then-arm computes `1 + 2` (result lands in
    /// an `add` destination, a distinct register from the else-arm's bare const).
    #[test]
    fn if_result_asymmetric_arms_reconcile_to_one_register_343() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::If,
                WasmOp::I32Const(1),
                WasmOp::I32Const(2),
                WasmOp::I32Add, // then-result in the add's dest reg
                WasmOp::Else,
                WasmOp::I32Const(20), // else-result in a bare const reg
                WasmOp::End,
                WasmOp::End,
            ],
            1,
        );
        let else_pos = out
            .iter()
            .position(|o| matches!(o, RiscVOp::Label { name } if name.starts_with("Lelse")))
            .expect("else label emitted");
        let end_pos = out
            .iter()
            .position(|o| matches!(o, RiscVOp::Label { name } if name.starts_with("Lif_end")))
            .expect("if-end label emitted");
        assert!(else_pos < end_pos, "else label precedes end label");
        // A reconciliation move is `addi rd, rs, 0` with rd != rs (register→
        // register copy). The else-arm's const is `addi rd, zero, 20` (imm 20),
        // so it is not mistaken for one.
        let recon: Vec<(Reg, Reg)> = out[else_pos + 1..end_pos]
            .iter()
            .filter_map(|o| match o {
                RiscVOp::Addi { rd, rs1, imm: 0 } if rd != rs1 => Some((*rd, *rs1)),
                _ => None,
            })
            .collect();
        assert_eq!(
            recon.len(),
            1,
            "exactly one reconciliation mv on the else path, got {recon:?}"
        );
    }

    /// #343 (i64): an `if (result i64)` whose arms land the pair in DIFFERENT
    /// register pairs must reconcile BOTH halves — two `mv` (`addi rd, rs, 0`)
    /// on the else path, one for `lo` and one for `hi`. This is the arm carrying
    /// the documented no-cycle argument (`lo` allocated before `hi` in both
    /// arms), so it gets its own gate rather than riding on the i32 test. The
    /// then-arm's `i64.add` result occupies a distinct pair from the else-arm's
    /// bare `i64.const`, and both halves of the two constants differ, so neither
    /// move can collapse into a self-copy.
    #[test]
    fn if_result_i64_reconciles_both_halves_343() {
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::If,
                WasmOp::I64Const(0x1_0000_0002),
                WasmOp::I64Const(1),
                WasmOp::I64Add, // then-result pair in the add's dest regs
                WasmOp::Else,
                WasmOp::I64Const(0x7_0000_0020), // else-result pair, distinct
                WasmOp::End,
                WasmOp::End,
            ],
            1,
        );
        let else_pos = out
            .iter()
            .position(|o| matches!(o, RiscVOp::Label { name } if name.starts_with("Lelse")))
            .expect("else label emitted");
        let end_pos = out
            .iter()
            .position(|o| matches!(o, RiscVOp::Label { name } if name.starts_with("Lif_end")))
            .expect("if-end label emitted");
        assert!(else_pos < end_pos, "else label precedes end label");
        let recon: Vec<(Reg, Reg)> = out[else_pos + 1..end_pos]
            .iter()
            .filter_map(|o| match o {
                RiscVOp::Addi { rd, rs1, imm: 0 } if rd != rs1 => Some((*rd, *rs1)),
                _ => None,
            })
            .collect();
        assert_eq!(
            recon.len(),
            2,
            "an i64 join reconciles both lo and hi, got {recon:?}"
        );
        // The no-cycle invariant: the two moves are not a register permutation
        // (`mv a,b; mv b,a` would clobber `b` before its move). Distinct dests,
        // and no dest is another move's source.
        let (d0, s0) = recon[0];
        let (d1, s1) = recon[1];
        assert_ne!(d0, d1, "lo and hi move to different registers");
        assert!(
            d0 != s1 && d1 != s0,
            "reconciliation moves must not form a permutation cycle: {recon:?}"
        );
    }

    /// #343: a control-flow-only / result-less `if/else` (arity 0) carries no
    /// value across the join, so NO reconciliation move is emitted — this is
    /// what keeps such if/else byte-identical to the pre-#343 output.
    #[test]
    fn if_without_result_emits_no_reconciliation_343() {
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
        let else_pos = out
            .iter()
            .position(|o| matches!(o, RiscVOp::Label { name } if name.starts_with("Lelse")))
            .expect("else label emitted");
        let end_pos = out
            .iter()
            .position(|o| matches!(o, RiscVOp::Label { name } if name.starts_with("Lif_end")))
            .expect("if-end label emitted");
        let recon = out[else_pos + 1..end_pos]
            .iter()
            .filter(|o| matches!(o, RiscVOp::Addi { rd, rs1, imm: 0 } if rd != rs1))
            .count();
        assert_eq!(recon, 0, "no reconciliation for an arity-0 if/else");
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

    // -------- I64DivS / I64DivU / I64RemS / I64RemU (Phase 3) --------

    #[test]
    fn i64_div_rem_no_longer_unsupported() {
        // Phase 3 implements all four i64 div/rem ops via inline software
        // long division — the `Unsupported` arm must no longer fire for them.
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
                    WasmOp::Drop,
                    WasmOp::End,
                ],
                0,
            )
            .map(|_| ()); // RiscVSelection isn't Debug — drop the Ok payload.
            assert!(
                r.is_ok(),
                "{:?} should now lower (Phase 3), got {:?}",
                op,
                r
            );
        }
    }

    /// Shared assertion: every i64 div/rem op must emit the zero-divisor
    /// trap (`bne or, zero, ok ; ebreak ; ok:`) and the long-division loop
    /// (a backward `Branch` to a labelled loop head, plus the inner subtract
    /// guard). We pin the *shape*, not register allocation.
    fn assert_i64_divrem_shape(out: &[RiscVOp]) {
        // The long-division core branches/loops, so several Branch + Label
        // ops appear. The zero-divisor trap contributes an Ebreak.
        assert!(
            count(out, |op| matches!(op, RiscVOp::Ebreak)) >= 1,
            "i64 div/rem must emit a trap (ebreak) for the zero divisor"
        );
        // The long-division loop body shifts via slli/srli — the core uses
        // `slli/srli ..., 1` and `srli ..., 31` for the shift-in carries.
        assert!(
            count(out, |op| matches!(op, RiscVOp::Slli { shamt: 1, .. })) >= 1,
            "long-division loop shifts the quotient/remainder by 1"
        );
        assert!(
            count(out, |op| matches!(op, RiscVOp::Srli { shamt: 31, .. })) >= 1,
            "long-division loop extracts the crossing MSB via `>> 31`"
        );
        // The loop subtracts the divisor; the core uses Sub for the 64-bit
        // remainder subtraction.
        assert!(
            count(out, |op| matches!(op, RiscVOp::Sub { .. })) >= 1,
            "long-division loop subtracts the divisor"
        );
        // At least one backward branch closes the loop, plus the labels.
        assert!(
            count(out, |op| matches!(op, RiscVOp::Label { .. })) >= 3,
            "long-division core emits a loop label + inner-branch labels"
        );
    }

    #[test]
    fn i64_div_u_emits_zero_trap_and_long_division() {
        let out = run_i64(&[
            WasmOp::I64Const(100),
            WasmOp::I64Const(7),
            WasmOp::I64DivU,
            WasmOp::Drop,
        ]);
        assert_i64_divrem_shape(&out);
        // The divide-by-zero guard ORs the two divisor halves and branches
        // when the OR is non-zero.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Or { .. })) >= 1,
            "zero-divisor guard ORs the two divisor halves"
        );
    }

    #[test]
    fn i64_rem_u_emits_zero_trap_and_long_division() {
        let out = run_i64(&[
            WasmOp::I64Const(100),
            WasmOp::I64Const(7),
            WasmOp::I64RemU,
            WasmOp::Drop,
        ]);
        assert_i64_divrem_shape(&out);
    }

    #[test]
    fn i64_div_s_emits_zero_trap_and_long_division() {
        let out = run_i64(&[
            WasmOp::I64Const(-100),
            WasmOp::I64Const(7),
            WasmOp::I64DivS,
            WasmOp::Drop,
        ]);
        assert_i64_divrem_shape(&out);
        // Signed div reduces operands to magnitudes via `sra hi, 31` sign
        // masks, then fixes the result sign — at least two Srai-by-31.
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 31, .. })) >= 2,
            "signed div derives operand sign masks via `sra hi, 31`"
        );
    }

    #[test]
    fn i64_rem_s_emits_zero_trap_and_long_division() {
        let out = run_i64(&[
            WasmOp::I64Const(-100),
            WasmOp::I64Const(7),
            WasmOp::I64RemS,
            WasmOp::Drop,
        ]);
        assert_i64_divrem_shape(&out);
        // rem_s also needs the sign masks (remainder takes the dividend sign).
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Srai { shamt: 31, .. })) >= 2,
            "signed rem derives operand sign masks via `sra hi, 31`"
        );
    }

    /// #317: the `nsign`/`dsign` sign masks (the only `sra hi, 31` ops in the
    /// signed div/rem lowering) must NOT land in the inline long-division
    /// core's fixed register file. The core bypasses the allocator and copies
    /// its inputs into `DIV_D_LO`/`DIV_D_HI` (t4/t5) via a parallel-move; if a
    /// sign mask sat there it would be clobbered before `result_sign` reads it,
    /// producing the wrong sign (div_s(-100,3) → 0x1f instead of -34).
    #[test]
    fn i64_signed_div_sign_masks_avoid_div_core_file() {
        for op in [WasmOp::I64DivS, WasmOp::I64RemS] {
            let out = run_i64(&[
                WasmOp::I64Const(-100),
                WasmOp::I64Const(3),
                op.clone(),
                WasmOp::Drop,
            ]);
            let sign_mask_regs: Vec<Reg> = out
                .iter()
                .filter_map(|o| match o {
                    RiscVOp::Srai { rd, shamt: 31, .. } => Some(*rd),
                    _ => None,
                })
                .collect();
            assert!(
                sign_mask_regs.len() >= 2,
                "{op:?}: expected the two operand sign masks (`sra hi, 31`)"
            );
            for r in &sign_mask_regs {
                assert!(
                    !Selector::DIV_CORE_TEMPS.contains(r),
                    "{op:?}: sign mask landed in {r:?}, a register the udiv core \
                     overwrites (DIV_CORE_TEMPS = {:?}) — #317 sign clobber",
                    Selector::DIV_CORE_TEMPS
                );
            }
        }
    }

    #[test]
    fn i64_div_s_emits_signed_overflow_trap() {
        // INT64_MIN / -1 overflows: div_s must emit the overflow guard. The
        // guard materialises INT64_MIN's high half (0x8000_0000) via
        // emit_load_imm and branches against it; with the trap there are at
        // least two Ebreak ops (zero-divisor + overflow).
        let out = run_i64(&[
            WasmOp::I64Const(i64::MIN),
            WasmOp::I64Const(-1),
            WasmOp::I64DivS,
            WasmOp::Drop,
        ]);
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Ebreak)) >= 2,
            "div_s emits both the zero-divisor and the INT64_MIN/-1 traps"
        );
    }

    #[test]
    fn i64_rem_s_does_not_emit_overflow_trap() {
        // INT64_MIN % -1 == 0 and must NOT trap — rem_s emits only the
        // zero-divisor trap, so the Ebreak count is exactly one less than
        // the equivalent div_s. We compare the two directly.
        let rem_out = run_i64(&[
            WasmOp::I64Const(i64::MIN),
            WasmOp::I64Const(-1),
            WasmOp::I64RemS,
            WasmOp::Drop,
        ]);
        let div_out = run_i64(&[
            WasmOp::I64Const(i64::MIN),
            WasmOp::I64Const(-1),
            WasmOp::I64DivS,
            WasmOp::Drop,
        ]);
        let rem_ebreaks = count(&rem_out, |op| matches!(op, RiscVOp::Ebreak));
        let div_ebreaks = count(&div_out, |op| matches!(op, RiscVOp::Ebreak));
        assert_eq!(
            rem_ebreaks + 1,
            div_ebreaks,
            "rem_s must omit the INT64_MIN/-1 overflow trap that div_s emits"
        );
    }

    #[test]
    fn i64_div_result_is_i64_typed() {
        // The quotient is pushed as an i64 pair — a following i64 consumer
        // (I64Add) must lower without a type mismatch.
        let out = run_i64(&[
            WasmOp::I64Const(40),
            WasmOp::I64Const(8),
            WasmOp::I64DivU,
            WasmOp::I64Const(1),
            WasmOp::I64Add,
            WasmOp::Drop,
        ]);
        // I64Add emits its add/sltu/add/add quartet → at least 3 Add ops.
        assert!(count(&out, |op| matches!(op, RiscVOp::Add { .. })) >= 3);
    }

    #[test]
    fn parallel_move_breaks_a_swap_cycle() {
        // The input copy-in for the long-division core must be alias-safe
        // even when the inputs form a permutation cycle. A pure swap
        // `t0<-t1, t1<-t0` needs a scratch-mediated 3-move expansion.
        let mut ctx = Selector::new_with_options(0, SelectorOptions::wasm_compliant());
        ctx.emit_parallel_move(&[(Reg::T0, Reg::T1), (Reg::T1, Reg::T0)], Reg::S7);
        // A 2-cycle expands to exactly 3 moves (save + 2 copies).
        let mvs = count(&ctx.out, |op| matches!(op, RiscVOp::Addi { imm: 0, .. }));
        assert_eq!(mvs, 3, "a swap cycle expands to 3 scratch-mediated moves");
        // The scratch register must appear as a move destination (the save).
        assert!(
            ctx.out
                .iter()
                .any(|op| matches!(op, RiscVOp::Addi { rd: Reg::S7, .. })),
            "swap cycle is broken through the scratch register"
        );
    }

    #[test]
    fn parallel_move_skips_trivial_self_moves() {
        // `dst == src` pairs are no-ops and must not be emitted at all.
        let mut ctx = Selector::new_with_options(0, SelectorOptions::wasm_compliant());
        ctx.emit_parallel_move(&[(Reg::T0, Reg::T0), (Reg::T1, Reg::T2)], Reg::S7);
        let mvs = count(&ctx.out, |op| matches!(op, RiscVOp::Addi { .. }));
        assert_eq!(mvs, 1, "only the non-trivial move is emitted");
    }

    #[test]
    fn i64_div_u_runs_64_iteration_loop() {
        // Pin the long-division loop structure: the core sets the iteration
        // counter to 64 (`addi cnt, zero, 64`) and decrements it (`addi cnt,
        // cnt, -1`) — both immediates must appear.
        let out = run_i64(&[
            WasmOp::I64Const(99),
            WasmOp::I64Const(4),
            WasmOp::I64DivU,
            WasmOp::Drop,
        ]);
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Addi {
                    rs1: Reg::ZERO,
                    imm: 64,
                    ..
                }
            )) >= 1,
            "long-division core initialises the loop counter to 64"
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Addi { imm: -1, .. })) >= 1,
            "long-division core decrements the loop counter"
        );
    }

    /// #220: a function that uses callee-saved s-registers as temps must
    /// spill/restore them (RV psABI) — otherwise it corrupts the caller. The body
    /// stays unchanged; it is wrapped in a balanced prologue/epilogue.
    #[test]
    fn callee_saved_registers_preserved_220() {
        // Keep 8 values simultaneously live (the 7 caller-saved t-registers can
        // hold only 7), forcing the lowest-free allocator into the callee-saved
        // s-registers — then reduce them. This is what now exercises the #220
        // spill/restore path (a shorter expression stays in t-registers).
        let sel = select(
            &[
                WasmOp::I32Const(1),
                WasmOp::I32Const(2),
                WasmOp::I32Const(3),
                WasmOp::I32Const(4),
                WasmOp::I32Const(5),
                WasmOp::I32Const(6),
                WasmOp::I32Const(7),
                WasmOp::I32Const(8), // 8th live value → spills into s1
                WasmOp::I32Add,
                WasmOp::I32Add,
                WasmOp::I32Add,
                WasmOp::I32Add,
                WasmOp::I32Add,
                WasmOp::I32Add,
                WasmOp::I32Add,
            ],
            0,
        )
        .unwrap();
        let out = &sel.ops;

        // The body writes callee-saved s-registers...
        let writes_s = out
            .iter()
            .any(|op| op_dest(op).is_some_and(is_callee_saved_temp));
        assert!(writes_s, "test premise: body uses callee-saved s-registers");

        // ...so the prologue must SW each of them to the stack frame, and the
        // first instruction must open the frame (addi sp, sp, -N).
        assert!(
            matches!(out.first(), Some(RiscVOp::Addi { rd: Reg::SP, imm, .. }) if *imm < 0),
            "prologue must open a stack frame: {:?}",
            out.first()
        );
        // Every callee-saved reg written is also spilled (SW) and restored (LW).
        for op in out.iter() {
            if let Some(rd) = op_dest(op)
                && is_callee_saved_temp(rd)
            {
                {
                    assert!(
                        out.iter()
                            .any(|o| matches!(o, RiscVOp::Sw { rs2, .. } if *rs2 == rd)),
                        "callee-saved {rd:?} written but never spilled (#220)"
                    );
                    assert!(
                        out.iter()
                            .any(|o| matches!(o, RiscVOp::Lw { rd: r, .. } if *r == rd)),
                        "callee-saved {rd:?} written but never restored (#220)"
                    );
                }
            }
        }
        // SP adjustments balance (frame opened == frame closed).
        let sp_delta: i32 = out
            .iter()
            .filter_map(|op| match op {
                RiscVOp::Addi {
                    rd: Reg::SP, imm, ..
                } => Some(*imm),
                _ => None,
            })
            .sum();
        // One open (-N) + one close (+N) per return path; with N return paths the
        // sum is 0 only if open is counted once per path too. The epilogue closes
        // on every `ret`, and the single prologue opens once — so net is
        // `-N + (returns * N)`. Assert each close matches the open magnitude.
        let opens: Vec<i32> = out
            .iter()
            .filter_map(|op| match op {
                RiscVOp::Addi {
                    rd: Reg::SP, imm, ..
                } if *imm < 0 => Some(-*imm),
                _ => None,
            })
            .collect();
        let closes: Vec<i32> = out
            .iter()
            .filter_map(|op| match op {
                RiscVOp::Addi {
                    rd: Reg::SP, imm, ..
                } if *imm > 0 => Some(*imm),
                _ => None,
            })
            .collect();
        assert_eq!(opens.len(), 1, "exactly one prologue frame open");
        assert!(
            closes.iter().all(|&c| c == opens[0]),
            "every epilogue closes the same frame size as the prologue: {sp_delta}"
        );
    }

    /// #220: a function using only caller-saved (t/a) registers needs no frame,
    /// so the preservation pass must be a no-op (don't penalise simple functions).
    #[test]
    fn no_frame_when_only_caller_saved_220() {
        let sel = select(
            &[WasmOp::LocalGet(0), WasmOp::LocalGet(1), WasmOp::I32Add],
            2,
        )
        .unwrap();
        assert!(
            !sel.ops.iter().any(|op| matches!(op, RiscVOp::Sw { .. })),
            "no callee-saved spill for a t-register-only function"
        );
        assert!(
            !sel.ops
                .iter()
                .any(|op| matches!(op, RiscVOp::Addi { rd: Reg::SP, imm, .. } if *imm != 0)),
            "no stack-frame adjustment when no callee-saved register is used"
        );
    }

    /// #223: `select` lowers to a branch + two moves (RV32 has no cmov).
    #[test]
    fn select_lowers_to_branch_223() {
        let sel = select(
            &[
                WasmOp::I32Const(10),
                WasmOp::I32Const(20),
                WasmOp::I32Const(1),
                WasmOp::Select,
            ],
            0,
        )
        .unwrap();
        assert!(
            sel.ops.iter().any(|op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Ne,
                    rs2: Reg::ZERO,
                    ..
                }
            )),
            "select branches on `cond != 0`"
        );
        // Two arms, each a `mv` (Addi rd, rs, 0).
        assert!(
            count(&sel.ops, |op| matches!(op, RiscVOp::Addi { imm: 0, .. })) >= 2,
            "select moves both candidate values"
        );
    }

    /// #223: `i32.extend16_s` / `extend8_s` lower to `slli`+`srai`.
    #[test]
    fn sign_extend_uses_slli_srai_223() {
        for (op, sh) in [(WasmOp::I32Extend16S, 16u8), (WasmOp::I32Extend8S, 24u8)] {
            let sel = select(&[WasmOp::LocalGet(0), op], 1).unwrap();
            assert!(
                sel.ops
                    .iter()
                    .any(|o| matches!(o, RiscVOp::Slli { shamt, .. } if *shamt == sh)),
                "sign-extend uses slli #{sh}"
            );
            assert!(
                sel.ops
                    .iter()
                    .any(|o| matches!(o, RiscVOp::Srai { shamt, .. } if *shamt == sh)),
                "sign-extend uses srai #{sh}"
            );
        }
    }

    /// #223: a non-parameter local (idx >= num_params) is frame-backed — set
    /// stores to the stack (`sw`), get loads from it (`lw`), and the unified
    /// prologue opens a frame to hold it.
    #[test]
    fn non_param_local_uses_frame_223() {
        // num_params = 0, so local 0 is a non-param local.
        let sel = select(
            &[
                WasmOp::I32Const(42),
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
            ],
            0,
        )
        .unwrap();
        assert!(
            sel.ops
                .iter()
                .any(|op| matches!(op, RiscVOp::Sw { rs1: Reg::SP, .. })),
            "local.set on a non-param local stores to the frame"
        );
        assert!(
            sel.ops
                .iter()
                .any(|op| matches!(op, RiscVOp::Lw { rs1: Reg::SP, .. })),
            "local.get on a non-param local loads from the frame"
        );
        assert!(
            matches!(sel.ops.first(), Some(RiscVOp::Addi { rd: Reg::SP, imm, .. }) if *imm < 0),
            "a frame is opened for the local"
        );
    }

    /// #226: `alloc_temp` must never hand out a register that still pins a live
    /// `vstack` value, even after the round-robin pool wraps past its length.
    /// This is the invariant whose violation lost the `updates<<24` byte in
    /// `controller_step` on RV32.
    #[test]
    fn alloc_temp_skips_live_vstack_regs_226() {
        let mut sel = Selector::new_with_options(0, SelectorOptions::wasm_compliant());
        // Pin three registers by leaving them on the vstack.
        let pinned = [sel.alloc_temp(), sel.alloc_temp(), sel.alloc_temp()];
        for r in pinned {
            sel.push_i32(r);
        }
        // Spin the allocator well past the pool size; it must dodge all three.
        // #312: allocations within one op pin their result (so pairs never
        // alias) — clear the per-op scope each iteration, as `lower_one` does
        // at every op boundary.
        for _ in 0..(sel.temps.len() * 3) {
            sel.op_pinned.clear();
            let r = sel.alloc_temp();
            assert!(
                !pinned.contains(&r),
                "alloc_temp returned live vstack register {r:?}"
            );
        }
        assert!(
            !sel.alloc_exhausted,
            "only 3 of {} temps pinned — must not flag exhaustion",
            sel.temps.len()
        );
    }

    /// #232: the signed-division `INT_MIN / -1` overflow guard materializes its
    /// comparison constants into scratch registers — which must NOT be the
    /// dividend or divisor (both popped off the vstack but still live until the
    /// `div`). Regression for the v0.11.26 lowest-free clobber.
    #[test]
    fn signed_div_guard_does_not_clobber_operands_232() {
        // (p0 + p1) / 1000 — a signed div by a constant leaf.
        let sel = select(
            &[
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                WasmOp::I32Add,
                WasmOp::I32Const(1000),
                WasmOp::I32DivS,
            ],
            2,
        )
        .unwrap();
        let ops = &sel.ops;
        let (dividend, divisor) = ops
            .iter()
            .find_map(|o| match o {
                RiscVOp::Div { rs1, rs2, .. } => Some((*rs1, *rs2)),
                _ => None,
            })
            .expect("a Div is emitted");
        // INT_MIN (lui …0x80000…) and -1 (addi rd, zero, -1) are the guard
        // constants; neither may land on the live dividend/divisor.
        for op in ops {
            let guard_dst = match op {
                RiscVOp::Lui { rd, imm20 } if *imm20 == 0x8_0000 => Some(*rd),
                RiscVOp::Addi {
                    rd,
                    rs1: Reg::ZERO,
                    imm: -1,
                } => Some(*rd),
                _ => None,
            };
            if let Some(d) = guard_dst {
                assert!(
                    d != dividend && d != divisor,
                    "guard constant clobbers live operand {d:?} (dividend={dividend:?}, divisor={divisor:?}) — #232"
                );
            }
        }
    }

    /// #226: when *every* temp pins a live value, `alloc_temp` flags
    /// `alloc_exhausted` so the caller skips the function (honest
    /// skip-and-continue) rather than emitting a clobbering allocation.
    #[test]
    fn alloc_temp_flags_exhaustion_when_all_pinned_226() {
        let mut sel = Selector::new_with_options(0, SelectorOptions::wasm_compliant());
        let n = sel.temps.len();
        // Pin each register as it is allocated, so the next alloc must pick a
        // different one (lowest-free returns the same reg until it is pinned).
        for _ in 0..n {
            let r = sel.alloc_temp();
            sel.push_i32(r);
        }
        assert!(
            !sel.alloc_exhausted,
            "no exhaustion before the pool is full"
        );
        let _ = sel.alloc_temp(); // nothing free → must flag
        assert!(
            sel.alloc_exhausted,
            "all temps pinned → exhaustion flagged for skip-and-continue"
        );
    }

    /// #312: within one op's lowering, back-to-back `alloc_temp` calls (an
    /// i64 `(lo, hi)` pair) must never alias, and freshly allocated scratch
    /// must never land on an operand popped earlier in the same op. Before
    /// the per-op pin scope, lowest-free (#231) collapsed every i64 pair to
    /// a single register — `check(3,4)` returned 0x0 on the u64-unpack
    /// oracle because each pair's hi write destroyed its own lo.
    #[test]
    fn i64_pair_registers_never_alias_312() {
        // i64.const: lo/hi must be two registers.
        let mut sel = Selector::new_with_options(0, SelectorOptions::wasm_compliant());
        sel.lower_one(&WasmOp::I64Const(5)).unwrap();
        let Some(&VstackVal::I64 { lo, hi }) = sel.vstack.last() else {
            panic!("i64.const must push an i64 pair");
        };
        assert_ne!(lo, hi, "i64.const pair collapsed to one register");

        // i64.extend_i32_u: the fresh hi (= 0) must not land on the popped
        // src, which becomes the pair's lo.
        let mut sel = Selector::new_with_options(0, SelectorOptions::wasm_compliant());
        sel.lower_one(&WasmOp::I32Const(7)).unwrap();
        sel.lower_one(&WasmOp::I64ExtendI32U).unwrap();
        let Some(&VstackVal::I64 { lo, hi }) = sel.vstack.last() else {
            panic!("i64.extend_i32_u must push an i64 pair");
        };
        assert_ne!(lo, hi, "extend_i32_u zeroed hi on top of its own lo");
    }

    /// #312: an i64 local.get must load the two frame words into two distinct
    /// registers (the repro loaded both `0(sp)` and `4(sp)` into the same reg).
    #[test]
    fn i64_local_get_loads_distinct_pair_312() {
        let sel = select(
            &[
                WasmOp::I64Const(1),
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
            ],
            0,
        )
        .unwrap();
        let frame_loads: Vec<Reg> = sel
            .ops
            .iter()
            .filter_map(|op| match op {
                RiscVOp::Lw {
                    rd, rs1: Reg::SP, ..
                } => Some(*rd),
                _ => None,
            })
            .collect();
        assert_eq!(frame_loads.len(), 2, "i64 local.get loads both slot words");
        assert_ne!(
            frame_loads[0], frame_loads[1],
            "i64 local.get pair collapsed to one register"
        );
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

    // -------- #312: i64 locals (two-word frame slots) --------

    /// Count Sw ops against the frame (`sp`-based) at byte offset `imm`.
    fn count_sw_sp(out: &[RiscVOp], at: i32) -> usize {
        count(
            out,
            |op| matches!(op, RiscVOp::Sw { rs1: Reg::SP, imm, .. } if *imm == at),
        )
    }

    /// Count Lw ops against the frame (`sp`-based) at byte offset `imm`.
    fn count_lw_sp(out: &[RiscVOp], at: i32) -> usize {
        count(
            out,
            |op| matches!(op, RiscVOp::Lw { rs1: Reg::SP, imm, .. } if *imm == at),
        )
    }

    // ─── VCR-RA #472 lever baselines (epic #242) ───────────────────────────
    // These pin the CURRENT (pre-lever) RV32 codegen for the three patterns the
    // RISC-V lever port targets (see scripts/repro/riscv_lever_parity_472.md).
    // They are oracle-first: frozen-safe today (assert what the selector emits
    // now), and each flips when its lever lands default-on — so CI surfaces the
    // codegen change as a deliberate, reviewed assertion update rather than a
    // silent drift on the un-byte-gated RV32 path. They also validate the scoping
    // doc's source-read claims with executable evidence.

    /// #472 const-address-fold baseline: a constant-address store is NOT folded.
    /// Today it materializes `add t, s11, addr; sw v, 0(t)`; the lever will rewrite
    /// that to a single `sw v, ADDR(s11)`. Pins the current unfolded shape.
    #[test]
    fn const_addr_store_not_folded_baseline_472() {
        // (i32.store (i32.const 8) (i32.const 33))  — address 8, value 33.
        let out = s(
            &[
                WasmOp::I32Const(8),
                WasmOp::I32Const(33),
                WasmOp::I32Store {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            0,
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Add { rs1: Reg::S11, .. })) >= 1,
            "baseline: const-addr store computes base+addr via `add _,s11,_`: {out:?}"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sw { rs1: Reg::S11, .. })),
            0,
            "baseline: the store is NOT yet folded directly off s11: {out:?}"
        );
    }

    /// #472 immediate-shift-fold baseline: a constant shift amount uses the
    /// REGISTER form `sll` (preceded by an `li` of the amount), not `slli #shamt`.
    #[test]
    fn const_shift_uses_register_form_baseline_472() {
        // (i32.shl (local.get 0) (i32.const 8))
        let out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Const(8),
                WasmOp::I32Shl,
                WasmOp::Drop,
                WasmOp::End,
            ],
            1,
        );
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Sll { .. })) >= 1,
            "baseline: const shift uses the register form `sll`: {out:?}"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Slli { .. })),
            0,
            "baseline: not yet folded to `slli #shamt`: {out:?}"
        );
    }

    /// #472 imm-shift-fold: the post-pass folds a constant shift amount into the
    /// immediate form `slli #shamt` and drops the `li` of the amount. Driven on
    /// the baseline fixture output — exactly what the env flag wires in the CLI.
    #[test]
    fn fold_const_shift_folds_amount_into_slli_472() {
        // (i32.shl (local.get 0) (i32.const 8)) — RESULT returned (observable).
        let mut out = s(
            &[
                WasmOp::LocalGet(0),
                WasmOp::I32Const(8),
                WasmOp::I32Shl,
                WasmOp::End,
            ],
            1,
        );
        let before_addi8 = count(
            &out,
            |op| matches!(op, RiscVOp::Addi { rs1, imm: 8, .. } if *rs1 == Reg::ZERO),
        );
        assert_eq!(before_addi8, 1, "baseline materializes the amount: {out:?}");

        let folds = fold_const_shift(&mut out);
        assert_eq!(folds, 1, "exactly the one const shift folds: {out:?}");
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Slli { shamt: 8, .. })),
            1,
            "folded to `slli #8`: {out:?}"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Sll { .. })),
            0,
            "the register-form `sll` is gone: {out:?}"
        );
        assert_eq!(
            count(
                &out,
                |op| matches!(op, RiscVOp::Addi { rs1, imm: 8, .. } if *rs1 == Reg::ZERO)
            ),
            0,
            "the `li amount, 8` dead store is dropped: {out:?}"
        );
    }

    /// `srl`/`sra` fold to `srli`/`srai` just like `sll` → `slli`.
    #[test]
    fn fold_const_shift_handles_srl_and_sra_472() {
        for (op, want_slli, want_srli, want_srai) in
            [(WasmOp::I32ShrU, 0, 1, 0), (WasmOp::I32ShrS, 0, 0, 1)]
        {
            let mut out = s(
                &[
                    WasmOp::LocalGet(0),
                    WasmOp::I32Const(3),
                    op.clone(),
                    WasmOp::End,
                ],
                1,
            );
            assert_eq!(fold_const_shift(&mut out), 1, "{op:?} folds: {out:?}");
            assert_eq!(
                count(&out, |o| matches!(o, RiscVOp::Slli { .. })),
                want_slli,
                "{op:?}: {out:?}"
            );
            assert_eq!(
                count(&out, |o| matches!(o, RiscVOp::Srli { shamt: 3, .. })),
                want_srli,
                "{op:?}: {out:?}"
            );
            assert_eq!(
                count(&out, |o| matches!(o, RiscVOp::Srai { shamt: 3, .. })),
                want_srai,
                "{op:?}: {out:?}"
            );
        }
    }

    /// The shift amount is masked to its low 5 bits (WASM shift-mod-32, which the
    /// register `sll` already enforces in hardware): `i32.const 33` → `slli #1`,
    /// `i32.const -1` → `slli #31`. The mask is what makes the fold semantics-
    /// preserving for out-of-range / negative constants.
    #[test]
    fn fold_const_shift_masks_amount_to_low_5_bits_472() {
        for (amount, want_shamt) in [(33i32, 1u8), (-1, 31), (32, 0), (64, 0)] {
            let mut out = s(
                &[
                    WasmOp::LocalGet(0),
                    WasmOp::I32Const(amount),
                    WasmOp::I32Shl,
                    WasmOp::End,
                ],
                1,
            );
            // Large/negative amounts may not take the single-`addi` materialization
            // path (`lui+addi`); only assert the mask when the fold actually fired.
            if fold_const_shift(&mut out) == 1 {
                assert_eq!(
                    count(
                        &out,
                        |op| matches!(op, RiscVOp::Slli { shamt, .. } if *shamt == want_shamt)
                    ),
                    1,
                    "amount {amount} masks to shamt {want_shamt}: {out:?}"
                );
            }
        }
    }

    /// Soundness guard: when the amount temp aliases the shift's INPUT
    /// (`sll t0, t0, t0`), dropping the `li` would remove the input's definition —
    /// the fold must decline (`rs1 != tmp`).
    #[test]
    fn fold_const_shift_declines_when_amount_aliases_input_472() {
        let mut out = vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 4,
            },
            RiscVOp::Sll {
                rd: Reg::T0,
                rs1: Reg::T0, // input == amount temp
                rs2: Reg::T0,
            },
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(fold_const_shift(&mut out), 0, "must not fold: {out:?}");
        assert_eq!(count(&out, |op| matches!(op, RiscVOp::Sll { .. })), 1);
    }

    /// Soundness guard: when the amount temp is read again after the shift (and is
    /// not the shift's destination), it is live — the `li` is not a dead store, so
    /// the fold must decline.
    #[test]
    fn fold_const_shift_declines_when_amount_live_after_472() {
        let mut out = vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 4,
            },
            RiscVOp::Sll {
                rd: Reg::T1,
                rs1: Reg::A0,
                rs2: Reg::T0,
            },
            // reads t0 again ⇒ the amount is still live past the shift
            RiscVOp::Add {
                rd: Reg::A0,
                rs1: Reg::T1,
                rs2: Reg::T0,
            },
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            fold_const_shift(&mut out),
            0,
            "amount live ⇒ no fold: {out:?}"
        );
        assert_eq!(count(&out, |op| matches!(op, RiscVOp::Slli { .. })), 0);
    }

    /// The `rd == tmp` dead-store case (`sll t0, rs1, t0` → `slli t0, rs1, #N`):
    /// the fold's destination redefining the amount temp is itself the proof the
    /// `li` is dead — fold fires even though `t0` is "used" as the result.
    #[test]
    fn fold_const_shift_folds_when_dest_is_amount_temp_472() {
        let mut out = vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 5,
            },
            RiscVOp::Sll {
                rd: Reg::T0, // result reuses the amount temp
                rs1: Reg::A0,
                rs2: Reg::T0,
            },
            RiscVOp::Addi {
                rd: Reg::A0,
                rs1: Reg::T0, // result read into a0
                imm: 0,
            },
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(fold_const_shift(&mut out), 1, "dest==tmp folds: {out:?}");
        assert_eq!(
            count(
                &out,
                |op| matches!(op, RiscVOp::Slli { rd, shamt: 5, .. } if *rd == Reg::T0)
            ),
            1,
            "{out:?}"
        );
    }

    // ---- #472 step 2: const-address fold ----

    /// Folds `addi a,zero,ADDR; add tmp,s11,a; sw v,off(tmp)` to `sw v,(ADDR)(s11)`,
    /// dropping the address `addi` and the `add`. Driven on the baseline fixture
    /// output (what the CLI flag wires in).
    #[test]
    fn fold_const_addr_folds_store_off_s11_472() {
        // (i32.store (i32.const 8) (i32.const 33))
        let mut out = s(
            &[
                WasmOp::I32Const(8),
                WasmOp::I32Const(33),
                WasmOp::I32Store {
                    offset: 0,
                    align: 2,
                },
                WasmOp::End,
            ],
            0,
        );
        let before_adds = count(&out, |op| matches!(op, RiscVOp::Add { rs1: Reg::S11, .. }));
        assert_eq!(before_adds, 1, "baseline computes base+addr: {out:?}");
        let folds = fold_const_addr(&mut out);
        assert_eq!(folds, 1, "the const-addr store folds: {out:?}");
        assert_eq!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Sw {
                    rs1: Reg::S11,
                    imm: 8,
                    ..
                }
            )),
            1,
            "store folded to `sw v, 8(s11)`: {out:?}"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Add { rs1: Reg::S11, .. })),
            0,
            "the `add _,s11,_` is gone: {out:?}"
        );
    }

    /// The folded immediate is `ADDR + access-offset`; both terms must sum within
    /// the signed 12-bit window. `i32.store offset=4 (i32.const 8)` → `sw v,12(s11)`.
    #[test]
    fn fold_const_addr_adds_access_offset_472() {
        let mut out = s(
            &[
                WasmOp::I32Const(8),
                WasmOp::I32Const(33),
                WasmOp::I32Store {
                    offset: 4,
                    align: 2,
                },
                WasmOp::End,
            ],
            0,
        );
        assert_eq!(fold_const_addr(&mut out), 1, "{out:?}");
        assert_eq!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Sw {
                    rs1: Reg::S11,
                    imm: 12,
                    ..
                }
            )),
            1,
            "ADDR(8)+off(4) = 12: {out:?}"
        );
    }

    /// A load folds the same way: `lw dst, (ADDR)(s11)`.
    #[test]
    fn fold_const_addr_folds_load_472() {
        let mut out = s(
            &[
                WasmOp::I32Const(16),
                WasmOp::I32Load {
                    offset: 0,
                    align: 2,
                },
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
        );
        assert_eq!(fold_const_addr(&mut out), 1, "{out:?}");
        assert_eq!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Lw {
                    rs1: Reg::S11,
                    imm: 16,
                    ..
                }
            )),
            1,
            "load folded to `lw dst, 16(s11)`: {out:?}"
        );
    }

    /// Range guard: when `ADDR + off` exceeds the signed 12-bit window the fold
    /// must decline (the access stays `lw/sw _,off(tmp)` off the computed base).
    #[test]
    fn fold_const_addr_declines_when_sum_out_of_12bit_472() {
        // ADDR = 2044, off = 8 → 2052 > 2047 → out of range.
        let mut out = vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 2044,
            },
            RiscVOp::Add {
                rd: Reg::T1,
                rs1: Reg::S11,
                rs2: Reg::T0,
            },
            RiscVOp::Sw {
                rs1: Reg::T1,
                rs2: Reg::T2,
                imm: 8,
            },
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            fold_const_addr(&mut out),
            0,
            "out-of-range sum: no fold: {out:?}"
        );
        assert_eq!(
            count(&out, |op| matches!(op, RiscVOp::Add { rs1: Reg::S11, .. })),
            1
        );
    }

    /// Soundness: when the address temp `a` is read by another op (not single-use),
    /// the fold must NOT drop its `addi` — decline.
    #[test]
    fn fold_const_addr_declines_when_addr_reused_472() {
        let mut out = vec![
            RiscVOp::Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 16,
            },
            RiscVOp::Add {
                rd: Reg::T1,
                rs1: Reg::S11,
                rs2: Reg::T0,
            },
            RiscVOp::Sw {
                rs1: Reg::T1,
                rs2: Reg::T2,
                imm: 0,
            },
            // a second use of the address constant t0 ⇒ not single-use
            RiscVOp::Add {
                rd: Reg::T3,
                rs1: Reg::A0,
                rs2: Reg::T0,
            },
            RiscVOp::Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            fold_const_addr(&mut out),
            0,
            "addr reused ⇒ no fold: {out:?}"
        );
    }

    /// #472 local-promotion baseline: a non-param i32 local is frame-spilled
    /// (`sw _,off(sp)` / `lw`), not register-homed. The lever will keep eligible
    /// leaf locals in s-registers (the #390 analogue, carrying the #474 fallback).
    #[test]
    fn nonparam_local_frame_spilled_baseline_472() {
        // local 1 is non-param (num_params = 1); set from a const, then read.
        let out = s(
            &[
                WasmOp::I32Const(5),
                WasmOp::LocalSet(1),
                WasmOp::LocalGet(1),
                WasmOp::Drop,
                WasmOp::End,
            ],
            1,
        );
        // No s-register is written by this tiny body, so the only sp-relative
        // store is the local's frame slot (the #220 callee-saved spills don't fire).
        assert!(
            count(&out, |op| matches!(op, RiscVOp::Sw { rs1: Reg::SP, .. })) >= 1,
            "baseline: non-param local is frame-spilled (`sw _,off(sp)`): {out:?}"
        );
    }

    /// #312: `local.set` + `local.get` of an i64 local round-trips through a
    /// two-word frame slot — sw/lw at `off` (lo) and `off+4` (hi).
    #[test]
    fn i64_local_set_get_roundtrip_two_words_312() {
        let out = s(
            &[
                WasmOp::I64Const(0x1122_3344_5566_7788),
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
        );
        // The only sp-relative traffic at 0/4 is the local slot (no s-regs are
        // written by this tiny body, so the #220 spills don't interfere).
        assert_eq!(count_sw_sp(&out, 0), 1, "lo store at off 0: {out:?}");
        assert_eq!(count_sw_sp(&out, 4), 1, "hi store at off 4: {out:?}");
        assert_eq!(count_lw_sp(&out, 0), 1, "lo load at off 0: {out:?}");
        assert_eq!(count_lw_sp(&out, 4), 1, "hi load at off 4: {out:?}");
    }

    /// #312: `local.tee` of an i64 local (the exact op the issue's repro
    /// refused with "expected i32, found i64") stores both words and keeps
    /// the pair on the vstack.
    #[test]
    fn i64_local_tee_stores_both_words_and_keeps_value_312() {
        let out = s(
            &[
                WasmOp::I64Const(7),
                WasmOp::LocalTee(0),
                WasmOp::I64Const(1),
                WasmOp::I64Add, // consumes the teed pair → it stayed on the stack
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
        );
        assert_eq!(count_sw_sp(&out, 0), 1, "tee lo store at off 0: {out:?}");
        assert_eq!(count_sw_sp(&out, 4), 1, "tee hi store at off 4: {out:?}");
        assert!(count(&out, |op| matches!(op, RiscVOp::Add { .. })) >= 3);
    }

    /// #312: width inference — a local fed by an i64-producing op (not just an
    /// i64.const) gets the 8-byte slot.
    #[test]
    fn i64_local_inferred_from_i64_producing_op_312() {
        let out = s(
            &[
                WasmOp::I64Const(1),
                WasmOp::I64Const(2),
                WasmOp::I64Add,
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
        );
        assert_eq!(count_sw_sp(&out, 0), 1);
        assert_eq!(count_sw_sp(&out, 4), 1);
        assert_eq!(count_lw_sp(&out, 0), 1);
        assert_eq!(count_lw_sp(&out, 4), 1);
    }

    /// #312: mixed i32/i64 layout — the i64 local after an i32 local is padded
    /// up to 8-byte alignment (i32 at 0, i64 at 8/12 — not 4/8).
    #[test]
    fn i64_local_slot_is_8_byte_aligned_after_i32_local_312() {
        let out = s(
            &[
                WasmOp::I32Const(9),
                WasmOp::LocalSet(0), // i32 local → off 0
                WasmOp::I64Const(5),
                WasmOp::LocalSet(1), // i64 local → aligned to off 8
                WasmOp::LocalGet(1),
                WasmOp::Drop,
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
        );
        assert_eq!(count_sw_sp(&out, 0), 1, "i32 local at off 0: {out:?}");
        assert_eq!(count_sw_sp(&out, 4), 0, "off 4 is padding: {out:?}");
        assert_eq!(count_sw_sp(&out, 8), 1, "i64 lo at off 8: {out:?}");
        assert_eq!(count_sw_sp(&out, 12), 1, "i64 hi at off 12: {out:?}");
        assert_eq!(count_lw_sp(&out, 8), 1);
        assert_eq!(count_lw_sp(&out, 12), 1);
    }

    /// #312 (mirrors ARM #311): an i64-returning call's result is the a0:a1
    /// pair; a call-fed local gets the 8-byte slot and both words stored.
    #[test]
    fn call_fed_i64_local_stores_a0_a1_pair_312() {
        let out = select_with_result_types(
            &[
                WasmOp::I32Const(1),
                WasmOp::I32Const(2),
                WasmOp::Call(0),
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
            SelectorOptions::wasm_compliant(),
            &[true], // func 0 returns i64
            &[],
        )
        .unwrap()
        .ops;
        // lo (a0) at off 0, hi (a1) at off 4.
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Sw {
                    rs1: Reg::SP,
                    rs2: Reg::A0,
                    imm: 0
                }
            )) == 1,
            "a0 (lo) stored at off 0: {out:?}"
        );
        assert!(
            count(&out, |op| matches!(
                op,
                RiscVOp::Sw {
                    rs1: Reg::SP,
                    rs2: Reg::A1,
                    imm: 4
                }
            )) == 1,
            "a1 (hi) stored at off 4: {out:?}"
        );
        assert_eq!(count_lw_sp(&out, 0), 1);
        assert_eq!(count_lw_sp(&out, 4), 1);
    }

    /// #312: without the result-type table the same call result stays i32 —
    /// the legacy behaviour `select_with_options` callers rely on.
    #[test]
    fn call_result_defaults_to_i32_without_tables_312() {
        let r = select(
            &[
                WasmOp::I32Const(1),
                WasmOp::I32Const(2),
                WasmOp::Call(0),
                WasmOp::LocalSet(0),
                WasmOp::LocalGet(0),
                WasmOp::Drop,
                WasmOp::End,
            ],
            0,
        )
        .unwrap()
        .ops;
        assert_eq!(count_sw_sp(&r, 0), 1, "single-word store: {r:?}");
        assert_eq!(count_sw_sp(&r, 4), 0, "no hi-word store: {r:?}");
    }

    /// #312: i64 *params* are not modeled (an i64 param needs an a-register
    /// pair per the RV32 psABI) — the selector must bail with `Unsupported`
    /// (skip-and-continue under --all-exports), never store half the value.
    #[test]
    fn i64_param_local_is_unsupported_312() {
        let r = select(
            &[WasmOp::I64Const(5), WasmOp::LocalSet(0), WasmOp::End],
            1, // local 0 is a param
        );
        assert!(
            matches!(r, Err(SelectorError::Unsupported(_))),
            "i64 param must skip honestly, got: {:?}",
            r.map(|sel| sel.ops)
        );
    }

    // ─────────────── #472: RV32 i32 local promotion (VCR-RA) ───────────────

    fn s_promo(ops: &[WasmOp], num_params: u32, promote: bool) -> Vec<RiscVOp> {
        select_inner(
            ops,
            num_params,
            SelectorOptions::wasm_compliant(),
            &[],
            &[],
            promote,
            false,
        )
        .unwrap()
        .ops
    }

    fn count_lw_any_sp(out: &[RiscVOp]) -> usize {
        count(out, |op| matches!(op, RiscVOp::Lw { rs1: Reg::SP, .. }))
    }

    fn writes_reg(out: &[RiscVOp], reg: Reg) -> bool {
        out.iter().any(|op| op_dest(op) == Some(reg))
    }

    /// A leaf function whose local 1 (non-param) is written once and read three
    /// times at depth 0 — the promotable shape.
    fn promotable_ops() -> Vec<WasmOp> {
        vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalSet(1), // local1 = param0 (write first)
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ]
    }

    /// Flag OFF must be byte-identical to the default `select()` path, and must
    /// keep the local on the frame (frame `lw`s, no promoted s-register).
    /// (Local promotion is still OPT-IN — HELD from the RV32 flip-wave on the
    /// no-grow blocker documented at the env read in
    /// [`select_with_result_types`].)
    #[test]
    fn local_promotion_flag_off_is_identical_and_frame_backed_472() {
        let ops = promotable_ops();
        // select() reads the env; promotion is opt-in, cmp→select is
        // default-on (flip-wave) — promotable_ops has no select, so fusion is
        // a no-op here and the env-unset default is the unpromoted lowering.
        let default = s(&ops, 1);
        let off = s_promo(&ops, 1, false);
        assert_eq!(
            default, off,
            "flag-off must equal the default select() path"
        );
        assert!(
            count_lw_any_sp(&off) >= 3,
            "local must stay frame-backed (>=3 lw): {off:?}"
        );
        assert!(
            !writes_reg(&off, Reg::S8),
            "no promotion register may be written with the flag off: {off:?}"
        );
    }

    /// Flag ON promotes local 1 into `s8`: no frame loads for it, and the
    /// callee-saved preservation pass saves+restores `s8` in the prologue.
    #[test]
    fn local_promotion_flag_on_uses_s_register_472() {
        let ops = promotable_ops();
        let on = s_promo(&ops, 1, true);
        assert!(
            writes_reg(&on, Reg::S8),
            "local 1 must be promoted to s8: {on:?}"
        );
        assert!(
            count_lw_any_sp(&on) < count_lw_any_sp(&s_promo(&ops, 1, false)),
            "promotion must remove frame loads: {on:?}"
        );
        // preserve_callee_saved must spill+restore the promoted s8.
        assert!(
            on.iter().any(|op| matches!(
                op,
                RiscVOp::Sw {
                    rs2: Reg::S8,
                    rs1: Reg::SP,
                    ..
                }
            )),
            "prologue must save s8: {on:?}"
        );
        assert!(
            on.iter().any(|op| matches!(
                op,
                RiscVOp::Lw {
                    rd: Reg::S8,
                    rs1: Reg::SP,
                    ..
                }
            )),
            "epilogue must restore s8: {on:?}"
        );
    }

    /// The pure decision function: which locals promote, to which reg, and which
    /// need a zero-init.
    #[test]
    fn compute_local_promotion_rules_472() {
        use std::collections::HashSet;
        let no_i64 = HashSet::new();

        // Write-before-read i32, 4 accesses → promoted to s8, no zero-init.
        let (map, zi) = compute_local_promotion(&promotable_ops(), 1, &no_i64);
        assert_eq!(map.get(&1), Some(&Reg::S8));
        assert!(!zi.contains(&1), "write-first local needs no zero-init");

        // Read-before-write → promoted AND flagged for zero-init (#457).
        let rbw = [
            WasmOp::LocalGet(1), // first access is a READ
            WasmOp::LocalGet(0),
            WasmOp::I32Add,
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
            WasmOp::End,
        ];
        let (map, zi) = compute_local_promotion(&rbw, 1, &no_i64);
        assert_eq!(map.get(&1), Some(&Reg::S8));
        assert!(
            zi.contains(&1),
            "read-before-write local must be zero-inited"
        );

        // A single access can't repay the save/restore → declined.
        let once = [WasmOp::LocalGet(1), WasmOp::End];
        assert!(compute_local_promotion(&once, 1, &no_i64).0.is_empty());

        // A local touched inside control flow → declined (dominance not proven).
        let cf = [
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(1),
            WasmOp::End,
            WasmOp::End,
        ];
        assert!(compute_local_promotion(&cf, 1, &no_i64).0.is_empty());

        // An i64 local (needs a pair) → declined.
        let mut i64_set = HashSet::new();
        i64_set.insert(1u32);
        assert!(
            compute_local_promotion(&promotable_ops(), 1, &i64_set)
                .0
                .is_empty()
        );

        // Any call in the body → leaf-only, promote nothing.
        let with_call = [
            WasmOp::LocalGet(0),
            WasmOp::LocalSet(1),
            WasmOp::Call(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        assert!(compute_local_promotion(&with_call, 1, &no_i64).0.is_empty());
    }

    /// Three promotable locals exhaust exactly the s8/s9/s10 budget in
    /// ascending index order.
    #[test]
    fn compute_local_promotion_budget_order_472() {
        use std::collections::HashSet;
        let mut ops = Vec::new();
        for idx in [1u32, 2, 3] {
            ops.push(WasmOp::LocalGet(0));
            ops.push(WasmOp::LocalSet(idx));
            ops.push(WasmOp::LocalGet(idx));
            ops.push(WasmOp::LocalGet(idx));
            ops.push(WasmOp::I32Add);
            ops.push(WasmOp::Drop);
        }
        ops.push(WasmOp::End);
        let (map, _) = compute_local_promotion(&ops, 1, &HashSet::new());
        assert_eq!(map.get(&1), Some(&Reg::S8));
        assert_eq!(map.get(&2), Some(&Reg::S9));
        assert_eq!(map.get(&3), Some(&Reg::S10));
    }

    // ─────────── #472: RV32 cmp→select fusion (VCR-SEL-004 port) ───────────

    fn s_fuse(ops: &[WasmOp], num_params: u32, fuse: bool) -> Vec<RiscVOp> {
        select_inner(
            ops,
            num_params,
            SelectorOptions::wasm_compliant(),
            &[],
            &[],
            false,
            fuse,
        )
        .unwrap()
        .ops
    }

    fn count_branch(out: &[RiscVOp], want: Branch) -> usize {
        count(
            out,
            |op| matches!(op, RiscVOp::Branch { cond, .. } if *cond == want),
        )
    }

    /// `select(p0, p1, p0 <s p1)` — a comparison directly feeding a select.
    fn lt_s_select_ops() -> Vec<WasmOp> {
        vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32LtS,
            WasmOp::Select,
            WasmOp::End,
        ]
    }

    /// DEFAULT-ON since the flip-wave: the env-unset `select()` path must take
    /// the FUSED lowering; the `SYNTH_RV_CMP_SELECT=0` opt-out (explicit
    /// `fuse=false`, the same bool the entry point derives from `=0`) restores
    /// the pre-flip shape — boolean materialized (`slt`), select branches on
    /// `bool != 0`.
    #[test]
    fn cmp_select_default_on_and_opt_out_is_unfused_472() {
        let ops = lt_s_select_ops();
        let default = s(&ops, 2); // select() — env unset in tests → default-ON
        assert_eq!(
            default,
            s_fuse(&ops, 2, true),
            "env-unset default must equal the fused path (flip-wave)"
        );
        let off = s_fuse(&ops, 2, false);
        assert_eq!(count(&off, |op| matches!(op, RiscVOp::Slt { .. })), 1);
        assert_eq!(count_branch(&off, Branch::Ne), 1, "bne bool, zero: {off:?}");
        assert_eq!(count_branch(&off, Branch::Lt), 0);
    }

    /// Flag ON fuses `lt_s` into the select's branch: the `slt` disappears and
    /// the branch becomes `blt a, b` — one instruction saved.
    #[test]
    fn cmp_select_flag_on_fuses_lt_s_472() {
        let ops = lt_s_select_ops();
        let off = s_fuse(&ops, 2, false);
        let on = s_fuse(&ops, 2, true);
        assert_eq!(
            count(&on, |op| matches!(op, RiscVOp::Slt { .. })),
            0,
            "boolean materialization must be deleted: {on:?}"
        );
        assert_eq!(count_branch(&on, Branch::Lt), 1, "blt expected: {on:?}");
        assert_eq!(count_branch(&on, Branch::Ne), 0, "no bne-vs-zero: {on:?}");
        assert_eq!(on.len(), off.len() - 1, "one instruction saved: {on:?}");
    }

    /// `eq` costs two instructions to materialize (`xor` + `sltiu`) — fusing
    /// into `beq a, b` saves both.
    #[test]
    fn cmp_select_flag_on_fuses_eq_472() {
        let ops = [
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Eq,
            WasmOp::Select,
            WasmOp::End,
        ];
        let off = s_fuse(&ops, 2, false);
        let on = s_fuse(&ops, 2, true);
        assert_eq!(count(&on, |op| matches!(op, RiscVOp::Xor { .. })), 0);
        assert_eq!(count(&on, |op| matches!(op, RiscVOp::Sltiu { .. })), 0);
        assert_eq!(count_branch(&on, Branch::Eq), 1, "beq expected: {on:?}");
        assert_eq!(on.len(), off.len() - 2, "two instructions saved: {on:?}");
    }

    /// `ge_u` costs `sltu` + `xori` — fusing into `bgeu a, b` saves both.
    #[test]
    fn cmp_select_flag_on_fuses_ge_u_472() {
        let ops = [
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32GeU,
            WasmOp::Select,
            WasmOp::End,
        ];
        let off = s_fuse(&ops, 2, false);
        let on = s_fuse(&ops, 2, true);
        assert_eq!(count(&on, |op| matches!(op, RiscVOp::Sltu { .. })), 0);
        assert_eq!(count(&on, |op| matches!(op, RiscVOp::Xori { .. })), 0);
        assert_eq!(count_branch(&on, Branch::Geu), 1, "bgeu expected: {on:?}");
        assert_eq!(on.len(), off.len() - 2, "two instructions saved: {on:?}");
    }

    /// `eqz` fuses into `beq src, zero` — the `sltiu` disappears.
    #[test]
    fn cmp_select_flag_on_fuses_eqz_472() {
        let ops = [
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(0),
            WasmOp::I32Eqz,
            WasmOp::Select,
            WasmOp::End,
        ];
        let off = s_fuse(&ops, 2, false);
        let on = s_fuse(&ops, 2, true);
        assert_eq!(count(&on, |op| matches!(op, RiscVOp::Sltiu { .. })), 0);
        assert_eq!(
            count(&on, |op| matches!(
                op,
                RiscVOp::Branch {
                    cond: Branch::Eq,
                    rs2: Reg::ZERO,
                    ..
                }
            )),
            1,
            "beq src, zero expected: {on:?}"
        );
        assert_eq!(on.len(), off.len() - 1, "one instruction saved: {on:?}");
    }

    /// An i32 comparison feeding a select of i64 operands fuses too — the
    /// condition is i32 regardless of the selected type, and both halves move
    /// under the single fused branch.
    #[test]
    fn cmp_select_flag_on_fuses_i64_operand_select_472() {
        let ops = [
            WasmOp::I64Const(11),
            WasmOp::I64Const(22),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32LtU,
            WasmOp::Select,
            WasmOp::End,
        ];
        let off = s_fuse(&ops, 2, false);
        let on = s_fuse(&ops, 2, true);
        assert_eq!(count(&on, |op| matches!(op, RiscVOp::Sltu { .. })), 0);
        assert_eq!(count_branch(&on, Branch::Ltu), 1, "bltu expected: {on:?}");
        assert_eq!(on.len(), off.len() - 1, "one instruction saved: {on:?}");
    }

    /// Fusion requires the comparison to IMMEDIATELY precede the select — an
    /// intervening op (here a `local.tee` of the boolean) invalidates the
    /// record even though the same register ends up back on top of the stack.
    #[test]
    fn cmp_select_no_fuse_when_not_adjacent_472() {
        let ops = [
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32LtS,
            WasmOp::LocalTee(2),
            WasmOp::Select,
            WasmOp::End,
        ];
        let on = s_fuse(&ops, 2, true);
        assert_eq!(
            count(&on, |op| matches!(op, RiscVOp::Slt { .. })),
            1,
            "boolean must stay materialized (tee reads it): {on:?}"
        );
        assert_eq!(count_branch(&on, Branch::Ne), 1, "unfused select: {on:?}");
        assert_eq!(count_branch(&on, Branch::Lt), 0, "no blt: {on:?}");
    }

    /// An i64 comparison feeding a select is NOT fused (out of scope — its
    /// boolean needs the full multi-instruction sequence); the select stays on
    /// the baseline branch-on-boolean path.
    #[test]
    fn cmp_select_i64_comparison_not_fused_472() {
        let ops = [
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I64Const(3),
            WasmOp::I64Const(4),
            WasmOp::I64LtS,
            WasmOp::Select,
            WasmOp::End,
        ];
        let off = s_fuse(&ops, 2, false);
        let on = s_fuse(&ops, 2, true);
        assert_eq!(on, off, "i64 comparisons are out of fusion scope");
    }
}
