//! AArch64 instruction selector — #538 integer subset (milestone 2).
//!
//! A straight-line stack-machine lowering for the integer core: parameters
//! arrive in `w0/x0..w7/x7` (AAPCS64), values live in a small register
//! value-stack, and the function result is moved to `x0` before `ret`. Anything
//! outside the subset returns `Unsupported` — an honest loud-skip (the
//! RISC-V-skeleton contract), never silent wrong code.
//!
//! **Milestone 2 broadens the covered ops** from the m1 i32
//! add/sub/mul/and/or/xor core to the full i32 AND i64 integer ALU:
//!
//! - i64 add/sub/mul/and/or/xor + i64.const (A64 is natively 64-bit, so these
//!   are one `x`-form instruction each; the value stack holds architectural
//!   register numbers, width-agnostic, and the width comes from the op).
//! - i32/i64 shifts (`shl`/`shr_u`/`shr_s`) and rotates (`rotr`, and `rotl` via
//!   `neg`+`rorv`) — the register-shift forms mask the amount mod 32/64,
//!   matching WASM's shift/rotate-count semantics exactly.
//! - i32/i64 `clz`, and `ctz` (`rbit`+`clz`).
//! - the full i32/i64 compare family (`eq/ne/lt/gt/le/ge` signed+unsigned) and
//!   `eqz`, lowered to `cmp` + `cset`.
//!
//! **Shipped since #851:** `div_s/div_u/rem_s/rem_u` (i32+i64, with the ÷0 and
//! signed-`INT_MIN÷-1` WASM trap guards A64's total `SDIV`/`UDIV` omit — the
//! "more-total-than-WASM" class is guarded, not naive), `popcnt` (SIMD
//! `CNT`+`ADDV`), f64↔i64 reinterpret, linear-memory load/store, non-param
//! locals, direct `call`, and full control flow (`if`/`else`/`loop`/`return`).
//! The VCR-SEL-005 third-backend enumeration (#851, v0.53) then closed:
//! `select` (branchless `CSEL`/`FCSEL`, both register files), `drop`/`nop`,
//! `i32.wrap_i64`, `i64.extend_i32_{s,u}`, the five in-place sign extensions
//! (`i32/i64.extend8/16/32_s` — `SXTB`/`SXTH`/`SXTW`), and fixed-memory
//! `memory.size`/`memory.grow` (declared-min page count / branchless
//! `grow(0)≡size`, `grow(n>0)`→−1, the #539 rule — growth failure is
//! §-permitted and keeps the #865 static bounds limit sound).
//!
//! **Deliberately still declined (loud-skip, never wrong code) — the
//! mechanically-derived complement lives in the cross-backend op-parity oracle
//! (`crates/synth-backend-riscv/tests/cross_backend_op_parity.rs`, aarch64
//! leg):**
//! - import calls, `>8` integer args, multi-result or float-result callees
//!   (returned in v0/d0, not x0), and a live value-stack temp across a `call`.
//! - register spilling and bulk memory (`memory.copy`/`memory.fill`).
//! - Float rounding (`ceil`/`floor`/`trunc`/`nearest`), f32/f64 linear-memory
//!   load/store, i64→float converts, and the TRAPPING i64-target truncations
//!   (the saturating forms do lower).
//! - Data-segment init and the startup that establishes the `x28` linear-memory
//!   base (the load/store lowering is correct given the base precondition;
//!   wiring it at runtime is a follow-on). OOB accesses TRAP since #865 under
//!   [`MemBounds::Software`] (the CLI default); `--safety-bounds none` is the
//!   explicit unchecked opt-out.
//!
//! **#851 — non-param locals:** GP locals beyond the params (index >=
//! `num_params`) get zero-initialized 8-byte stack slots (`[sp, #(idx -
//! num_params)*8]`, frame rounded to a 16-byte SP-aligned multiple), only when
//! the function actually declares one. `local.get` LOADS the slot into a fresh
//! temp (copy-semantics — a later `local.set` of the same index cannot alias a
//! stacked value), `local.set`/`local.tee` store it (tee without popping).
//! 64-bit slots preserve both i32 and i64. Still declined here: FP non-param
//! locals (their types are not threaded to the backend, so an FP `local.set` is
//! caught by the GP file-check and declined).
//!
//! **RQ-57-A64PARAM (#851) — PARAM HOMING.** A function that CALLS (v0.54 lane
//! L3) or WRITES a parameter (this increment) gives EVERY local — params
//! included — an 8-byte slot at `[sp, #idx*8]`; the prologue stores each
//! incoming argument register into its slot, and every `local.get` becomes a
//! `ldr` into a fresh temp. That is what makes `local.set`/`local.tee` on a
//! param index lower at all: the write has a durable home, and because reads
//! are copies it cannot alias a value the stack already holds — the exact
//! hazard the old decline was protecting against, now structurally impossible.
//! `writes_param` is a subset of `references_param`, so this changes behaviour
//! for exactly one class (leaf functions that write a param, all of which
//! declined before); non-leaf homing is byte-identical.
//!
//! Declined here: a homing function that declares a FLOAT param — the slot
//! model is single-register-file, so a v-register param would be stored and
//! reloaded as a GP register (named follow-up: thread the per-local file).
//!
//! **Milestone 3 adds scalar floating point** (the separate V/D/S register file):
//! f32/f64 const, add/sub/mul/div, abs/neg/sqrt, the full compare family, the
//! f32<->f64 conversions (promote/demote), the int->float conversions
//! (`convert_i32_{s,u}` → SCVTF/UCVTF), and the reinterprets (FMOV GP<->FP).
//! The value stack now tags each entry with its register FILE (GP vs FP) so an
//! f32 param (delivered in `s0..` under AAPCS64, a counter INDEPENDENT of the
//! GP arg registers) is never confused with a GP operand.
//!
//! **VCR-A64-CF-001 (v0.55) — `br_table` + VALUE-CARRYING control flow.** The
//! two largest entries in the mechanically-derived decline complement:
//!
//! - `br_table` lowers as a COMPARE-AND-BRANCH CHAIN (`cbz` for entry 0, then
//!   `cmp`+`b.eq` per further entry, then an unconditional `b` to the default),
//!   deliberately the same construction #882 chose for RV32. The index is
//!   compared in the W view, so the UNSIGNED index semantics hold exactly:
//!   only `0..len-1` match and every other index — including the "negative"
//!   i32s that denote huge unsigned values — reaches the DEFAULT. One table may
//!   MIX a backward loop header with forward block ends.
//! - A VALUE-CARRYING `block`/`loop`/`if` reserves a reconciliation register
//!   pair (one GP, one FP — the arity side-table carries counts only, so the
//!   result's register FILE is not known at frame entry) that is withheld from
//!   the temp allocator for the frame's whole extent. Every edge into the
//!   frame's join deposits there, so the result is in ONE register on every
//!   path. See [`reconcile_into`] for why no clobber window exists.
//!
//! SOUNDNESS-CRITICAL: a `br` to a LOOP label targets the loop HEADER and
//! carries the loop's PARAMETERS, not its results, so a `loop (result T)`
//! back-edge reconciles NOTHING (`Frame::label_arity` vs `Frame::result_arity`).
//! Still declined by name: a `br_table` past [`BR_TABLE_MAX_TARGETS`], a
//! `br_table` with value-carrying targets, and a block type with PARAMETERS or
//! MULTI-VALUE results.
//!
//! **Milestone 4 converts the #709-class declines into SOUND capabilities:**
//!
//! - The trapping float→int truncations (`i32.trunc_f32_{s,u}`,
//!   `i32.trunc_f64_{s,u}`): A64 `FCVTZS`/`FCVTZU` SATURATE on out-of-range/NaN
//!   whereas WASM traps (§4.3.3) — the #709 "more-total-than-WASM" silent
//!   miscompile class. m4 lowers them with an EXPLICIT domain guard (the A64
//!   twin of the Thumb-2 `f32_trunc_range_guard`): `fcmp` against the exact
//!   WASM boundary constant, an ORDERED `b.cond` that skips a `brk #0` only
//!   when the operand is proven in-range (NaN fails every ordered condition ⇒
//!   falls into the trap), then the saturating convert on the proven-in-range
//!   path where the two semantics agree.
//! - `f32/f64.min/max`: A64 `FMIN`/`FMAX` (NOT `FMINNM`/`FMAXNM`) implement
//!   IEEE 754-2019 minimum/maximum — either-NaN ⇒ NaN, `-0.0 < +0.0` — exactly
//!   WASM's semantics; execution-verified against wasmtime (NaN/±0 matrix) in
//!   `aarch64_m4_trunc_minmax_538_differential.py`, not assumed.
//! - `f32/f64.copysign`: pure bit surgery through the GP file (`fmov` out,
//!   one sign mask + `bic`/`and`/`orr`, `fmov` back).
//!
//! **Still declined (loud-skip, never wrong code):** the rounding ops
//! (`ceil`/`floor`/`trunc`/`nearest`) and the i64<->float conversions
//! (a later increment).

use crate::encoder as enc;
use crate::encoder::{Cond, FReg, Reg};
use synth_core::WasmOp;
use synth_core::backend::{CodeRelocation, FUNC_TABLE_SYMBOL, RelocKind};

/// The GP value-stack temp registers: caller-saved `w9/x9..w15/x15` (7 slots).
/// `w0..w7` hold incoming integer params; results funnel back through `x0`.
const TEMPS: [Reg; 7] = [9, 10, 11, 12, 13, 14, 15];

/// The FP value-stack temp registers: caller-saved `v16..v23` (the low `v0..v7`
/// carry incoming float params, `v8..v15` are callee-saved). 8 scratch slots.
const FTEMPS: [FReg; 8] = [16, 17, 18, 19, 20, 21, 22, 23];

/// VCR-A64-CF-001 — the largest `br_table` the compare-and-branch-chain
/// lowering accepts. Each entry past the first costs 2 instructions
/// (`cmp` + `b.eq`), so 16 targets is a ≤32-instruction dispatch; past that a
/// real PC-relative jump table wins and the selector LOUD-DECLINES instead of
/// emitting an unbounded chain. Same threshold as the RV32 lowering (#882),
/// deliberately — the two backends' `br_table` frontiers stay comparable.
pub const BR_TABLE_MAX_TARGETS: usize = 16;

/// #851 — the WASM linear-memory base register. A memory-using function expects
/// `x28 = __linear_memory_base` on entry — the same dedicated-base convention
/// the ARM (R11) and RV32 (s11) backends use, chosen OUTSIDE the temp pool
/// (`x9..x15`), the AAPCS64 arg/result registers (`x0..x7`), and the platform /
/// frame registers (`x18`, `x29`, `x30`, `sp`). `x28` is callee-saved and
/// non-platform, so a caller establishing it once keeps it stable across the
/// function body; the lowering only READS it (never clobbers), so it stays a
/// clean ambient input. Effective address = `x28 + uxtw(w_addr) + memarg.offset`.
///
/// FRONTIER (honest): this backend does NOT yet EMIT anything that establishes
/// `x28` — there is no aarch64 startup / linker script (the RV32 backend sets
/// s11 in its generated `startup.rs`; the host-native subset has none). So a
/// memory-using function is correct *given* the `x28 = base` precondition, which
/// the #851 execution differential supplies explicitly; wiring the ABI/startup
/// that establishes it in a real program is a documented follow-on (alongside
/// data-segment init and memory.{size,grow}; OOB accesses trap since #865).
const LINMEM_BASE: Reg = 28;

/// #865 — linear-memory bounds-check mode for the load/store lowering.
///
/// v0.51.0 shipped the #851 lowering with NO bounds check and `--safety-bounds`
/// silently ignored (all four modes byte-identical): a guest address is
/// zero-extended (`uxtw`), so `0xFFFFFFFF` reaches `x28 + 4 GiB − 1` — an OOB
/// read (disclosure) / write (arbitrary-write) primitive where WASM requires a
/// trap. This enum makes the choice EXPLICIT at the selector boundary: a caller
/// must either supply the memory limit (and get per-access trap checks) or
/// explicitly opt out — there is no silent default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemBounds {
    /// No per-access check — the explicit `--safety-bounds none` opt-out.
    /// An out-of-bounds guest access dereferences host memory (documented,
    /// deliberate; NOT the CLI default).
    Unchecked,
    /// Software bounds (#865): every access proves
    /// `uxtw(addr) + memarg.offset + access_size <= limit_bytes`
    /// or traps (`brk #0`) BEFORE the dereference — WASM §4.4.7 OOB-trap
    /// semantics. `limit_bytes` is the module's declared minimum memory size
    /// (pages × 64 KiB); `memory.grow` is not lowered on this backend, so the
    /// declared minimum IS the runtime size and the static limit is sound.
    Software { limit_bytes: u64 },
}

/// Which register file a value-stack entry lives in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum File {
    /// General-purpose (`w`/`x`) — integers and 0/1 compare results.
    Gp,
    /// Floating-point (`s`/`d`) — f32/f64 values.
    Fp,
}

/// A value-stack entry: a register number plus which file it lives in. Widths
/// are carried by the op (as in m2), not the entry — an FP op knows whether it
/// wants the `s` or `d` view.
#[derive(Clone, Copy, Debug)]
struct Val {
    reg: u8,
    file: File,
}
impl Val {
    fn gp(reg: Reg) -> Self {
        Val {
            reg,
            file: File::Gp,
        }
    }
    fn fp(reg: FReg) -> Self {
        Val {
            reg,
            file: File::Fp,
        }
    }
}

#[derive(Debug)]
pub struct SelectError(pub String);

impl std::fmt::Display for SelectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "aarch64 selector: {}", self.0)
    }
}

/// Lower a single function body to A64 words, assuming the integer subset (m2)
/// param convention: params in `w0/x0..` with no float params. Thin wrapper over
/// [`select_typed`] with empty float-param masks.
pub fn select(ops: &[WasmOp], num_params: u32) -> Result<Vec<u32>, SelectError> {
    select_typed(ops, num_params, &[], &[])
}

/// Lower a body with per-param float masks but no control-flow (empty
/// block-arity table). Kept for callers/tests that predate the #538-cf
/// increment — behavior is byte-identical to threading an empty arity slice.
pub fn select_typed(
    ops: &[WasmOp],
    num_params: u32,
    params_f32: &[bool],
    params_f64: &[bool],
) -> Result<Vec<u32>, SelectError> {
    select_typed_cf(ops, num_params, params_f32, params_f64, &[])
}

/// The parameter's assigned register + file under AAPCS64. Integer params take
/// `x0,x1,…` in order; float params take `v0,v1,…` in order — the two counters
/// are INDEPENDENT, so `(param i32 f32 i32)` is w0, s0, w1.
fn param_map(num_params: u32, params_f32: &[bool], params_f64: &[bool]) -> Vec<Val> {
    let mut out = Vec::with_capacity(num_params as usize);
    let mut ngrn: u8 = 0; // next general (integer) arg register
    let mut nsrn: u8 = 0; // next SIMD/FP arg register
    for k in 0..num_params as usize {
        let is_f32 = params_f32.get(k).copied().unwrap_or(false);
        let is_f64 = params_f64.get(k).copied().unwrap_or(false);
        if is_f32 || is_f64 {
            out.push(Val::fp(nsrn));
            nsrn += 1;
        } else {
            out.push(Val::gp(ngrn));
            ngrn += 1;
        }
    }
    out
}

/// Lower a single function body with per-param type info AND control-flow.
///
/// `params_f32[k]` / `params_f64[k]` mark which params are float (delivered in V
/// registers). `block_arity` is the decoder's ordinal blocktype-arity side-table
/// (`(param_count, result_count)` of the k-th `Block`/`Loop`/`If` in op order),
/// used to gate the control-flow increment.
///
/// **Control-flow subset (#538 cf increment):** VOID-result `block … end` with
/// forward `br`/`br_if` to enclosing block ends. Only `block_arity == (0,0)`
/// blocks are accepted — a value-carrying (typed) block would need result-
/// register reconciliation across the branch and is LOUD-DECLINED. `loop`
/// (backward branch), `if`, and `br_table` are declined by name. This keeps the
/// straight-line value-stack model sound: nothing crosses the branch, so at each
/// `end` the value stack is exactly its block-entry height (asserted).
pub fn select_typed_cf(
    ops: &[WasmOp],
    num_params: u32,
    params_f32: &[bool],
    params_f64: &[bool],
    block_arity: &[(u8, u8)],
) -> Result<Vec<u32>, SelectError> {
    // No call metadata → any `call` in the body hits the honest catch-all decline
    // (byte-identical to the pre-#851 behavior for call-free functions).
    // No memory context either → bounds-unchecked, matching the pre-#865
    // behavior of these compatibility wrappers (the real driver — the Backend
    // impl — threads the resolved `MemBounds` explicitly).
    // No module context either -> `ModuleCtx::default()` has
    // `substrate_emitted == false`, so globals and `call_indirect` LOUD-DECLINE
    // here (this wrapper's callers place no `.data` / funcref table).
    let (words, _sites, _relocs) = select_typed_cf_calls(
        ops,
        num_params,
        params_f32,
        params_f64,
        block_arity,
        0,
        &[],
        &[],
        &[],
        MemBounds::Unchecked,
        &ModuleCtx::default(),
    )?;
    Ok(words)
}

/// A direct-`call` site produced during selection (#851): the BYTE offset of the
/// `bl` instruction within the function's code, and the callee's FULL wasm
/// function index (imports first). The backend turns each into an
/// `R_AARCH64_CALL26` relocation against the callee's `func_N` symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallSite {
    /// Byte offset of the `bl` instruction within the function's machine code.
    pub offset: u32,
    /// Callee's full wasm function index (imports first).
    pub callee: u32,
}

/// Lower a body, ALSO lowering direct `call` (#851). Same as [`select_typed_cf`]
/// plus the call-lowering inputs:
///
/// - `num_imports`: functions with full index `< num_imports` are IMPORTS —
///   calling one is loud-declined in v1 (no import-dispatch ABI yet).
/// - `func_arg_counts[idx]`: the callee's AAPCS integer-arg slot count (how many
///   values `call` pops off the value stack and marshals into `x0..x7`).
/// - `func_result_counts[idx]`: the callee's result count (0 = void, 1 = one
///   value pushed back). Multi-result and out-of-range are declined.
/// - `func_ret_float[idx]`: true when the callee returns an f32/f64. AAPCS64
///   returns floats in `v0/d0`, NOT `x0`, so a float-returning callee is
///   LOUD-DECLINED (pushing `x0` would read a stale GP register — the
///   "more-total-than-WASM" silent-miscompile class). Float results are a
///   documented later increment.
///
/// A function whose body contains a lowered `call` becomes NON-LEAF: `bl`
/// clobbers `x30`, so a non-leaf prologue saves FP/LR (`stp x29,x30,[sp,#-16]!`)
/// and every epilogue restores them (`ldp`) before `ret`. Leaf functions stay
/// byte-identical to the pre-#851 output (the frame is gated on "body has a
/// lowered call").
/// #851 lane L3 — the MODULE-LEVEL context the `global.get`/`global.set` and
/// `call_indirect` lowerings need, threaded as one parameter rather than five.
///
/// [`Default`] means "the driver emitted NO substrate", which makes all three
/// ops LOUD-DECLINE. That default is the fail-safe: a caller that has not
/// placed `__synth_globals` / `__synth_func_table` in the object cannot get code
/// that addresses them (see `CompileConfig::a64_substrate_emitted` and
/// [`crate::substrate::plan`], the single producer of both regions).
#[derive(Debug, Clone, Default)]
pub struct ModuleCtx {
    /// The driver has emitted the substrate regions this context describes.
    pub substrate_emitted: bool,
    /// Per DEFINED global index: true when the slot holds a 64-bit value
    /// (i64/f64) and must be read/written through the `x` view.
    pub global_is64: Vec<bool>,
    /// Per table index: `(compile-time slot count, base SLOT index of this
    /// table within the contiguous funcref region)`.
    pub tables: Vec<(u32, u32)>,
    /// Per module type index: the STRUCTURAL class id the dispatch compares
    /// (>= 1; 0 means "no class known", which declines).
    pub type_class_ids: Vec<u32>,
    /// Per module type index: AAPCS64 integer-argument slot count.
    pub type_arg_counts: Vec<u32>,
    /// Per module type index: result count (0 = void, 1 = one value).
    pub type_result_counts: Vec<u32>,
    /// Per module type index: the type returns f32/f64 (in `v0`/`d0`, not `x0`)
    /// — declined, exactly as for a direct `call`.
    pub type_ret_float: Vec<bool>,
}

/// #851 lane L3 — what one `select_typed_cf_calls` call produces: the emitted
/// A64 words, the direct-`call` sites (turned into `R_AARCH64_CALL26` by the
/// driver), and the symbol relocations for the `adrp`+`add :lo12:` pairs that
/// reach the emitted globals region / funcref table.
pub type Selection = (Vec<u32>, Vec<CallSite>, Vec<CodeRelocation>);

#[allow(clippy::too_many_arguments)]
pub fn select_typed_cf_calls(
    ops: &[WasmOp],
    num_params: u32,
    params_f32: &[bool],
    params_f64: &[bool],
    block_arity: &[(u8, u8)],
    num_imports: u32,
    func_arg_counts: &[u32],
    func_result_counts: &[u32],
    func_ret_float: &[bool],
    bounds: MemBounds,
    ctx: &ModuleCtx,
) -> Result<Selection, SelectError> {
    if num_params > 8 {
        return Err(SelectError(format!(
            "{num_params} params — supports at most 8 register params"
        )));
    }

    // #851 — is this function NON-LEAF (contains a `call` we will lower)? A `bl`
    // clobbers x30, so a non-leaf must save/restore LR. Computed up front so the
    // prologue can emit the frame; call-free functions stay byte-identical.
    // #851 lane L3: `call_indirect` lowers to `blr`, which also clobbers x30.
    let is_non_leaf = ops
        .iter()
        .any(|op| matches!(op, WasmOp::Call(_) | WasmOp::CallIndirect { .. }));

    // #851 lane L3 — PARAM HOMING for non-leaf functions.
    //
    // Params arrive in x0..x7, which are caller-saved: a `bl`/`blr` clobbers
    // them, so reading `local.get p` after a call would be garbage. Before this
    // increment that whole shape was loud-declined — which made `call_indirect`
    // near-useless, since the table index all but always comes from a parameter.
    //
    // The fix reuses the non-param-local machinery unchanged: when a non-leaf
    // function references a param, EVERY local (params included) gets an 8-byte
    // stack slot, the prologue STORES each param register into its slot, and
    // `local.get` becomes a `ldr` into a fresh temp exactly like a non-param
    // local. That restores both properties the decline was protecting:
    //
    //   * a post-call read hits the SLOT, which the call cannot clobber;
    //   * every value-stack entry is a temp (x9..x15) again — nothing lives in
    //     x0..x7 by reference — so argument marshalling stays hazard-free.
    //
    // RQ-57-A64PARAM (#851): the SAME machinery also unblocks WRITING a param.
    //
    // A LEAF function used to keep its params register-resident, so
    // `local.set`/`local.tee` on a param index had nowhere durable to write and
    // loud-declined — two of the four mechanically-derived ARM/aarch64
    // divergences (`cross_backend_op_parity.rs`). Homing gives the write a home
    // slot, and the copy-semantics `local.get` makes the aliasing hazard the
    // decline was guarding against structurally impossible: every value-stack
    // entry is a fresh temp, never the home location itself.
    //
    // `references_param` below matches reads AND writes, so `writes_param` is a
    // SUBSET of it: widening the predicate changes behaviour for EXACTLY ONE
    // class — leaf functions that write a param, every one of which declined
    // before. Non-leaf homing is bit-for-bit unchanged, and no function that
    // compiled without a frame starts consuming temps for `local.get`.
    let references_param = ops.iter().any(
        |op| matches!(op, WasmOp::LocalGet(i) | WasmOp::LocalSet(i) | WasmOp::LocalTee(i) if *i < num_params),
    );
    let writes_param = ops
        .iter()
        .any(|op| matches!(op, WasmOp::LocalSet(i) | WasmOp::LocalTee(i) if *i < num_params));
    let home_params = (is_non_leaf && references_param) || writes_param;
    // FLOAT params live in v0..v7, a DIFFERENT register file from the one the
    // slot model addresses. Homing them is not blocked by the encoder (it has
    // `str s/d` since the v0.54 L2 float load/store increment) but by the slot
    // model itself: `slot_resident`/`local_slot_off` are file-agnostic, and a
    // per-local register file is not threaded through them, so a homed v-param
    // would be stored and reloaded as a GP register — the wrong file. Rather
    // than emit that, loud-decline the whole function. Named follow-up: thread
    // the per-local file so float params home too.
    if home_params && (params_f32.iter().any(|b| *b) || params_f64.iter().any(|b| *b)) {
        return Err(SelectError(
            "function homes its parameters (it calls, or writes a parameter) but \
             declares a FLOAT parameter — the aarch64 home-slot model is \
             single-register-file, so homing a v-register param would store and \
             reload it as a GP register; loud-declining (#851)"
                .into(),
        ));
    }
    let params = param_map(num_params, params_f32, params_f64);
    let mut words: Vec<u32> = Vec::new();
    let mut stack: Vec<Val> = Vec::new();

    // --- non-param locals (#851): stack-slot frame ---
    //
    // WASM locals beyond the parameters (index >= num_params) are addressed by
    // any `local.get`/`local.set`/`local.tee` with index >= num_params. Their
    // count is `highest referenced index + 1 - num_params`. Each gets a fixed
    // 8-byte slot on the stack (64-bit wide so both i32 and i64 read back intact),
    // ZERO-INITIALIZED at entry per WASM's local default-value rule.
    //
    // Stack slots (not registers) give ALIAS SAFETY BY CONSTRUCTION: every
    // `local.get` is a `ldr` into a FRESH temp — a copy, never the home location —
    // so a later `local.set` of the same index cannot clobber a value already on
    // the value stack (the read-by-reference param path would miscompile this;
    // params stay read-only, see the LocalSet/LocalTee decline below).
    //
    // The slot for non-param local L (num_params <= L) is at `[sp, #(L -
    // num_params)*8]`. The frame is sized to a 16-byte multiple (AArch64 SP
    // alignment) and only materialized when there is at least one non-param local
    // — a function with none is byte-identical to before this increment.
    let max_local_idx = ops
        .iter()
        .filter_map(|op| match op {
            WasmOp::LocalGet(i) | WasmOp::LocalSet(i) | WasmOp::LocalTee(i) => Some(*i),
            _ => None,
        })
        .max();
    // #851 lane L3: when params are homed, the frame covers EVERY local
    // (index 0..=max), so slot `idx` sits at `idx * 8`; otherwise it covers only
    // the non-param locals and slot `idx` sits at `(idx - num_params) * 8`.
    let slot_base = if home_params { 0 } else { num_params };
    let num_slots = match max_local_idx {
        Some(m) if m >= slot_base => m - slot_base + 1,
        _ => 0,
    };
    // Frame size in bytes: one 8-byte slot per local, rounded UP to a 16-byte
    // multiple (the ABI requires 16-byte SP alignment).
    let frame_size: u32 = if num_slots == 0 {
        0
    } else {
        (num_slots * 8).div_ceil(16) * 16
    };
    // Byte offset of local `idx`'s slot from SP.
    let local_slot_off = |idx: u32| -> u32 { (idx - slot_base) * 8 };
    // Is local `idx` slot-resident (vs a register-resident param in a leaf)?
    let slot_resident = |idx: u32| -> bool { home_params || idx >= num_params };

    // Prologue. Order (each step lowers SP; epilogue reverses):
    //   1. #851 non-leaf: `stp x29,x30,[sp,#-16]!` saves FP/LR (a `bl` clobbers
    //      x30). SP stays 16-byte aligned. Only when the body has a lowered call.
    //   2. Non-param-local frame: `sub sp` then zero each 8-byte slot. Slot
    //      offsets are relative to the POST-sub SP, unaffected by the LR save
    //      that sits above them.
    if is_non_leaf {
        words.push(enc::stp_fp_lr_pre16());
    }
    if frame_size > 0 {
        words.push(enc::sub_imm64(enc::SP, enc::SP, frame_size));
        for k in 0..num_slots {
            let local_idx = slot_base + k;
            if home_params && local_idx < num_params {
                // #851 lane L3: HOME the incoming param register. The full
                // 64-bit store is right for i32 too — a `w`-form producer zeroes
                // the upper half, and every reader takes the `w` view back.
                words.push(enc::str_x_imm(
                    params[local_idx as usize].reg,
                    enc::SP,
                    k * 8,
                ));
            } else {
                // A non-param local is ZERO-INITIALIZED (WASM's default-value
                // rule).
                words.push(enc::str_x_imm(enc::XZR, enc::SP, k * 8));
            }
        }
    }

    // #851 — direct-call sites recorded during selection (byte offset of the
    // `bl`, callee full index) for the backend's R_AARCH64_CALL26 relocations.
    let mut call_sites: Vec<CallSite> = Vec::new();
    // #851 lane L3 — symbol relocations for the `adrp`+`add :lo12:` pairs that
    // reach the emitted globals region / funcref table.
    let mut sym_relocs: Vec<CodeRelocation> = Vec::new();

    // #851 lane L3 — resolve a global index to "is this an 8-byte slot?", or
    // LOUD-DECLINE. The `substrate_emitted` gate is the fail-safe: without it
    // the driver has placed no `__synth_globals`, so addressing it would be a
    // relocation against a symbol that does not exist.
    let global_slot = |ctx: &ModuleCtx, idx: u32| -> Result<bool, SelectError> {
        if !ctx.substrate_emitted {
            return Err(SelectError(
                "global.get/global.set needs the emitted `__synth_globals`                  region, which this compile path does not place —                  loud-declining (#851)"
                    .into(),
            ));
        }
        ctx.global_is64.get(idx as usize).copied().ok_or_else(|| {
            SelectError(format!(
                "global {idx} is out of range for the emitted globals region                  ({} slots) — loud-declining (#851)",
                ctx.global_is64.len()
            ))
        })
    };

    // Control-flow state (#538 cf increment, #851 full control flow). Each open
    // `block`/`loop`/`if` pushes a frame. The matching `End` pops it. Where a
    // `br`/`br_if` to that frame lands depends on the frame KIND:
    //
    //   * `Block` / `If`: a branch to the frame targets its END (fall-through) —
    //     a FORWARD branch, recorded in `pending` and patched when `End` closes
    //     the frame (the target position is only known then).
    //   * `Loop`: a branch to the frame targets its ENTRY (the loop header) — a
    //     BACKWARD branch, resolved to a NEGATIVE offset immediately at emission
    //     (`entry` is already known), never patched.
    //
    // This "dispatch on the TARGET frame's kind, not on the branch op" is what
    // makes loop back-edges correct alongside forward block exits.
    enum Kind {
        /// A plain `block`: branches to it go to its END (forward).
        Block,
        /// A `loop`: branches to it go to `entry` (the loop header, backward).
        Loop { entry: usize },
        /// An `if`: like Block for `br` (branches go to END), but also carries
        /// the position of the `cbz`/`b.cond` that skips the THEN arm, patched
        /// at `else` (to the else arm) or at `end` (past the then arm).
        If { else_fixup: Option<usize> },
    }
    /// VCR-A64-CF-001 — the reconciliation registers a VALUE-CARRYING frame
    /// reserves. Both files are reserved because the blocktype-arity side-table
    /// carries counts only; `file` records which one the first reconciliation
    /// actually used, so `End` pushes the right one.
    struct Slot {
        gp: Reg,
        fp: FReg,
        file: Option<File>,
    }
    struct Frame {
        kind: Kind,
        /// Word positions in `words` of FORWARD branches targeting this frame's
        /// END, awaiting fix-up when the frame closes (Block/If only; a Loop's
        /// branches are backward and resolved eagerly).
        pending: Vec<usize>,
        /// Value-stack height on entry — a void frame must restore it at `End`.
        stack_entry: usize,
        /// How many values a `br`/`br_if`/`br_table` to THIS frame's LABEL
        /// carries. For a Block/If the label is its END, so this is the frame's
        /// RESULT count; for a Loop the label is its HEADER, so this is the
        /// frame's PARAMETER count. Getting that distinction wrong is a SILENT
        /// MISCOMPILE, not a decline: reconciling on a `loop (result i32)`
        /// back-edge would overwrite the result register with a garbage value
        /// on every iteration. Only 0 or 1 (params and multi-value decline).
        label_arity: u8,
        /// How many values the frame's FALL-THROUGH `End` leaves on the stack
        /// (the frame's result count). Only 0 or 1.
        result_arity: u8,
        /// Reserved reconciliation registers — `Some` iff the frame is
        /// value-carrying (`result_arity == 1`).
        slot: Option<Slot>,
    }
    let mut ctrl: Vec<Frame> = Vec::new();
    // Ordinal counter over Block/Loop/If in op order — the key into
    // `block_arity`. Incremented on EVERY control op encountered (even declined
    // ones, though a decline aborts the whole compile so alignment is moot).
    let mut ctrl_ord: usize = 0;
    // Reachability of the current linear position (#851). Code after an
    // UNCONDITIONAL transfer (`br`, `return`, `unreachable`) is unreachable and
    // WASM's stack becomes polymorphic there — the straight-line height model no
    // longer tracks the real stack. We keep truncating the value stack to the
    // frame's entry height at `else`/`end` (that fixes the model), but SKIP the
    // fall-through height assert when unreachable (it only holds on a reachable
    // fall-through). `br_if` is conditional, so its fall-through stays reachable.
    let mut reachable = true;

    // VCR-A64-CF-001 (#851/#509) — RESERVED reconciliation registers.
    //
    // A value-carrying frame (`block (result T)`, `if (result T)`,
    // `loop (result T)`) needs ONE register that holds the frame's value on
    // EVERY path reaching its `end`. That register must be withheld from the
    // temp allocator for the frame's whole extent, otherwise code between a
    // `br` that deposited into it and the `end` that reads it could allocate
    // the same temp and clobber a live result.
    //
    // The reservation is a BITMASK (bit r = register r reserved), not a value-
    // stack entry: the value stack is consumed WHOLESALE by the `call` /
    // `call_indirect` argument marshalling (`stack.iter().enumerate()` +
    // `stack.clear()`), so a placeholder pushed there would be marshalled as an
    // argument and then erased. A separate mask cannot be reached by any of
    // those whole-stack consumers, and `epilogue(stack.last())` can never
    // return a reservation.
    //
    // Both files are reserved per frame, because the blocktype arity side-table
    // carries COUNTS ONLY — whether the result is i32/i64 (GP) or f32/f64 (FP)
    // is not known until the first value is reconciled.
    let reserved_gp = std::cell::Cell::<u32>::new(0);
    let reserved_fp = std::cell::Cell::<u32>::new(0);
    let gp_free = |t: Reg, stack: &[Val]| {
        reserved_gp.get() & (1u32 << t) == 0
            && !stack.iter().any(|v| v.file == File::Gp && v.reg == t)
    };
    let fp_free = |t: FReg, stack: &[Val]| {
        reserved_fp.get() & (1u32 << t) == 0
            && !stack.iter().any(|v| v.file == File::Fp && v.reg == t)
    };

    // Pick a GP temp holding neither a live GP value-stack entry nor an open
    // frame's reserved result register.
    let alloc_temp = |stack: &[Val]| -> Result<Reg, SelectError> {
        TEMPS
            .iter()
            .copied()
            .find(|t| gp_free(*t, stack))
            .ok_or_else(|| SelectError("value-stack too deep (GP temp regs exhausted)".into()))
    };
    // Pick an FP temp holding neither a live FP value-stack entry nor an open
    // frame's reserved result register.
    let alloc_ftemp = |stack: &[Val]| -> Result<FReg, SelectError> {
        FTEMPS
            .iter()
            .copied()
            .find(|t| fp_free(*t, stack))
            .ok_or_else(|| SelectError("value-stack too deep (FP temp regs exhausted)".into()))
    };

    // VCR-A64-CF-001 — validate a `block`/`loop`/`if` blocktype arity and, when
    // it is VALUE-CARRYING, reserve its reconciliation register pair.
    //
    // Returns `(label_arity, result_arity, slot)`. `is_loop` picks the LABEL
    // arity: a `br` to a Loop targets its HEADER and carries the loop's
    // PARAMETERS, while a `br` to a Block/If targets its END and carries the
    // frame's RESULTS. A `loop (result i32)` therefore has label arity 0 —
    // its back-edge must reconcile NOTHING, or every iteration would stamp a
    // garbage value into the result register.
    let open_slot = |what: &str,
                     ord: usize,
                     arity: (u8, u8),
                     is_loop: bool,
                     stack: &[Val]|
     -> Result<(u8, u8, Option<Slot>), SelectError> {
        let (params, results) = arity;
        if params != 0 {
            return Err(SelectError(format!(
                "{what} #{ord} has type {arity:?} — a PARAMETER-taking block \
                 type (multi-value) is not lowered on aarch64: the \
                 reconciliation slot is ONE register, so block params would \
                 need a per-path multi-register shuffle; loud-declining \
                 (VCR-A64-CF-001)"
            )));
        }
        if results > 1 {
            return Err(SelectError(format!(
                "{what} #{ord} has type {arity:?} — a MULTI-VALUE result block \
                 type is not lowered on aarch64 (the reconciliation slot is ONE \
                 register); loud-declining (VCR-A64-CF-001)"
            )));
        }
        let slot = if results == 1 {
            let gp = alloc_temp(stack)?;
            reserved_gp.set(reserved_gp.get() | 1u32 << gp);
            let fp = match alloc_ftemp(stack) {
                Ok(f) => f,
                Err(e) => {
                    // Roll the GP reservation back so a decline leaves no
                    // stranded register behind.
                    reserved_gp.set(reserved_gp.get() & !(1u32 << gp));
                    return Err(e);
                }
            };
            reserved_fp.set(reserved_fp.get() | 1u32 << fp);
            Some(Slot { gp, fp, file: None })
        } else {
            None
        };
        Ok((if is_loop { params } else { results }, results, slot))
    };

    /// VCR-A64-CF-001 — move `v` into a value-carrying frame's reconciliation
    /// register, recording which register FILE the frame's result lives in.
    ///
    /// The 64-bit forms are deliberate and match [`epilogue`]: `mov x` carries
    /// an i32 intact (w-form producers zero the upper half) and `fmov d`
    /// carries an f32's low 32 bits intact.
    ///
    /// SOUNDNESS NOTE — why no clobber window exists. `v.reg` can never BE the
    /// slot register (the slot is reserved, so the temp allocator cannot have
    /// handed it out to a live value), so this move never destroys a live
    /// operand. And every call site writes the slot IMMEDIATELY before a
    /// transfer to the frame's join point: `br`/`br_if` before the branch,
    /// `else` before the `b end`, `end` before the push. So on the path that
    /// WRITES the slot, the very next thing executed is the join — nothing
    /// (not even a `bl`, which clobbers the caller-saved x9..x15 temp pool)
    /// runs in between. On any other path the written value is dead and is
    /// re-written before that path reaches the join.
    fn reconcile_into(words: &mut Vec<u32>, slot: &mut Slot, v: Val) {
        match v.file {
            File::Gp => {
                if v.reg != slot.gp {
                    words.push(enc::mov_reg64(slot.gp, v.reg));
                }
            }
            File::Fp => {
                if v.reg != slot.fp {
                    words.push(enc::fmov_d(slot.fp, v.reg));
                }
            }
        }
        slot.file = Some(v.file);
    }

    /// VCR-A64-CF-001 — reconcile a `br`/`br_if` that targets `ctrl[target]`.
    ///
    /// A no-op unless the target's LABEL arity is 1 (results for a Block/If,
    /// PARAMS for a Loop — see [`Frame::label_arity`]). The value is PEEKED,
    /// never popped: `br_if`'s not-taken path keeps it on the operand stack,
    /// and `br`'s fall-through is unreachable so the stale entry is truncated
    /// away at the frame's `End`.
    fn reconcile_branch(
        words: &mut Vec<u32>,
        ctrl: &mut [Frame],
        stack: &[Val],
        target: usize,
        ctx: &str,
    ) -> Result<(), SelectError> {
        if ctrl[target].label_arity == 0 {
            return Ok(());
        }
        if stack.len() <= ctrl[target].stack_entry {
            return Err(SelectError(format!(
                "{ctx}: branch to a value-carrying label with no result on the \
                 value stack (height {}, target frame entry height {})",
                stack.len(),
                ctrl[target].stack_entry
            )));
        }
        let v = stack[stack.len() - 1];
        let slot = ctrl[target].slot.as_mut().ok_or_else(|| {
            SelectError(format!(
                "{ctx}: value-carrying label has no reconciliation slot \
                 (internal invariant)"
            ))
        })?;
        reconcile_into(words, slot, v);
        Ok(())
    }

    // Pop a GP operand, erroring if the top value is actually an FP value (a
    // type confusion that would otherwise silently read the wrong file).
    fn pop_gp(stack: &mut Vec<Val>, ctx: &str) -> Result<Reg, SelectError> {
        let v = stack
            .pop()
            .ok_or_else(|| SelectError(format!("{ctx} underflow")))?;
        if v.file != File::Gp {
            return Err(SelectError(format!("{ctx}: expected GP operand, got FP")));
        }
        Ok(v.reg)
    }
    fn pop_fp(stack: &mut Vec<Val>, ctx: &str) -> Result<FReg, SelectError> {
        let v = stack
            .pop()
            .ok_or_else(|| SelectError(format!("{ctx} underflow")))?;
        if v.file != File::Fp {
            return Err(SelectError(format!("{ctx}: expected FP operand, got GP")));
        }
        Ok(v.reg)
    }

    // A GP binary `dst = a OP b`.
    let binop = |words: &mut Vec<u32>,
                 stack: &mut Vec<Val>,
                 f: fn(Reg, Reg, Reg) -> u32|
     -> Result<(), SelectError> {
        let b = pop_gp(stack, "binop")?;
        let a = pop_gp(stack, "binop")?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a, b));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // A GP unary `dst = OP a`.
    let unop = |words: &mut Vec<u32>,
                stack: &mut Vec<Val>,
                f: fn(Reg, Reg) -> u32|
     -> Result<(), SelectError> {
        let a = pop_gp(stack, "unop")?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // An FP binary `dst = a OP b` (both operands and result in the FP file).
    let fbinop = |words: &mut Vec<u32>,
                  stack: &mut Vec<Val>,
                  f: fn(FReg, FReg, FReg) -> u32|
     -> Result<(), SelectError> {
        let b = pop_fp(stack, "fbinop")?;
        let a = pop_fp(stack, "fbinop")?;
        let dst = alloc_ftemp(stack)?;
        words.push(f(dst, a, b));
        stack.push(Val::fp(dst));
        Ok(())
    };
    // An FP unary `dst = OP a` (FP → FP).
    let funop = |words: &mut Vec<u32>,
                 stack: &mut Vec<Val>,
                 f: fn(FReg, FReg) -> u32|
     -> Result<(), SelectError> {
        let a = pop_fp(stack, "funop")?;
        let dst = alloc_ftemp(stack)?;
        words.push(f(dst, a));
        stack.push(Val::fp(dst));
        Ok(())
    };
    // An FP compare `dst(GP 0/1) = (a CMP b)` — `fcmp` + `cset cond`. The result
    // is a GP boolean; `cond` is the clang-matched (NaN-correct) condition.
    let fcmp_op = |words: &mut Vec<u32>,
                   stack: &mut Vec<Val>,
                   fcmp: fn(FReg, FReg) -> u32,
                   cond: Cond|
     -> Result<(), SelectError> {
        let b = pop_fp(stack, "fcompare")?;
        let a = pop_fp(stack, "fcompare")?;
        let dst = alloc_temp(stack)?;
        words.push(fcmp(a, b));
        words.push(enc::cset(dst, cond));
        stack.push(Val::gp(dst));
        Ok(())
    };
    // int → float conversion: pop a GP operand, push an FP result.
    let cvt_gp_to_fp = |words: &mut Vec<u32>,
                        stack: &mut Vec<Val>,
                        f: fn(FReg, Reg) -> u32|
     -> Result<(), SelectError> {
        let a = pop_gp(stack, "convert")?;
        let dst = alloc_ftemp(stack)?;
        words.push(f(dst, a));
        stack.push(Val::fp(dst));
        Ok(())
    };
    // m4: trapping float→int truncation with the #709 WASM domain guard
    // (§4.3.3). A64 FCVTZS/FCVTZU SATURATE where WASM must TRAP, so the
    // convert is emitted ONLY behind two fcmp + b.cond + brk range checks:
    //
    //   mov  dst, #hi_bits ; fmov bound, dst ; fcmp a, bound
    //   b.mi +2                      // x < hi (ORDERED: NaN ⇒ fall through)
    //   brk  #0                      // trap: NaN or too large
    //   mov  dst, #lo_bits ; fmov bound, dst ; fcmp a, bound
    //   b.<ge|gt> +2                 // x >= lo (signed f32) / x > lo (strict)
    //   brk  #0                      // trap: too small
    //   fcvtz[su] dst, a             // proven in-range: saturate == trunc
    //
    // Boundary table (WASM Core §4.3.3, mirrored from the Thumb-2 #709 guard):
    //   f32→s: hi 2^31 (0x4F000000, exclusive), lo -2^31 (0xCF000000,
    //          INCLUSIVE — -2^31 is representable and in-range; no f32 exists
    //          strictly between -2^31-1 and -2^31, so `ge` is exact).
    //   f32→u: hi 2^32 (0x4F800000, exclusive), lo -1.0 (0xBF800000, STRICT —
    //          trunc(-0.5) = 0 is valid, trunc(-1.0) = -1 traps).
    //   f64→s: hi 2^31 (0x41E0...0, exclusive), lo -(2^31)-1 (0xC1E0...0020_0000,
    //          STRICT — f64 CAN represent values in (-2^31-1, -2^31), e.g.
    //          -2147483648.5, which truncate to -2^31 and are IN-range; an
    //          inclusive -2^31 bound would wrongly trap them).
    //   f64→u: hi 2^32 (0x41F0...0, exclusive), lo -1.0 (0xBFF0...0, strict).
    //
    // v0.54 L2 (#851): `dst64` extends the SAME guard to the i64-TARGET forms.
    // Only the two bound constants and the destination width change — the
    // shape (ordered hi check, then lo check, then the bare convert) is
    // identical, so the i64 forms inherit the proven NaN handling (an ordered
    // `b.mi` is FALSE for NaN, so NaN falls into the first `brk`).
    //
    // i64 boundary table (WASM Core §4.3.3), each entry justified — the whole
    // point is that A64 saturation must never be observable:
    //   f32→s64: hi 2^63 (0x5F000000, exclusive), lo -2^63 (0xDF000000,
    //            INCLUSIVE. -2^63 is exactly representable in f32 (exponent
    //            63, zero mantissa) and truncates to INT64_MIN, which is
    //            in-range; the next f32 below it is -2^63·(1+2^-23), far
    //            outside. So `ge` is exact — a STRICT bound would wrongly trap
    //            the legal INT64_MIN input.)
    //   f32→u64: hi 2^64 (0x5F800000, exclusive), lo -1.0 (0xBF800000, STRICT
    //            — trunc_u(-0.5) = 0 is legal, trunc_u(-1.0) traps).
    //   f64→s64: hi 2^63 (0x43E0...0, exclusive), lo -2^63 (0xC3E0...0,
    //            INCLUSIVE. NOTE this differs from the i32/f64 row above, and
    //            the reason is the ULP: near 2^63 the f64 spacing is
    //            2^63·2^-52 = 2048, so NO f64 exists in (-2^63-1, -2^63) —
    //            unlike the i32 case where -2147483648.5 is representable and
    //            forced a strict -(2^31)-1 bound. Here the next f64 below
    //            -2^63 is -2^63-2048, which is genuinely out of range, so an
    //            inclusive bound is both exact and necessary.)
    //   f64→u64: hi 2^64 (0x43F0...0, exclusive), lo -1.0 (0xBFF0...0, strict).
    // Every row is execution-checked against wasmtime over both sides of each
    // boundary in `aarch64_float_completion_851_differential.py`.
    let trunc_guarded = |words: &mut Vec<u32>,
                         stack: &mut Vec<Val>,
                         is_f64: bool,
                         signed: bool,
                         dst64: bool|
     -> Result<(), SelectError> {
        let a = pop_fp(stack, "trunc")?;
        // Keep `a` live across temp allocation: it is read by both fcmps and
        // the final convert, so the bound register must never alias it.
        stack.push(Val::fp(a));
        let dst = alloc_temp(stack)?; // GP: const scratch, then the result
        let bound = alloc_ftemp(stack)?;
        stack.pop();
        let (hi_bits, lo_bits, lo_cond): (u64, u64, Cond) = match (is_f64, signed, dst64) {
            (false, true, false) => (0x4F00_0000, 0xCF00_0000, Cond::Ge),
            (false, false, false) => (0x4F80_0000, 0xBF80_0000, Cond::Gt),
            (true, true, false) => (0x41E0_0000_0000_0000, 0xC1E0_0000_0020_0000, Cond::Gt),
            (true, false, false) => (0x41F0_0000_0000_0000, 0xBFF0_0000_0000_0000, Cond::Gt),
            (false, true, true) => (0x5F00_0000, 0xDF00_0000, Cond::Ge),
            (false, false, true) => (0x5F80_0000, 0xBF80_0000, Cond::Gt),
            (true, true, true) => (0x43E0_0000_0000_0000, 0xC3E0_0000_0000_0000, Cond::Ge),
            (true, false, true) => (0x43F0_0000_0000_0000, 0xBFF0_0000_0000_0000, Cond::Gt),
        };
        let check = |words: &mut Vec<u32>, bits: u64, cond: Cond| {
            if is_f64 {
                for w in enc::mov_imm64(dst, bits) {
                    words.push(w);
                }
                words.push(enc::fmov_d_from_x(bound, dst));
                words.push(enc::fcmp_d(a, bound));
            } else {
                for w in enc::mov_imm32(dst, bits as u32) {
                    words.push(w);
                }
                words.push(enc::fmov_s_from_w(bound, dst));
                words.push(enc::fcmp_s(a, bound));
            }
            words.push(enc::bcond(cond, 2)); // skip the brk when in-range
            words.push(enc::brk(0));
        };
        check(words, hi_bits, Cond::Mi);
        check(words, lo_bits, lo_cond);
        words.push(match (is_f64, signed, dst64) {
            (false, true, false) => enc::fcvtzs_w_from_s(dst, a),
            (false, false, false) => enc::fcvtzu_w_from_s(dst, a),
            (true, true, false) => enc::fcvtzs_w_from_d(dst, a),
            (true, false, false) => enc::fcvtzu_w_from_d(dst, a),
            (false, true, true) => enc::fcvtzs_x_from_s(dst, a),
            (false, false, true) => enc::fcvtzu_x_from_s(dst, a),
            (true, true, true) => enc::fcvtzs_x_from_d(dst, a),
            (true, false, true) => enc::fcvtzu_x_from_d(dst, a),
        });
        stack.push(Val::gp(dst));
        Ok(())
    };

    // #782a: NONTRAPPING saturating float→int truncation (WASM §4.3.2
    // trunc_sat — the 0xFC-prefixed family). A64 FCVTZS/FCVTZU already
    // implement it EXACTLY: round-toward-zero, out-of-range saturates to the
    // integer bound, NaN → 0 (FPToFixed) — the very "more-total-than-WASM"
    // behavior the m4 `trunc_guarded` domain guard defends the TRAPPING forms
    // against is the REQUIRED semantics here, so the lowering is one bare
    // convert. All eight forms land (A64 is 64-bit native, so the i64 targets
    // are the same one-instruction shape with an x destination).
    // Execution-verified vs wasmtime (NaN/±inf/exact-boundary table) in
    // `scripts/repro/trunc_sat_782_differential.py`.
    let trunc_sat = |words: &mut Vec<u32>,
                     stack: &mut Vec<Val>,
                     f: fn(Reg, FReg) -> u32|
     -> Result<(), SelectError> {
        let a = pop_fp(stack, "trunc_sat")?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // m4: copysign(z1, z2) — the magnitude of z1 with the sign of z2, a pure
    // bit operation (WASM §4.3.3 fcopysign; NaN payloads pass through intact).
    // Route both operands through the GP file, isolate the sign with ONE
    // materialized mask (`and` for the sign, `bic` for the magnitude), merge,
    // and move back.
    let copysign =
        |words: &mut Vec<u32>, stack: &mut Vec<Val>, is_f64: bool| -> Result<(), SelectError> {
            let b = pop_fp(stack, "copysign")?; // z2: sign source
            let a = pop_fp(stack, "copysign")?; // z1: magnitude
            // Three DISTINCT free GP temps (a-bits, b-bits, mask).
            let mut free = TEMPS.iter().copied().filter(|t| gp_free(*t, stack));
            let (Some(ta), Some(tb), Some(tm)) = (free.next(), free.next(), free.next()) else {
                return Err(SelectError(
                    "value-stack too deep (copysign needs 3 GP temps)".into(),
                ));
            };
            let dst = alloc_ftemp(stack)?; // may alias a/b: written last, from GP
            if is_f64 {
                words.push(enc::fmov_x_from_d(ta, a));
                words.push(enc::fmov_x_from_d(tb, b));
                for w in enc::mov_imm64(tm, 0x8000_0000_0000_0000) {
                    words.push(w);
                }
                words.push(enc::and64(tb, tb, tm)); // sign of z2
                words.push(enc::bic64(ta, ta, tm)); // magnitude of z1
                words.push(enc::orr64(ta, ta, tb));
                words.push(enc::fmov_d_from_x(dst, ta));
            } else {
                words.push(enc::fmov_w_from_s(ta, a));
                words.push(enc::fmov_w_from_s(tb, b));
                for w in enc::mov_imm32(tm, 0x8000_0000) {
                    words.push(w);
                }
                words.push(enc::and(tb, tb, tm));
                words.push(enc::bic(ta, ta, tm));
                words.push(enc::orr(ta, ta, tb));
                words.push(enc::fmov_s_from_w(dst, ta));
            }
            stack.push(Val::fp(dst));
            Ok(())
        };

    // reinterpret GP → FP (bit-cast, FMOV).
    let reinterpret_gp_to_fp = |words: &mut Vec<u32>,
                                stack: &mut Vec<Val>,
                                f: fn(FReg, Reg) -> u32|
     -> Result<(), SelectError> {
        let a = pop_gp(stack, "reinterpret")?;
        let dst = alloc_ftemp(stack)?;
        words.push(f(dst, a));
        stack.push(Val::fp(dst));
        Ok(())
    };
    // reinterpret FP → GP (bit-cast, FMOV).
    let reinterpret_fp_to_gp = |words: &mut Vec<u32>,
                                stack: &mut Vec<Val>,
                                f: fn(Reg, FReg) -> u32|
     -> Result<(), SelectError> {
        let a = pop_fp(stack, "reinterpret")?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // #851 — integer divide / remainder with WASM-faithful traps.
    //
    // A64 SDIV/UDIV are TOTAL where WASM is PARTIAL, so the raw instruction is a
    // "more-total-than-WASM" silent miscompile (the #633/#666/#709 class). WASM
    // (Core §4.3.2) requires:
    //   * div/rem by ZERO traps         (all four forms)
    //   * div_s(INT_MIN, -1) traps      (overflow: +2^(N-1) is unrepresentable)
    //   * rem_s(INT_MIN, -1) = 0        (NO trap — falls out of MSUB naturally)
    // We therefore emit an explicit divisor-zero guard for every form and, for
    // SIGNED DIV only, an INT_MIN/-1 overflow guard. `is_rem`/`signed`/`is64`
    // parameterize the one closure.
    //
    // Aliasing (the #776 lesson): `msub rd, q, b, a` reads a, b AND q at once, and
    // the guards read a/b after materializing const scratch. So every temp
    // (quotient, const scratch, result) is allocated while a and b are STILL on
    // the value stack (pushed back as reservations), guaranteeing no allocation
    // hands back a register still holding a live operand.
    let divrem = |words: &mut Vec<u32>,
                  stack: &mut Vec<Val>,
                  signed: bool,
                  is64: bool,
                  is_rem: bool|
     -> Result<(), SelectError> {
        let b = pop_gp(stack, "divrem")?; // divisor
        let a = pop_gp(stack, "divrem")?; // dividend
        // Reserve a and b so temp allocation never collides with them.
        stack.push(Val::gp(a));
        stack.push(Val::gp(b));
        // Need up to three DISTINCT scratch regs beyond a/b: quotient, and (for
        // the signed-div overflow guard) two const-materialization temps.
        let mut free = TEMPS.iter().copied().filter(|t| gp_free(*t, stack));
        let (Some(q), Some(s0), Some(s1)) = (free.next(), free.next(), free.next()) else {
            stack.pop();
            stack.pop();
            return Err(SelectError(
                "value-stack too deep (divrem needs 3 GP temps)".into(),
            ));
        };
        stack.pop(); // b
        stack.pop(); // a

        // --- Guard 1: divisor == 0 → trap (all four forms). Test the FULL width
        // so an i64 divisor with a zero low word but nonzero high word (e.g.
        // 0x1_0000_0000) is correctly seen as nonzero. `cbnz b, +2` skips the
        // brk when the divisor is nonzero.
        if is64 {
            words.push(enc::cbnz64(b, 2));
        } else {
            words.push(enc::cbnz(b, 2));
        }
        words.push(enc::brk(0)); // divide by zero

        // --- Guard 2 (signed DIV only): dividend == INT_MIN && divisor == -1
        // → overflow trap. rem_s does NOT trap here (result is 0). Materialize
        // INT_MIN and -1, compare, and branch over the brk when EITHER differs.
        if signed && !is_rem {
            let (min_bits, neg1_bits): (u64, u64) = if is64 {
                (0x8000_0000_0000_0000, 0xFFFF_FFFF_FFFF_FFFF)
            } else {
                (0x8000_0000, 0xFFFF_FFFF)
            };
            if is64 {
                for w in enc::mov_imm64(s0, min_bits) {
                    words.push(w);
                }
                for w in enc::mov_imm64(s1, neg1_bits) {
                    words.push(w);
                }
                words.push(enc::cmp64(a, s0));
            } else {
                for w in enc::mov_imm32(s0, min_bits as u32) {
                    words.push(w);
                }
                for w in enc::mov_imm32(s1, neg1_bits as u32) {
                    words.push(w);
                }
                words.push(enc::cmp(a, s0));
            }
            // b.ne → dividend != INT_MIN, no overflow: jump PAST the second cmp,
            // its b.ne, and the brk, landing on the arithmetic. Those are the
            // next THREE instructions, so the branch target is +4 words from
            // this branch (`b.<cond> #(imm*4)` is pc-relative to the branch).
            words.push(enc::bcond(Cond::Ne, 4));
            words.push(if is64 {
                enc::cmp64(b, s1)
            } else {
                enc::cmp(b, s1)
            });
            words.push(enc::bcond(Cond::Ne, 2)); // divisor != -1 → skip brk
            words.push(enc::brk(0)); // INT_MIN / -1 overflow
        }

        // --- The arithmetic.
        let dst = if is_rem {
            // rem = a − (a/b)·b. SDIV/UDIV into q, then MSUB into the result reg
            // (which may reuse q — msub reads q before writing its dst).
            if signed {
                words.push(if is64 {
                    enc::sdiv64(q, a, b)
                } else {
                    enc::sdiv(q, a, b)
                });
            } else {
                words.push(if is64 {
                    enc::udiv64(q, a, b)
                } else {
                    enc::udiv(q, a, b)
                });
            }
            words.push(if is64 {
                enc::msub64(q, q, b, a)
            } else {
                enc::msub(q, q, b, a)
            });
            q
        } else {
            words.push(match (signed, is64) {
                (true, false) => enc::sdiv(q, a, b),
                (true, true) => enc::sdiv64(q, a, b),
                (false, false) => enc::udiv(q, a, b),
                (false, true) => enc::udiv64(q, a, b),
            });
            q
        };
        stack.push(Val::gp(dst));
        Ok(())
    };

    // #851 — scalar popcount via the Advanced-SIMD unit (A64 has no scalar
    // POPCNT): move the integer into a V register, per-byte CNT, horizontal
    // ADDV, move back. For i32, `fmov s,w` zero-fills the upper lanes so CNT.8b
    // counts exactly 4 value bytes; for i64, `fmov d,x` fills all 8.
    let popcnt = |words: &mut Vec<u32>,
                  stack: &mut Vec<Val>,
                  is64: bool|
     -> Result<(), SelectError> {
        let a = pop_gp(stack, "popcnt")?;
        let dst = alloc_temp(stack)?;
        // Grab an FP scratch that no live FP value-stack entry holds.
        let vtmp = FTEMPS
            .iter()
            .copied()
            .find(|t| fp_free(*t, stack))
            .ok_or_else(|| SelectError("value-stack too deep (popcnt needs an FP temp)".into()))?;
        if is64 {
            words.push(enc::fmov_d_from_x(vtmp, a));
        } else {
            words.push(enc::fmov_s_from_w(vtmp, a));
        }
        words.push(enc::cnt_8b(vtmp, vtmp));
        words.push(enc::addv_8b(vtmp, vtmp));
        words.push(enc::fmov_w_from_s(dst, vtmp));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // `ctz` = `rbit` then `clz` (A64 has no direct CTZ). `sf` selects width.
    let ctz = |words: &mut Vec<u32>, stack: &mut Vec<Val>, sf: bool| -> Result<(), SelectError> {
        let a = pop_gp(stack, "ctz")?;
        let dst = alloc_temp(stack)?;
        if sf {
            words.push(enc::rbit64(dst, a));
            words.push(enc::clz64(dst, dst));
        } else {
            words.push(enc::rbit(dst, a));
            words.push(enc::clz(dst, dst));
        }
        stack.push(Val::gp(dst));
        Ok(())
    };

    // `rotl rd, rn, rk` = `neg rtmp, rk; rorv rd, rn, rtmp` (mod-width neg gives
    // the equivalent right-rotate; correct including k=0 → neg 0 = 0).
    let rotl = |words: &mut Vec<u32>, stack: &mut Vec<Val>, sf: bool| -> Result<(), SelectError> {
        let k = pop_gp(stack, "rotl")?;
        let n = pop_gp(stack, "rotl")?;
        let dst = alloc_temp(stack)?;
        // #776: the `neg` scratch must NOT be `dst` — `alloc_temp` can hand back
        // the register that held the computed operand `n` (n,k are already popped,
        // so n's reg is free to reuse), and `neg(dst, k)` would then destroy `n`
        // before `rorv` reads it (silent wrong result; param-only rotates escaped
        // because their `n` sits in a distinct arg register). Compute `-k` in `k`'s
        // own now-dead register instead; `rorv` then reads `n` (intact) + `-k` and
        // writes `dst` safely — reads-before-write holds even if `dst` aliases an
        // input, and n/k are distinct stack slots so `neg(k,k)` never touches `n`.
        if sf {
            words.push(enc::neg64(k, k));
            words.push(enc::rorv64(dst, n, k));
        } else {
            words.push(enc::neg(k, k));
            words.push(enc::rorv(dst, n, k));
        }
        stack.push(Val::gp(dst));
        Ok(())
    };

    // A GP comparison `dst = (a CMP b)` as `cmp` + `cset cond`. `sf` selects width.
    let cmp_op = |words: &mut Vec<u32>,
                  stack: &mut Vec<Val>,
                  sf: bool,
                  cond: Cond|
     -> Result<(), SelectError> {
        let b = pop_gp(stack, "compare")?;
        let a = pop_gp(stack, "compare")?;
        let dst = alloc_temp(stack)?;
        words.push(if sf { enc::cmp64(a, b) } else { enc::cmp(a, b) });
        words.push(enc::cset(dst, cond));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // `eqz`: `dst = (a == 0)` as `cmp a, zr` + `cset eq`.
    let eqz = |words: &mut Vec<u32>, stack: &mut Vec<Val>, sf: bool| -> Result<(), SelectError> {
        let a = pop_gp(stack, "eqz")?;
        let dst = alloc_temp(stack)?;
        words.push(if sf {
            enc::cmp64(a, enc::XZR)
        } else {
            enc::cmp(a, enc::WZR)
        });
        words.push(enc::cset(dst, Cond::Eq));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // #851 — form the effective linear-memory address `x_ea = x28 + uxtw(addr) +
    // offset` into a fresh GP temp and return it. `size_log2` is the access-size
    // log2 (0=byte,1=half,2=word,3=dword). If `offset` is a multiple of the
    // access size and the scaled result fits imm12 (< 4096), the caller may fold
    // it into the load/store immediate (returned as `Some(imm12)`); otherwise the
    // offset is ADDED into `x_ea` here and `None` is returned. `x_ea` is a temp
    // that does not alias any live value-stack entry (the address operand has
    // already been popped, so its register is free to reuse).
    //
    // SOUNDNESS (#865): under `MemBounds::Software` every access first PROVES
    // `uxtw(addr) + offset + size <= limit` or traps (`brk #0`) — WASM §4.4.7.
    // Since `offset`, `size`, and `limit` are all compile-time constants, the
    // check reduces to a single unsigned compare of the 32-bit guest address
    // against `K = limit - offset - size`:
    //
    //   in-bounds  ⇔  uxtw(addr) + offset + size ≤ limit  ⇔  uxtw(addr) ≤ K
    //
    //   mov  w_k, #K          ; K = limit - offset - size (compile-time)
    //   cmp  w_addr, w_k      ; 32-bit compare — uxtw-correct by construction
    //                         ; (w-form reads the low 32 bits, exactly the
    //                         ;  zero-extended guest address the EA add uses)
    //   b.ls +2               ; unsigned addr <= K → skip the trap
    //   brk  #0               ; OOB → trap (same mechanism as div/0, #709)
    //
    // When `K < 0` (offset + size exceed the limit) NO i32 address is in
    // bounds: emit an unconditional `brk` (the access always traps; the dead
    // access code that follows keeps the value-stack bookkeeping uniform).
    // K always fits u32 when non-negative: limit ≤ 2^32 and size ≥ 1.
    // Under `MemBounds::Unchecked` (explicit opt-out) no check is emitted.
    let bounds_check = |words: &mut Vec<u32>,
                        stack: &mut Vec<Val>,
                        addr: Reg,
                        offset: u32,
                        size_log2: u32|
     -> Result<(), SelectError> {
        let MemBounds::Software { limit_bytes } = bounds else {
            return Ok(());
        };
        let size = 1u64 << size_log2;
        let k = limit_bytes as i64 - offset as i64 - size as i64;
        if k < 0 {
            words.push(enc::brk(0));
            return Ok(());
        }
        // Keep `addr` live while allocating the limit scratch so they are
        // guaranteed distinct registers.
        stack.push(Val::gp(addr));
        let ktmp = alloc_temp(stack)?;
        stack.pop();
        for w in enc::mov_imm32(ktmp, k as u32) {
            words.push(w);
        }
        words.push(enc::cmp(addr, ktmp));
        words.push(enc::bcond(Cond::Ls, 2)); // in-bounds: hop over the brk
        words.push(enc::brk(0)); // OOB trap
        Ok(())
    };

    // In-bounds load/store is execution-verified vs wasmtime; the OOB-trap
    // check above is #865 (see `MemBounds`). Data-segment init and
    // memory.{size,grow} are the remaining documented follow-ons.
    let form_ea = |words: &mut Vec<u32>,
                   stack: &mut Vec<Val>,
                   addr: Reg,
                   offset: u32,
                   size_log2: u32|
     -> Result<(Reg, Option<u32>), SelectError> {
        // #865: prove the access in-bounds (or trap) BEFORE clobbering any
        // register — `addr` is still intact here.
        bounds_check(words, stack, addr, offset, size_log2)?;
        // The address operand is popped; its register is now free. Allocate the
        // EA temp against the CURRENT live stack (addr already removed).
        let ea = alloc_temp(stack)?;
        // x_ea = x28 + uxtw(w_addr) — zero-extends the unsigned i32 WASM address.
        words.push(enc::add_ext_uxtw(ea, LINMEM_BASE, addr));
        let size = 1u32 << size_log2;
        if offset.is_multiple_of(size) && (offset >> size_log2) < 4096 {
            return Ok((ea, Some(offset >> size_log2)));
        }
        if offset != 0 {
            // Offset does not fit the scaled immediate: materialize it in a
            // second temp and add. `alloc_temp` against the stack with `ea`
            // temporarily marked live picks a DISTINCT register.
            stack.push(Val::gp(ea));
            let otmp = alloc_temp(stack)?;
            stack.pop();
            for w in enc::mov_imm32(otmp, offset) {
                words.push(w);
            }
            words.push(enc::add_ext_uxtw(ea, ea, otmp)); // ea += uxtw(offset)
        }
        Ok((ea, None))
    };

    // A GP load: pop the i32 address, dereference `[base + addr + offset]` with
    // `ldr_op`, push the loaded value (zero/sign extension is baked into the op).
    let load = |words: &mut Vec<u32>,
                stack: &mut Vec<Val>,
                offset: u32,
                size_log2: u32,
                ldr_op: fn(Reg, Reg, u32) -> u32|
     -> Result<(), SelectError> {
        let addr = pop_gp(stack, "load")?;
        let (ea, imm) = form_ea(words, stack, addr, offset, size_log2)?;
        let dst = ea; // load target may reuse the EA register (read-before-write)
        words.push(ldr_op(dst, ea, imm.unwrap_or(0)));
        stack.push(Val::gp(dst));
        Ok(())
    };

    // A GP store: pop the value (top of stack) then the i32 address, store the
    // low `size` bytes of the value to `[base + addr + offset]`.
    let store = |words: &mut Vec<u32>,
                 stack: &mut Vec<Val>,
                 offset: u32,
                 size_log2: u32,
                 str_op: fn(Reg, Reg, u32) -> u32|
     -> Result<(), SelectError> {
        let val = pop_gp(stack, "store")?;
        let addr = pop_gp(stack, "store")?;
        // Keep `val` live across the EA temp allocation so `form_ea` never hands
        // back the value register.
        stack.push(Val::gp(val));
        let (ea, imm) = form_ea(words, stack, addr, offset, size_log2)?;
        stack.pop(); // release `val`
        words.push(str_op(val, ea, imm.unwrap_or(0)));
        Ok(())
    };

    // v0.54 L2 (#851) — an FP load: pop the i32 address, dereference
    // `[x28 + uxtw(addr) + offset]` with the SIMD&FP `ldr s/d`, push the value
    // into the FP file.
    //
    // The address arithmetic and the #865 SOFTWARE BOUNDS CHECK are the SAME
    // `form_ea` the integer loads use — an FP access is bounds-checked by
    // default exactly like an i32 one, and traps (`brk`) where wasmtime traps.
    // Only the data register file differs: the destination is a fresh FP temp,
    // so the GP `ea` temp is free again the instant the load retires.
    let fload = |words: &mut Vec<u32>,
                 stack: &mut Vec<Val>,
                 offset: u32,
                 size_log2: u32,
                 ldr_op: fn(FReg, Reg, u32) -> u32|
     -> Result<(), SelectError> {
        let addr = pop_gp(stack, "fload")?;
        let (ea, imm) = form_ea(words, stack, addr, offset, size_log2)?;
        // The FP destination lives in a DIFFERENT file than `ea`, so it cannot
        // alias it — no read-before-write reuse trick is needed (or possible).
        let dst = alloc_ftemp(stack)?;
        words.push(ldr_op(dst, ea, imm.unwrap_or(0)));
        stack.push(Val::fp(dst));
        Ok(())
    };

    // v0.54 L2 (#851) — an FP store: pop the FP value, then the i32 address,
    // and write `size` bytes to `[x28 + uxtw(addr) + offset]`. Bounds-checked
    // by the shared `form_ea` (#865). Unlike the GP store there is no need to
    // keep the value artificially live across the EA allocation: `form_ea`
    // hands out GP temps only, and the value lives in the FP file.
    let fstore = |words: &mut Vec<u32>,
                  stack: &mut Vec<Val>,
                  offset: u32,
                  size_log2: u32,
                  str_op: fn(FReg, Reg, u32) -> u32|
     -> Result<(), SelectError> {
        let val = pop_fp(stack, "fstore")?;
        let addr = pop_gp(stack, "fstore")?;
        let (ea, imm) = form_ea(words, stack, addr, offset, size_log2)?;
        words.push(str_op(val, ea, imm.unwrap_or(0)));
        Ok(())
    };

    for op in ops {
        match op {
            WasmOp::LocalGet(i) => {
                if slot_resident(*i) {
                    // Non-param local (#851): LOAD its stack slot into a FRESH GP
                    // temp — a copy, so a later `local.set` of the same index
                    // cannot alias this value. 64-bit load (both i32 and i64 read
                    // back correctly; an i32 producer wrote the low half and the
                    // slot was zeroed, so the upper half is clean).
                    let dst = alloc_temp(&stack)?;
                    words.push(enc::ldr_x_imm(dst, enc::SP, local_slot_off(*i)));
                    stack.push(Val::gp(dst));
                } else {
                    // Resolve the param to its AAPCS64 register + file (GP or FP).
                    stack.push(params[*i as usize]);
                }
            }
            // `local.set i` — pop the top value and store it into local `i`.
            // Every local a body writes is slot-resident: non-param locals
            // always, and a written PARAM because `writes_param` forces
            // `home_params` (RQ-57-A64PARAM, #851). The `else` is therefore an
            // INTERNAL INVARIANT, kept as a loud error rather than deleted so a
            // future change to the homing predicate cannot silently drop a
            // store.
            WasmOp::LocalSet(i) => {
                if slot_resident(*i) {
                    let src = pop_gp(&mut stack, "local.set")?;
                    words.push(enc::str_x_imm(src, enc::SP, local_slot_off(*i)));
                } else {
                    return Err(SelectError(format!(
                        "internal: local.set {i} targets a local with no home slot \
                         (num_params={num_params}, home_params={home_params}) — the \
                         homing predicate and the slot model disagree (#851)"
                    )));
                }
            }
            // `local.tee i` — like `local.set` but leaves the value on the stack.
            // Store the top value WITHOUT popping it (peek + `str`). Same
            // slot-residency invariant as `local.set`.
            WasmOp::LocalTee(i) => {
                if slot_resident(*i) {
                    let top = *stack
                        .last()
                        .ok_or_else(|| SelectError("local.tee underflow".into()))?;
                    if top.file != File::Gp {
                        return Err(SelectError("local.tee: expected GP operand, got FP".into()));
                    }
                    words.push(enc::str_x_imm(top.reg, enc::SP, local_slot_off(*i)));
                } else {
                    return Err(SelectError(format!(
                        "internal: local.tee {i} targets a local with no home slot \
                         (num_params={num_params}, home_params={home_params}) — the \
                         homing predicate and the slot model disagree (#851)"
                    )));
                }
            }
            WasmOp::I32Const(c) => {
                let dst = alloc_temp(&stack)?;
                for w in enc::mov_imm32(dst, *c as u32) {
                    words.push(w);
                }
                stack.push(Val::gp(dst));
            }
            WasmOp::I64Const(c) => {
                let dst = alloc_temp(&stack)?;
                for w in enc::mov_imm64(dst, *c as u64) {
                    words.push(w);
                }
                stack.push(Val::gp(dst));
            }
            // f32/f64 const: materialize the bit-pattern in a GP temp, then FMOV
            // it into an FP temp (there is no direct FP immediate for arbitrary
            // constants). The GP temp is transient (freed before the push).
            WasmOp::F32Const(c) => {
                let gp = alloc_temp(&stack)?;
                for w in enc::mov_imm32(gp, c.to_bits()) {
                    words.push(w);
                }
                let dst = alloc_ftemp(&stack)?;
                words.push(enc::fmov_s_from_w(dst, gp));
                stack.push(Val::fp(dst));
            }
            WasmOp::F64Const(c) => {
                let gp = alloc_temp(&stack)?;
                for w in enc::mov_imm64(gp, c.to_bits()) {
                    words.push(w);
                }
                let dst = alloc_ftemp(&stack)?;
                words.push(enc::fmov_d_from_x(dst, gp));
                stack.push(Val::fp(dst));
            }
            // #665: wasm `unreachable` traps unconditionally (WASM §4.4.5) —
            // `brk #0`, the A64 analogue of Thumb-2 `udf #0` / RV32 `ebreak`.
            WasmOp::Unreachable => {
                words.push(enc::brk(0));
                // `unreachable` traps unconditionally: fall-through is dead.
                reachable = false;
            }

            // --- control flow (#538 cf increment; VCR-A64-CF-001 value-carrying) ---
            //
            // `block` opens a new control frame. Since VCR-A64-CF-001 a
            // VALUE-CARRYING `(0,1)` block is accepted as well as the void
            // `(0,0)` one: it reserves a reconciliation register that every
            // path deposits its result into (see [`reconcile_into`]). Block
            // PARAMETERS and MULTI-VALUE results still loud-decline by name.
            // The arity comes from the decoder's ordinal side-table
            // (`unreachable`-polymorphic fall-through makes a stack-height
            // proxy UNSOUND — the arity table is the signal).
            WasmOp::Block => {
                let ord = ctrl_ord;
                ctrl_ord += 1;
                let arity = block_arity.get(ord).copied().unwrap_or((0, 0));
                let (label_arity, result_arity, slot) =
                    open_slot("block", ord, arity, false, &stack)?;
                ctrl.push(Frame {
                    kind: Kind::Block,
                    pending: Vec::new(),
                    stack_entry: stack.len(),
                    label_arity,
                    result_arity,
                    slot,
                });
            }
            // `br N` — unconditional branch to the END of the block N levels out.
            // A forward branch to a void block: emit `b <placeholder>`, record its
            // position for fix-up at that block's `End`. Ops after `br` up to the
            // enclosing `End` are unreachable (WASM stack-polymorphic) — the
            // selector still lowers them, but the branch skips them at runtime.
            WasmOp::Br(depth) => {
                let d = *depth as usize;
                if d >= ctrl.len() {
                    return Err(SelectError(format!(
                        "br {depth}: target depth exceeds open block nesting \
                         ({} open) — only branches to enclosing blocks are \
                         supported (a branch to the function body is not)",
                        ctrl.len()
                    )));
                }
                let target = ctrl.len() - 1 - d;
                // VCR-A64-CF-001 — a branch to a VALUE-CARRYING label hands the
                // label its result: move the top-of-stack into the target
                // frame's reserved register FIRST, so the join reads one
                // register on every incoming edge.
                reconcile_branch(&mut words, &mut ctrl, &stack, target, "br")?;
                let pos = words.len();
                if let Kind::Loop { entry } = ctrl[target].kind {
                    // BACKWARD branch to the loop header — resolve immediately.
                    let off = check_imm26((entry as i64 - pos as i64) as i32)?;
                    words.push(enc::b_uncond(off));
                } else {
                    // FORWARD branch to a block/if END — patched at that `End`.
                    words.push(enc::b_uncond(0)); // placeholder
                    ctrl[target].pending.push(pos);
                }
                // Unconditional transfer: fall-through is unreachable.
                reachable = false;
            }
            // `br_if N` — pop an i32 condition; branch to the block-N END iff it
            // is nonzero → `cbnz w_cond, <block-end>`. Not-taken falls through.
            WasmOp::BrIf(depth) => {
                let d = *depth as usize;
                if d >= ctrl.len() {
                    return Err(SelectError(format!(
                        "br_if {depth}: target depth exceeds open block nesting \
                         ({} open)",
                        ctrl.len()
                    )));
                }
                let cond = pop_gp(&mut stack, "br_if")?;
                let target = ctrl.len() - 1 - d;
                // VCR-A64-CF-001 — the condition sat ABOVE the branch's result,
                // so reconcile only after popping it. PEEK, don't pop: the
                // not-taken path still owns the value.
                reconcile_branch(&mut words, &mut ctrl, &stack, target, "br_if")?;
                let pos = words.len();
                if let Kind::Loop { entry } = ctrl[target].kind {
                    // BACKWARD conditional branch to the loop header.
                    let off = check_imm19((entry as i64 - pos as i64) as i32)?;
                    words.push(enc::cbnz(cond, off));
                } else {
                    // FORWARD conditional branch to a block/if END.
                    words.push(enc::cbnz(cond, 0)); // placeholder; patched at End
                    ctrl[target].pending.push(pos);
                }
            }
            // `br_table` (VCR-A64-CF-001) — WASM's multi-way branch: pop the
            // i32 index; index `i` branches to `targets[i]`, and ANY index
            // `>= targets.len()` goes to `default`. The index is UNSIGNED, so
            // the "negative" i32s are huge unsigned values and also land on
            // the default label.
            //
            // Lowering: a COMPARE-AND-BRANCH CHAIN, deliberately the same
            // construction #882 chose for RV32 so the two backends stay
            // reviewable against each other. Entry 0 is `cbz w_idx, L0` (one
            // instruction, no constant to materialize); every further entry is
            // `cmp w_idx, #i` + `b.eq L_i`; the chain ends in an unconditional
            // `b L_default`, which is exactly where every non-matching index —
            // in-range-of-i32 or not — lands. The compares are the W view, so
            // a dirty upper half (an i64 producer feeding the index) cannot
            // affect the dispatch, and equality against the constants
            // `0..len-1` is exact for the unsigned-index semantics.
            //
            // Targets may MIX destinations: a `loop` target is the loop HEADER
            // (backward, resolved eagerly to a negative offset) while a
            // block/if target is its END (forward, patched at that `End`) —
            // the same dispatch-on-the-TARGET-frame's-kind rule `br`/`br_if`
            // already use.
            //
            // No jump table, no data section, no PC-relative table: for the
            // small tables real drivers carry, the chain is smaller and simpler
            // to verify than an indirect dispatch. Past
            // [`BR_TABLE_MAX_TARGETS`] it LOUD-DECLINES rather than emit an
            // unbounded chain — the jump-table upgrade is a named follow-up.
            WasmOp::BrTable { targets, default } => {
                if targets.len() > BR_TABLE_MAX_TARGETS {
                    return Err(SelectError(format!(
                        "br_table with {} targets exceeds the aarch64 \
                         compare-chain threshold ({BR_TABLE_MAX_TARGETS}); \
                         PC-relative jump-table dispatch is not implemented for \
                         aarch64 — loud-declining (VCR-A64-CF-001)",
                        targets.len()
                    )));
                }
                let idx = pop_gp(&mut stack, "br_table")?;
                // Conservative VALUE-CARRYING guard (#509 class, mirroring the
                // RV32 #882 rule). A flat compare chain has no room for a
                // per-path result move: the deposit would have to sit on the
                // TAKEN edge of each individual compare. So every targeted
                // frame (the default included) must have a VOID label and must
                // have been entered at exactly the current post-pop height —
                // then a taken branch moves no values and the plain-jump
                // lowering is sound.
                let height = stack.len();
                for &depth in targets.iter().chain(std::iter::once(default)) {
                    let d = depth as usize;
                    if d >= ctrl.len() {
                        return Err(SelectError(format!(
                            "br_table target depth {depth} exceeds open block \
                             nesting ({} open)",
                            ctrl.len()
                        )));
                    }
                    let frame = &ctrl[ctrl.len() - 1 - d];
                    if frame.label_arity != 0 || frame.stack_entry != height {
                        return Err(SelectError(format!(
                            "br_table with VALUE-CARRYING targets (target depth \
                             {depth}: label arity {}, frame entry height {} vs \
                             post-pop height {height}) — the flat compare chain \
                             has no per-path edge to deposit a result on; \
                             loud-declining (VCR-A64-CF-001, the #509 class)",
                            frame.label_arity, frame.stack_entry
                        )));
                    }
                }
                // The chain. `idx` was popped, so no value-stack entry holds it
                // and nothing below can be disturbed.
                for (i, &depth) in targets.iter().enumerate() {
                    let target = ctrl.len() - 1 - depth as usize;
                    if i > 0 {
                        // i <= BR_TABLE_MAX_TARGETS - 1 always fits imm12.
                        words.push(enc::cmp_imm(idx, i as u32));
                    }
                    let pos = words.len();
                    if let Kind::Loop { entry } = ctrl[target].kind {
                        let off = check_imm19((entry as i64 - pos as i64) as i32)?;
                        words.push(if i == 0 {
                            enc::cbz(idx, off)
                        } else {
                            enc::bcond(Cond::Eq, off)
                        });
                    } else {
                        words.push(if i == 0 {
                            enc::cbz(idx, 0) // placeholder; patched at End
                        } else {
                            enc::bcond(Cond::Eq, 0) // placeholder; patched at End
                        });
                        ctrl[target].pending.push(pos);
                    }
                }
                // No entry matched → default. Also where every out-of-range
                // (unsigned) index lands.
                let dflt = ctrl.len() - 1 - *default as usize;
                let pos = words.len();
                if let Kind::Loop { entry } = ctrl[dflt].kind {
                    let off = check_imm26((entry as i64 - pos as i64) as i32)?;
                    words.push(enc::b_uncond(off));
                } else {
                    words.push(enc::b_uncond(0)); // placeholder
                    ctrl[dflt].pending.push(pos);
                }
                // Every index transfers control: the fall-through is dead.
                reachable = false;
            }
            // `loop` (#851): opens a control frame whose branch target is the
            // loop HEADER (the current position), so a `br`/`br_if` to it is a
            // BACKWARD branch.
            //
            // VCR-A64-CF-001 — a `loop (result T)` is now accepted, and the
            // asymmetry with `block` is SOUNDNESS-CRITICAL rather than
            // cosmetic: a branch to a LOOP label targets the header and carries
            // the loop's PARAMETERS, not its results. `open_slot(is_loop=true)`
            // therefore sets `label_arity = params` (0 here), so the back-edge
            // reconciles NOTHING and the reserved register is written by the
            // fall-through `End` alone. Reconciling on the back-edge — the
            // natural wrong implementation, and what treating `label_arity` as
            // "the frame is value-carrying" would do — would stamp a garbage
            // value into the result register on every iteration.
            //
            // Loop PARAMETERS still loud-decline: they would need the value
            // stack live across the back-edge, and the deterministic
            // temp-restart (`alloc_temp` picks the same register at the same
            // height) would no longer hold. Loop-carried state must live in
            // non-param LOCAL SLOTS (memory), reloaded each iteration.
            WasmOp::Loop => {
                let ord = ctrl_ord;
                ctrl_ord += 1;
                let arity = block_arity.get(ord).copied().unwrap_or((0, 0));
                let (label_arity, result_arity, slot) =
                    open_slot("loop", ord, arity, true, &stack)?;
                ctrl.push(Frame {
                    kind: Kind::Loop { entry: words.len() },
                    pending: Vec::new(),
                    stack_entry: stack.len(),
                    label_arity,
                    result_arity,
                    slot,
                });
            }
            // `if` (#851): pop the i32 condition; emit `cbz cond, <else/end>` to
            // SKIP the then-arm when the condition is false. The skip target is
            // patched at the matching `else` (to the else-arm entry) or, if
            // there is no `else`, at `end` (past the then-arm). VCR-A64-CF-001:
            // a value-producing `(0,1)` `if` is now accepted — "both arms must
            // land the result in one register" is exactly what the reserved
            // reconciliation slot guarantees (the then-arm deposits at `else`,
            // the else-arm at `end`).
            WasmOp::If => {
                let ord = ctrl_ord;
                ctrl_ord += 1;
                let arity = block_arity.get(ord).copied().unwrap_or((0, 0));
                let cond = pop_gp(&mut stack, "if")?;
                // Reserve AFTER popping the condition so the condition's temp
                // is a candidate for the slot (it is dead from here on).
                let (label_arity, result_arity, slot) = open_slot("if", ord, arity, false, &stack)?;
                let else_pos = words.len();
                // cbz: fall THROUGH into the then-arm when cond != 0; branch to
                // the else/end when cond == 0. Offset patched at else/end.
                words.push(enc::cbz(cond, 0)); // placeholder
                ctrl.push(Frame {
                    kind: Kind::If {
                        else_fixup: Some(else_pos),
                    },
                    pending: Vec::new(),
                    stack_entry: stack.len(),
                    label_arity,
                    result_arity,
                    slot,
                });
            }
            // `else` (#851): closes the then-arm of the innermost `if`. Emit an
            // unconditional `b <end>` to skip the else-arm at runtime (recorded
            // in `pending`, patched at `end`), then patch the `if`'s pending
            // `cbz` to land HERE (the else-arm entry). The value stack is reset
            // to the if's entry height (a void then-arm must not leave a value).
            WasmOp::Else => {
                let frame = ctrl
                    .last_mut()
                    .ok_or_else(|| SelectError("else without a matching if".into()))?;
                let else_fixup = match &mut frame.kind {
                    Kind::If { else_fixup } => else_fixup
                        .take()
                        .ok_or_else(|| SelectError("duplicate else for one if".into()))?,
                    _ => {
                        return Err(SelectError("else does not close an if block".into()));
                    }
                };
                // VCR-A64-CF-001 — a value-producing then-arm hands the join
                // its result here, immediately before the `b end` below (the
                // no-clobber-window property [`reconcile_into`] documents).
                if frame.result_arity == 1 && reachable {
                    let v = *stack.last().ok_or_else(|| {
                        SelectError(
                            "else: value-producing then-arm left no result on \
                             the value stack"
                                .into(),
                        )
                    })?;
                    let slot = frame.slot.as_mut().ok_or_else(|| {
                        SelectError(
                            "else: value-carrying if has no reconciliation slot \
                             (internal invariant)"
                                .into(),
                        )
                    })?;
                    reconcile_into(&mut words, slot, v);
                    stack.pop();
                }
                // A void then-arm leaves the stack at its entry height — but
                // only on a REACHABLE fall-through (a then-arm ending in
                // `return`/`br` is polymorphic). Truncate unconditionally (fixes
                // the model); assert only when reachable.
                debug_assert!(
                    !reachable || stack.len() == frame.stack_entry,
                    "void then-arm must restore stack height"
                );
                stack.truncate(frame.stack_entry);
                // The else-arm is a `cbz` target — always reachable.
                reachable = true;
                // Skip the else-arm when the then-arm falls through.
                let skip_pos = words.len();
                words.push(enc::b_uncond(0)); // placeholder; patched at end
                frame.pending.push(skip_pos);
                // The if's cbz now lands at the else-arm entry (current pos).
                let here = words.len();
                patch_branch(&mut words, else_fixup, here)?;
            }
            // `return` (#851): funnel the top-of-stack into x0/d0, tear down the
            // frame, and `ret` — an EARLY function exit. Ops after `return` up
            // to the enclosing `end` are unreachable (WASM stack-polymorphic);
            // the selector still lowers them but this `ret` never falls into
            // them. Mirrors the existing "code after `br` is unreachable but
            // still emitted" model — no shared epilogue label needed.
            WasmOp::Return => {
                epilogue(&mut words, stack.last().copied(), frame_size, is_non_leaf);
                // Unconditional transfer: fall-through is unreachable.
                reachable = false;
            }

            // --- i32 arithmetic / bitwise ---
            WasmOp::I32Add => binop(&mut words, &mut stack, enc::add)?,
            WasmOp::I32Sub => binop(&mut words, &mut stack, enc::sub)?,
            WasmOp::I32Mul => binop(&mut words, &mut stack, enc::mul)?,
            WasmOp::I32And => binop(&mut words, &mut stack, enc::and)?,
            WasmOp::I32Or => binop(&mut words, &mut stack, enc::orr)?,
            WasmOp::I32Xor => binop(&mut words, &mut stack, enc::eor)?,
            WasmOp::I32Shl => binop(&mut words, &mut stack, enc::lslv)?,
            WasmOp::I32ShrU => binop(&mut words, &mut stack, enc::lsrv)?,
            WasmOp::I32ShrS => binop(&mut words, &mut stack, enc::asrv)?,
            WasmOp::I32Rotr => binop(&mut words, &mut stack, enc::rorv)?,
            WasmOp::I32Rotl => rotl(&mut words, &mut stack, false)?,
            WasmOp::I32Clz => unop(&mut words, &mut stack, enc::clz)?,
            WasmOp::I32Ctz => ctz(&mut words, &mut stack, false)?,
            WasmOp::I32Popcnt => popcnt(&mut words, &mut stack, false)?,
            // #851 — i32 divide / remainder (SDIV/UDIV + MSUB) with the WASM
            // trap guards (÷0 all forms; INT_MIN/-1 signed-div only).
            WasmOp::I32DivS => divrem(&mut words, &mut stack, true, false, false)?,
            WasmOp::I32DivU => divrem(&mut words, &mut stack, false, false, false)?,
            WasmOp::I32RemS => divrem(&mut words, &mut stack, true, false, true)?,
            WasmOp::I32RemU => divrem(&mut words, &mut stack, false, false, true)?,

            // --- i32 comparisons ---
            WasmOp::I32Eqz => eqz(&mut words, &mut stack, false)?,
            WasmOp::I32Eq => cmp_op(&mut words, &mut stack, false, Cond::Eq)?,
            WasmOp::I32Ne => cmp_op(&mut words, &mut stack, false, Cond::Ne)?,
            WasmOp::I32LtS => cmp_op(&mut words, &mut stack, false, Cond::Lt)?,
            WasmOp::I32LtU => cmp_op(&mut words, &mut stack, false, Cond::Lo)?,
            WasmOp::I32LeS => cmp_op(&mut words, &mut stack, false, Cond::Le)?,
            WasmOp::I32LeU => cmp_op(&mut words, &mut stack, false, Cond::Ls)?,
            WasmOp::I32GtS => cmp_op(&mut words, &mut stack, false, Cond::Gt)?,
            WasmOp::I32GtU => cmp_op(&mut words, &mut stack, false, Cond::Hi)?,
            WasmOp::I32GeS => cmp_op(&mut words, &mut stack, false, Cond::Ge)?,
            WasmOp::I32GeU => cmp_op(&mut words, &mut stack, false, Cond::Hs)?,

            // --- i64 arithmetic / bitwise ---
            WasmOp::I64Add => binop(&mut words, &mut stack, enc::add64)?,
            WasmOp::I64Sub => binop(&mut words, &mut stack, enc::sub64)?,
            WasmOp::I64Mul => binop(&mut words, &mut stack, enc::mul64)?,
            WasmOp::I64And => binop(&mut words, &mut stack, enc::and64)?,
            WasmOp::I64Or => binop(&mut words, &mut stack, enc::orr64)?,
            WasmOp::I64Xor => binop(&mut words, &mut stack, enc::eor64)?,
            WasmOp::I64Shl => binop(&mut words, &mut stack, enc::lslv64)?,
            WasmOp::I64ShrU => binop(&mut words, &mut stack, enc::lsrv64)?,
            WasmOp::I64ShrS => binop(&mut words, &mut stack, enc::asrv64)?,
            WasmOp::I64Rotr => binop(&mut words, &mut stack, enc::rorv64)?,
            WasmOp::I64Rotl => rotl(&mut words, &mut stack, true)?,
            WasmOp::I64Clz => unop(&mut words, &mut stack, enc::clz64)?,
            WasmOp::I64Ctz => ctz(&mut words, &mut stack, true)?,
            WasmOp::I64Popcnt => popcnt(&mut words, &mut stack, true)?,
            // #851 — i64 divide / remainder (x-form SDIV/UDIV + MSUB) with the
            // WASM trap guards (÷0 all forms; INT64_MIN/-1 signed-div only).
            WasmOp::I64DivS => divrem(&mut words, &mut stack, true, true, false)?,
            WasmOp::I64DivU => divrem(&mut words, &mut stack, false, true, false)?,
            WasmOp::I64RemS => divrem(&mut words, &mut stack, true, true, true)?,
            WasmOp::I64RemU => divrem(&mut words, &mut stack, false, true, true)?,

            // --- i64 comparisons (result is an i32 0/1) ---
            WasmOp::I64Eqz => eqz(&mut words, &mut stack, true)?,
            WasmOp::I64Eq => cmp_op(&mut words, &mut stack, true, Cond::Eq)?,
            WasmOp::I64Ne => cmp_op(&mut words, &mut stack, true, Cond::Ne)?,
            WasmOp::I64LtS => cmp_op(&mut words, &mut stack, true, Cond::Lt)?,
            WasmOp::I64LtU => cmp_op(&mut words, &mut stack, true, Cond::Lo)?,
            WasmOp::I64LeS => cmp_op(&mut words, &mut stack, true, Cond::Le)?,
            WasmOp::I64LeU => cmp_op(&mut words, &mut stack, true, Cond::Ls)?,
            WasmOp::I64GtS => cmp_op(&mut words, &mut stack, true, Cond::Gt)?,
            WasmOp::I64GtU => cmp_op(&mut words, &mut stack, true, Cond::Hi)?,
            WasmOp::I64GeS => cmp_op(&mut words, &mut stack, true, Cond::Ge)?,
            WasmOp::I64GeU => cmp_op(&mut words, &mut stack, true, Cond::Hs)?,

            // --- f32 arithmetic ---
            WasmOp::F32Add => fbinop(&mut words, &mut stack, enc::fadd_s)?,
            WasmOp::F32Sub => fbinop(&mut words, &mut stack, enc::fsub_s)?,
            WasmOp::F32Mul => fbinop(&mut words, &mut stack, enc::fmul_s)?,
            WasmOp::F32Div => fbinop(&mut words, &mut stack, enc::fdiv_s)?,
            WasmOp::F32Abs => funop(&mut words, &mut stack, enc::fabs_s)?,
            WasmOp::F32Neg => funop(&mut words, &mut stack, enc::fneg_s)?,
            WasmOp::F32Sqrt => funop(&mut words, &mut stack, enc::fsqrt_s)?,

            // --- f32 comparisons (result is a GP i32 0/1; NaN-correct conds) ---
            WasmOp::F32Eq => fcmp_op(&mut words, &mut stack, enc::fcmp_s, Cond::Eq)?,
            WasmOp::F32Ne => fcmp_op(&mut words, &mut stack, enc::fcmp_s, Cond::Ne)?,
            WasmOp::F32Lt => fcmp_op(&mut words, &mut stack, enc::fcmp_s, Cond::Mi)?,
            WasmOp::F32Le => fcmp_op(&mut words, &mut stack, enc::fcmp_s, Cond::Ls)?,
            WasmOp::F32Gt => fcmp_op(&mut words, &mut stack, enc::fcmp_s, Cond::Gt)?,
            WasmOp::F32Ge => fcmp_op(&mut words, &mut stack, enc::fcmp_s, Cond::Ge)?,

            // --- f64 arithmetic ---
            WasmOp::F64Add => fbinop(&mut words, &mut stack, enc::fadd_d)?,
            WasmOp::F64Sub => fbinop(&mut words, &mut stack, enc::fsub_d)?,
            WasmOp::F64Mul => fbinop(&mut words, &mut stack, enc::fmul_d)?,
            WasmOp::F64Div => fbinop(&mut words, &mut stack, enc::fdiv_d)?,
            WasmOp::F64Abs => funop(&mut words, &mut stack, enc::fabs_d)?,
            WasmOp::F64Neg => funop(&mut words, &mut stack, enc::fneg_d)?,
            WasmOp::F64Sqrt => funop(&mut words, &mut stack, enc::fsqrt_d)?,

            // --- f64 comparisons ---
            WasmOp::F64Eq => fcmp_op(&mut words, &mut stack, enc::fcmp_d, Cond::Eq)?,
            WasmOp::F64Ne => fcmp_op(&mut words, &mut stack, enc::fcmp_d, Cond::Ne)?,
            WasmOp::F64Lt => fcmp_op(&mut words, &mut stack, enc::fcmp_d, Cond::Mi)?,
            WasmOp::F64Le => fcmp_op(&mut words, &mut stack, enc::fcmp_d, Cond::Ls)?,
            WasmOp::F64Gt => fcmp_op(&mut words, &mut stack, enc::fcmp_d, Cond::Gt)?,
            WasmOp::F64Ge => fcmp_op(&mut words, &mut stack, enc::fcmp_d, Cond::Ge)?,

            // --- f32/f64 min/max (m4): A64 FMIN/FMAX are IEEE 754-2019
            // minimum/maximum — NaN-propagating, -0.0 < +0.0 — exactly WASM's
            // semantics (execution-verified vs wasmtime, NaN/±0 matrix). ---
            WasmOp::F32Min => fbinop(&mut words, &mut stack, enc::fmin_s)?,
            WasmOp::F32Max => fbinop(&mut words, &mut stack, enc::fmax_s)?,
            WasmOp::F64Min => fbinop(&mut words, &mut stack, enc::fmin_d)?,
            WasmOp::F64Max => fbinop(&mut words, &mut stack, enc::fmax_d)?,

            // --- copysign (m4): pure bit surgery through the GP file ---
            WasmOp::F32Copysign => copysign(&mut words, &mut stack, false)?,
            WasmOp::F64Copysign => copysign(&mut words, &mut stack, true)?,

            // --- v0.54 L2 (#851): round-to-integral (ceil/floor/trunc/nearest).
            //
            // One `FRINT<mode>` each, with the rounding mode pinned in the
            // OPCODE — the lowering never reads FPCR.RMode, so it is correct
            // under whatever rounding mode the embedder left set. All four are
            // TOTAL (WASM §4.3.3 `fceil`/`ffloor`/`ftrunc`/`fnearest` never
            // trap and neither do these), so no domain guard is needed — the
            // "more-total-than-WASM" hazard that forces the trunc guards below
            // simply does not arise for float→float rounding.
            //
            // `nearest` is roundTiesToEven, which is FRINTN (NOT FRINTA, which
            // is ties-AWAY-from-zero) — checked by execution against wasmtime
            // over a halfway table (0.5/1.5/2.5/-0.5/…), not assumed. ---
            WasmOp::F32Ceil => funop(&mut words, &mut stack, enc::frintp_s)?,
            WasmOp::F32Floor => funop(&mut words, &mut stack, enc::frintm_s)?,
            WasmOp::F32Trunc => funop(&mut words, &mut stack, enc::frintz_s)?,
            WasmOp::F32Nearest => funop(&mut words, &mut stack, enc::frintn_s)?,
            WasmOp::F64Ceil => funop(&mut words, &mut stack, enc::frintp_d)?,
            WasmOp::F64Floor => funop(&mut words, &mut stack, enc::frintm_d)?,
            WasmOp::F64Trunc => funop(&mut words, &mut stack, enc::frintz_d)?,
            WasmOp::F64Nearest => funop(&mut words, &mut stack, enc::frintn_d)?,

            // --- trapping float→int truncations (m4): domain-guarded #709 ---
            WasmOp::I32TruncF32S => trunc_guarded(&mut words, &mut stack, false, true, false)?,
            WasmOp::I32TruncF32U => trunc_guarded(&mut words, &mut stack, false, false, false)?,
            WasmOp::I32TruncF64S => trunc_guarded(&mut words, &mut stack, true, true, false)?,
            WasmOp::I32TruncF64U => trunc_guarded(&mut words, &mut stack, true, false, false)?,
            // v0.54 L2 (#851): the i64-TARGET trapping forms — the same #709
            // domain guard with the 2^63 / 2^64 boundaries and an `x`
            // destination. Without the guard these would SATURATE where WASM
            // traps (NaN → 0, overflow → INT64_MIN/MAX): the exact silent
            // miscompile the class is named for.
            WasmOp::I64TruncF32S => trunc_guarded(&mut words, &mut stack, false, true, true)?,
            WasmOp::I64TruncF32U => trunc_guarded(&mut words, &mut stack, false, false, true)?,
            WasmOp::I64TruncF64S => trunc_guarded(&mut words, &mut stack, true, true, true)?,
            WasmOp::I64TruncF64U => trunc_guarded(&mut words, &mut stack, true, false, true)?,

            // --- nontrapping saturating truncations (#782a): bare FCVTZ ---
            WasmOp::I32TruncSatF32S => trunc_sat(&mut words, &mut stack, enc::fcvtzs_w_from_s)?,
            WasmOp::I32TruncSatF32U => trunc_sat(&mut words, &mut stack, enc::fcvtzu_w_from_s)?,
            WasmOp::I32TruncSatF64S => trunc_sat(&mut words, &mut stack, enc::fcvtzs_w_from_d)?,
            WasmOp::I32TruncSatF64U => trunc_sat(&mut words, &mut stack, enc::fcvtzu_w_from_d)?,
            WasmOp::I64TruncSatF32S => trunc_sat(&mut words, &mut stack, enc::fcvtzs_x_from_s)?,
            WasmOp::I64TruncSatF32U => trunc_sat(&mut words, &mut stack, enc::fcvtzu_x_from_s)?,
            WasmOp::I64TruncSatF64S => trunc_sat(&mut words, &mut stack, enc::fcvtzs_x_from_d)?,
            WasmOp::I64TruncSatF64U => trunc_sat(&mut words, &mut stack, enc::fcvtzu_x_from_d)?,

            // --- float↔float precision conversions (total, never trap) ---
            WasmOp::F64PromoteF32 => funop(&mut words, &mut stack, enc::fcvt_d_from_s)?,
            WasmOp::F32DemoteF64 => funop(&mut words, &mut stack, enc::fcvt_s_from_d)?,

            // --- int → float conversions (total, never trap) ---
            WasmOp::F32ConvertI32S => cvt_gp_to_fp(&mut words, &mut stack, enc::scvtf_s_from_w)?,
            WasmOp::F32ConvertI32U => cvt_gp_to_fp(&mut words, &mut stack, enc::ucvtf_s_from_w)?,
            WasmOp::F64ConvertI32S => cvt_gp_to_fp(&mut words, &mut stack, enc::scvtf_d_from_w)?,
            WasmOp::F64ConvertI32U => cvt_gp_to_fp(&mut words, &mut stack, enc::ucvtf_d_from_w)?,
            // v0.54 L2 (#851): the i64-SOURCE converts — the `x`-form SCVTF/
            // UCVTF. Also TOTAL: every i64 has a nearest f32/f64, and the
            // rounding A64 applies when the value exceeds the destination's
            // exact-integer range (2^24 for f32, 2^53 for f64) is
            // round-to-nearest-EVEN, which is what WASM §4.3.2 `convert`
            // specifies. No guard, no decline — but execution-verified over
            // the rounding-tie table (2^53±1, 2^63-1, u64 max, …) rather than
            // assumed, since this is the one place the two could disagree.
            WasmOp::F32ConvertI64S => cvt_gp_to_fp(&mut words, &mut stack, enc::scvtf_s_from_x)?,
            WasmOp::F32ConvertI64U => cvt_gp_to_fp(&mut words, &mut stack, enc::ucvtf_s_from_x)?,
            WasmOp::F64ConvertI64S => cvt_gp_to_fp(&mut words, &mut stack, enc::scvtf_d_from_x)?,
            WasmOp::F64ConvertI64U => cvt_gp_to_fp(&mut words, &mut stack, enc::ucvtf_d_from_x)?,

            // --- bit-cast reinterprets (pure FMOV, no numeric change) ---
            WasmOp::F32ReinterpretI32 => {
                reinterpret_gp_to_fp(&mut words, &mut stack, enc::fmov_s_from_w)?
            }
            WasmOp::I32ReinterpretF32 => {
                reinterpret_fp_to_gp(&mut words, &mut stack, enc::fmov_w_from_s)?
            }
            // #851 (GI-FPU-001) — f64 <-> i64 bit-cast reinterprets, the 64-bit
            // twins of the f32/i32 pair above (`fmov dd,xn` / `fmov xd,dn`).
            WasmOp::F64ReinterpretI64 => {
                reinterpret_gp_to_fp(&mut words, &mut stack, enc::fmov_d_from_x)?
            }
            WasmOp::I64ReinterpretF64 => {
                reinterpret_fp_to_gp(&mut words, &mut stack, enc::fmov_x_from_d)?
            }

            // `End` is overloaded: it closes the innermost open `block`, or —
            // when no block is open — ends the FUNCTION body (funnel the result
            // into x0/d0 and return).
            WasmOp::End => {
                if let Some(mut frame) = ctrl.pop() {
                    // VCR-A64-CF-001 — the FALL-THROUGH edge of a
                    // value-carrying frame deposits its result. This MUST be
                    // emitted before `here` is taken: the forward branches
                    // reconciled at their own sites, so they have to land PAST
                    // this move, not on it.
                    if frame.result_arity == 1 && reachable {
                        let v = *stack.last().ok_or_else(|| {
                            SelectError(
                                "end: value-carrying block left no result on the \
                                 value stack"
                                    .into(),
                            )
                        })?;
                        let slot = frame.slot.as_mut().ok_or_else(|| {
                            SelectError(
                                "end: value-carrying frame has no reconciliation \
                                 slot (internal invariant)"
                                    .into(),
                            )
                        })?;
                        reconcile_into(&mut words, slot, v);
                        stack.pop();
                    }
                    // Frame close. Every recorded FORWARD branch (block/if exit,
                    // else-arm skip) targets HERE (fall-through). A Loop's
                    // branches were backward and already resolved. Patch each
                    // placeholder via the kind-preserving `patch_branch`.
                    let here = words.len();
                    // An `if` with NO `else`: its `cbz` still needs to skip the
                    // then-arm to here (the fall-through past the then-arm).
                    if let Kind::If {
                        else_fixup: Some(pos),
                    } = frame.kind
                    {
                        patch_branch(&mut words, pos, here)?;
                    }
                    for pos in frame.pending {
                        patch_branch(&mut words, pos, here)?;
                    }
                    // A void frame leaves the value stack exactly as on entry —
                    // but only on a REACHABLE fall-through (a body ending in
                    // `return`/`br` is stack-polymorphic). Truncate always;
                    // assert only when the fall-through is reachable.
                    debug_assert!(
                        !reachable || stack.len() == frame.stack_entry,
                        "void frame must restore stack height: entry={} now={}",
                        frame.stack_entry,
                        stack.len()
                    );
                    stack.truncate(frame.stack_entry);
                    // VCR-A64-CF-001 — release the frame's reservations and
                    // push its value. Every edge into this join has deposited
                    // into the same register, so the frame's result IS that
                    // register. `file` is `None` only when NO edge ever
                    // reconciled (an unreachable-only frame such as
                    // `block (result i32) unreachable end`); the pushed value
                    // is then dead by construction, so the GP default is safe.
                    if let Some(slot) = frame.slot {
                        reserved_gp.set(reserved_gp.get() & !(1u32 << slot.gp));
                        reserved_fp.set(reserved_fp.get() & !(1u32 << slot.fp));
                        stack.push(match slot.file.unwrap_or(File::Gp) {
                            File::Gp => Val::gp(slot.gp),
                            File::Fp => Val::fp(slot.fp),
                        });
                    }
                    // After closing a frame the position is reachable again: a
                    // forward branch could target this fall-through, and a loop's
                    // continuation follows. (A dead nested block would want the
                    // precise `fell_through || had_pending` rule; that only
                    // affects a debug assert, never emitted bytes — noted as a
                    // residual, the wasmtime differential is the correctness
                    // oracle here.)
                    reachable = true;
                } else {
                    epilogue(&mut words, stack.last().copied(), frame_size, is_non_leaf);
                }
            }
            // --- #851 linear-memory load/store ---
            //
            // Effective address = `x28 (base) + uxtw(i32 addr) + memarg.offset`.
            // Loads bake zero/sign extension into the A64 op (`ldrb`=zero-extend,
            // `ldrsb`=sign-extend, etc); stores write the low `size` bytes. The
            // `align` hint is advisory (WASM permits unaligned access) and
            // ignored — A64 unsigned-offset loads/stores are alignment-tolerant.
            // Only single-memory (memory 0) ops are lowered here; a `MultiMemory`
            // wrapper hits the catch-all and loud-declines.
            WasmOp::I32Load { offset, .. } => load(&mut words, &mut stack, *offset, 2, enc::ldr_w)?,
            WasmOp::I32Store { offset, .. } => {
                store(&mut words, &mut stack, *offset, 2, enc::str_w)?
            }
            WasmOp::I32Load8U { offset, .. } => {
                load(&mut words, &mut stack, *offset, 0, enc::ldrb)?
            }
            WasmOp::I32Load8S { offset, .. } => {
                load(&mut words, &mut stack, *offset, 0, enc::ldrsb_w)?
            }
            WasmOp::I32Load16U { offset, .. } => {
                load(&mut words, &mut stack, *offset, 1, enc::ldrh)?
            }
            WasmOp::I32Load16S { offset, .. } => {
                load(&mut words, &mut stack, *offset, 1, enc::ldrsh_w)?
            }
            WasmOp::I32Store8 { offset, .. } => {
                store(&mut words, &mut stack, *offset, 0, enc::strb)?
            }
            WasmOp::I32Store16 { offset, .. } => {
                store(&mut words, &mut stack, *offset, 1, enc::strh)?
            }
            WasmOp::I64Load { offset, .. } => load(&mut words, &mut stack, *offset, 3, enc::ldr_x)?,
            WasmOp::I64Store { offset, .. } => {
                store(&mut words, &mut stack, *offset, 3, enc::str_x)?
            }
            WasmOp::I64Load8U { offset, .. } => {
                load(&mut words, &mut stack, *offset, 0, enc::ldrb)?
            }
            WasmOp::I64Load8S { offset, .. } => {
                load(&mut words, &mut stack, *offset, 0, enc::ldrsb_x)?
            }
            WasmOp::I64Load16U { offset, .. } => {
                load(&mut words, &mut stack, *offset, 1, enc::ldrh)?
            }
            WasmOp::I64Load16S { offset, .. } => {
                load(&mut words, &mut stack, *offset, 1, enc::ldrsh_x)?
            }
            WasmOp::I64Load32U { offset, .. } => {
                load(&mut words, &mut stack, *offset, 2, enc::ldr_w)?
            }
            WasmOp::I64Load32S { offset, .. } => {
                load(&mut words, &mut stack, *offset, 2, enc::ldrsw)?
            }
            WasmOp::I64Store8 { offset, .. } => {
                store(&mut words, &mut stack, *offset, 0, enc::strb)?
            }
            WasmOp::I64Store16 { offset, .. } => {
                store(&mut words, &mut stack, *offset, 1, enc::strh)?
            }
            WasmOp::I64Store32 { offset, .. } => {
                store(&mut words, &mut stack, *offset, 2, enc::str_w)?
            }
            // v0.54 L2 (#851) — f32/f64 linear-memory access. Same address
            // path and same #865 bounds check as the integer forms; only the
            // data register file differs (`ldr/str s` = 4 bytes, `d` = 8).
            // WASM float load/store move BIT PATTERNS, so a NaN payload and
            // the sign of ±0 survive a round-trip intact.
            WasmOp::F32Load { offset, .. } => {
                fload(&mut words, &mut stack, *offset, 2, enc::ldr_s)?
            }
            WasmOp::F32Store { offset, .. } => {
                fstore(&mut words, &mut stack, *offset, 2, enc::str_s)?
            }
            WasmOp::F64Load { offset, .. } => {
                fload(&mut words, &mut stack, *offset, 3, enc::ldr_d)?
            }
            WasmOp::F64Store { offset, .. } => {
                fstore(&mut words, &mut stack, *offset, 3, enc::str_d)?
            }
            // --- #851 direct `call` ---
            //
            // AAPCS64: pop `argc` integer args off the value stack, marshal them
            // into x0..x{argc-1} in order (deepest = x0), `bl func_N` (recorded as
            // an R_AARCH64_CALL26 relocation), then push the x0 result if the
            // callee returns one value. LR is preserved by the non-leaf prologue.
            //
            // SOUNDNESS (v1 scope — everything else loud-declines, never wrong
            // code): a call CLOBBERS all caller-saved registers (x0..x18), so
            // value-stack temps (x9..x15) below the args do NOT survive it. We
            // therefore require the value stack to hold EXACTLY the args at the
            // call (`height == argc`) and decline otherwise. Combined with the
            // non-leaf "no param reads" guard, this leaves every arg in a temp
            // (x9..x15) disjoint from its destination (x0..x7), so the moves need
            // no shuffle. Imports, >8 args, and non-{0,1}-result callees decline.
            WasmOp::Call(func_idx) => {
                let idx = *func_idx;
                if idx < num_imports {
                    return Err(SelectError(format!(
                        "call to imported function {idx} — import dispatch is not \
                         yet supported for aarch64; loud-declining (#851)"
                    )));
                }
                let argc = *func_arg_counts.get(idx as usize).ok_or_else(|| {
                    SelectError(format!("call to function {idx}: unknown arg count"))
                })?;
                if argc > 8 {
                    return Err(SelectError(format!(
                        "call to function {idx}: {argc} args — at most 8 register \
                         args are supported; loud-declining (#851)"
                    )));
                }
                let rc = *func_result_counts.get(idx as usize).ok_or_else(|| {
                    SelectError(format!("call to function {idx}: unknown result count"))
                })?;
                if rc > 1 {
                    return Err(SelectError(format!(
                        "call to function {idx}: {rc} results — multi-result calls \
                         are not supported for aarch64; loud-declining (#851)"
                    )));
                }
                // AAPCS64 returns f32/f64 in v0/d0, NOT x0. A float-returning
                // callee must decline: pushing x0 as the result would read a
                // stale GP register — a silent miscompile. (Float call results
                // are a documented later increment.)
                if rc == 1 && func_ret_float.get(idx as usize).copied().unwrap_or(false) {
                    return Err(SelectError(format!(
                        "call to function {idx}: float result (returned in v0/d0, \
                         not x0) — float call results are not yet supported for \
                         aarch64; loud-declining (#851)"
                    )));
                }
                // The value stack must be EXACTLY the args (nothing survives the
                // clobber underneath). This also guarantees no arg is FP-tagged
                // improperly — an FP arg would need v-register marshalling we do
                // not do, and it is caught here or by the disjointness below.
                if stack.len() != argc as usize {
                    return Err(SelectError(format!(
                        "call to function {idx}: value stack holds {} entries but \
                         needs exactly {argc} (call clobbers caller-saved temps \
                         below the args); loud-declining (#851)",
                        stack.len()
                    )));
                }
                // Args are stack[0..argc] with stack[0] = x0 (deepest arg first).
                // All are GP temps (x9..x15) by the guards above; decline any FP.
                for (arg_reg, v) in stack.iter().enumerate() {
                    if v.file != File::Gp {
                        return Err(SelectError(format!(
                            "call to function {idx}: argument {arg_reg} is a float \
                             — FP call args are not supported for aarch64; \
                             loud-declining (#851)"
                        )));
                    }
                }
                for (arg_reg, v) in stack.iter().enumerate() {
                    if v.reg != arg_reg as u8 {
                        words.push(enc::mov_reg64(arg_reg as u8, v.reg));
                    }
                }
                stack.clear();
                // Record the reloc site (byte offset of the `bl`) then emit `bl 0`.
                call_sites.push(CallSite {
                    offset: (words.len() * 4) as u32,
                    callee: idx,
                });
                words.push(enc::bl(0));
                // Push the result if the callee returns one value. Move x0 into a
                // regular value-stack temp (x9..x15) immediately so the rest of the
                // selector's invariant holds — value-stack entries live in the temp
                // pool, never in x0 (which the epilogue and the next call reuse).
                // i64 fits in x0; the value stack is width-agnostic (op-carried).
                if rc == 1 {
                    let dst = alloc_temp(&stack)?;
                    words.push(enc::mov_reg64(dst, 0));
                    stack.push(Val::gp(dst));
                }
            }
            // --- #851 / VCR-SEL-005 third-backend op-surface closes ---
            //
            // `nop` executes nothing (WASM §4.4.1); no code, no stack effect.
            WasmOp::Nop => {}
            // `drop` pops and discards the top value (either register file);
            // purely a value-stack bookkeeping op, no code emitted.
            WasmOp::Drop => {
                stack
                    .pop()
                    .ok_or_else(|| SelectError("drop underflow".into()))?;
            }
            // `select`: [v1 v2 c] → c != 0 ? v1 : v2 (WASM §4.4.1) — the
            // branchless conditional gale flagged in #851. Lowered to
            // `cmp w_c, wzr` + `csel`/`fcsel` on NE (c nonzero picks v1).
            // Width-agnostic X/D forms carry both i32/i64 (resp. f32/f64)
            // correctly: consumers read the low half through w/s views, the
            // same convention the epilogue and `fmov d0, dN` already use.
            // Both operands must live in the SAME register file (validated
            // wasm guarantees same type; a mismatch here is loud, not silent).
            WasmOp::Select => {
                let cond = pop_gp(&mut stack, "select")?;
                let v2 = stack
                    .pop()
                    .ok_or_else(|| SelectError("select underflow".into()))?;
                let v1 = stack
                    .pop()
                    .ok_or_else(|| SelectError("select underflow".into()))?;
                if v1.file != v2.file {
                    return Err(SelectError(
                        "select: operand register-file mismatch (GP vs FP)".into(),
                    ));
                }
                // cmp reads only `cond`; csel/fcsel read v1/v2 before writing
                // dst (single instruction), so dst may safely reuse any of the
                // three just-popped registers.
                words.push(enc::cmp(cond, enc::WZR));
                match v1.file {
                    File::Gp => {
                        let dst = alloc_temp(&stack)?;
                        words.push(enc::csel64(dst, v1.reg, v2.reg, Cond::Ne));
                        stack.push(Val::gp(dst));
                    }
                    File::Fp => {
                        let dst = alloc_ftemp(&stack)?;
                        words.push(enc::fcsel_d(dst, v1.reg, v2.reg, Cond::Ne));
                        stack.push(Val::fp(dst));
                    }
                }
            }
            // `i32.wrap_i64` — take the low 32 bits. `mov wd, wn` (w-form orr)
            // reads the low half and ZEROES the upper half, so the result is a
            // clean i32 regardless of the source's upper bits.
            WasmOp::I32WrapI64 => unop(&mut words, &mut stack, enc::mov_reg)?,
            // `i64.extend_i32_u` — zero-extend: the same `mov wd, wn` (w-form
            // writes zero-extend to 64 bits by architecture).
            WasmOp::I64ExtendI32U => unop(&mut words, &mut stack, enc::mov_reg)?,
            // `i64.extend_i32_s` / `i64.extend32_s` — sign-extend the low word
            // (SXTW). Reads only the low 32 bits, so garbage upper source bits
            // (e.g. an i32 param's) never leak.
            WasmOp::I64ExtendI32S => unop(&mut words, &mut stack, enc::sxtw)?,
            WasmOp::I64Extend32S => unop(&mut words, &mut stack, enc::sxtw)?,
            // in-place sign extensions (sign-extension operators proposal)
            WasmOp::I32Extend8S => unop(&mut words, &mut stack, enc::sxtb)?,
            WasmOp::I32Extend16S => unop(&mut words, &mut stack, enc::sxth)?,
            WasmOp::I64Extend8S => unop(&mut words, &mut stack, enc::sxtb64)?,
            WasmOp::I64Extend16S => unop(&mut words, &mut stack, enc::sxth64)?,
            // `memory.size` (#851): this backend never lowers a real grow (see
            // MemoryGrow below), so the module's declared minimum IS the
            // runtime size — the same static argument that makes the #865
            // bounds limit sound — and memory.size is the compile-time page
            // count. Needs the limit, so it declines honestly under
            // `--safety-bounds none` (no limit is threaded there).
            WasmOp::MemorySize(mem) => {
                if *mem != 0 {
                    return Err(SelectError(format!(
                        "memory.size on memory {mem}: multi-memory is not \
                         supported for aarch64 (#406) — loud-declining"
                    )));
                }
                let MemBounds::Software { limit_bytes } = bounds else {
                    return Err(SelectError(
                        "memory.size needs the module's memory limit, which is \
                         not threaded under --safety-bounds none — \
                         loud-declining (#851)"
                            .into(),
                    ));
                };
                let dst = alloc_temp(&stack)?;
                for w in enc::mov_imm32(dst, (limit_bytes / 65536) as u32) {
                    words.push(w);
                }
                stack.push(Val::gp(dst));
            }
            // `memory.grow` (#851): the linear memory is a FIXED host buffer of
            // the declared minimum size, so growth always fails — which WASM
            // explicitly permits (§4.4.7: grow MAY fail, returning −1).
            // `grow(0)` trivially succeeds and returns the current page count
            // (grow(0) ≡ size, the #539 rule). Lowered branchless:
            //   mov t0, #pages ; mov t1, #-1 ; cmp delta, wzr ; csel t0 eq
            // Keeping the failure static means the #865 bounds limit stays
            // sound (the limit can never move at runtime).
            WasmOp::MemoryGrow(mem) => {
                if *mem != 0 {
                    return Err(SelectError(format!(
                        "memory.grow on memory {mem}: multi-memory is not \
                         supported for aarch64 (#406) — loud-declining"
                    )));
                }
                let MemBounds::Software { limit_bytes } = bounds else {
                    return Err(SelectError(
                        "memory.grow needs the module's memory limit, which is \
                         not threaded under --safety-bounds none — \
                         loud-declining (#851)"
                            .into(),
                    ));
                };
                let delta = pop_gp(&mut stack, "memory.grow")?;
                // Reserve `delta` so the two scratch temps are distinct from it.
                stack.push(Val::gp(delta));
                let mut free = TEMPS.iter().copied().filter(|t| gp_free(*t, &stack));
                let (Some(t0), Some(t1)) = (free.next(), free.next()) else {
                    stack.pop();
                    return Err(SelectError(
                        "value-stack too deep (memory.grow needs 2 GP temps)".into(),
                    ));
                };
                stack.pop();
                for w in enc::mov_imm32(t0, (limit_bytes / 65536) as u32) {
                    words.push(w);
                }
                for w in enc::mov_imm32(t1, u32::MAX) {
                    words.push(w);
                }
                words.push(enc::cmp(delta, enc::WZR));
                words.push(enc::csel(t0, t0, t1, Cond::Eq));
                stack.push(Val::gp(t0));
            }
            // --- #851 lane L3: WASM globals ------------------------------
            //
            // `global k` lives at `__synth_globals + k*8` in the `.data` region
            // THIS object emits ([`crate::substrate::plan`]). The address is
            // formed PC-relatively (`adrp`+`add :lo12:`), so globals need NO
            // base register and add NO precondition beside `x28`. An i32/f32
            // global occupies the low word of its 8-byte slot (`w` view), an
            // i64/f64 global the whole slot (`x` view). The load/store
            // immediate is size-SCALED, so slot `k*8` is `k*2` for a word
            // access and `k` for a doubleword one.
            WasmOp::GlobalGet(idx) => {
                let is64 = global_slot(ctx, *idx)?;
                let dst = alloc_temp(&stack)?;
                emit_sym_addr(
                    &mut words,
                    &mut sym_relocs,
                    dst,
                    crate::substrate::GLOBALS_SYMBOL,
                );
                // `dst` is read as the base and written as the destination by a
                // SINGLE instruction (read-before-write) — reusing it is safe.
                words.push(if is64 {
                    enc::ldr_x(dst, dst, *idx)
                } else {
                    enc::ldr_w(dst, dst, *idx * 2)
                });
                stack.push(Val::gp(dst));
            }
            WasmOp::GlobalSet(idx) => {
                let is64 = global_slot(ctx, *idx)?;
                let val = pop_gp(&mut stack, "global.set")?;
                // Keep `val` marked live while allocating the base temp, so the
                // two are guaranteed distinct registers.
                stack.push(Val::gp(val));
                let base = alloc_temp(&stack)?;
                stack.pop();
                emit_sym_addr(
                    &mut words,
                    &mut sym_relocs,
                    base,
                    crate::substrate::GLOBALS_SYMBOL,
                );
                words.push(if is64 {
                    enc::str_x(val, base, *idx)
                } else {
                    enc::str_w(val, base, *idx * 2)
                });
            }
            // --- #851 lane L3: `call_indirect` ---------------------------
            //
            // WASM Core §4.4.8 requires THREE traps that A64's `blr` does not
            // give for free — an out-of-range index, a null (uninitialized)
            // slot, and a signature mismatch. All three are emitted here; the
            // table itself is the `.text`-resident trampoline array
            // [`crate::substrate`] describes, one 8-byte
            // `[u32 class id][b func_N]` record per slot (`[0][brk #0]` when
            // null).
            //
            //   cmp  w_idx, #size          ; OOB guard — size is compile-time
            //   b.lo +2                    ; unsigned lower ⇒ in range
            //   brk  #0
            //   adrp x16, __synth_func_table
            //   add  x16, x16, :lo12:…     ; region base (no base register!)
            //   add  x16, x16, w_idx, uxtw #3   ; + idx*8
            //   [add x16, x16, #base*8]    ; + this table's base slot
            //   ldr  w17, [x16]            ; the slot's structural class id
            //   cmp  w17, #expected        ; TYPE check — and, because a null
            //   b.eq +2                    ; slot's id is 0 and expected is
            //   brk  #0                    ; >= 1, the NULL check too
            //   mov  x0..x7, args
            //   add  x16, x16, #4          ; the slot's trampoline
            //   blr  x16
            //
            // The class id is STRUCTURAL, so structurally-equal duplicate
            // types stay interchangeable (§4.4.8) — comparing raw type indices
            // would trap where wasmtime calls.
            WasmOp::CallIndirect {
                type_index,
                table_index,
            } => {
                if !ctx.substrate_emitted {
                    return Err(SelectError(
                        "call_indirect needs the emitted `__synth_func_table` \
                         region, which this compile path does not place — \
                         loud-declining (#851)"
                            .into(),
                    ));
                }
                let ti = *type_index as usize;
                let &(table_slots, base_slot) =
                    ctx.tables.get(*table_index as usize).ok_or_else(|| {
                        SelectError(format!(
                            "call_indirect on table {table_index}, which has no \
                             compile-time size/base in the emitted funcref region \
                             — loud-declining (#851)"
                        ))
                    })?;
                let expected = ctx.type_class_ids.get(ti).copied().unwrap_or(0);
                if expected == 0 {
                    return Err(SelectError(format!(
                        "call_indirect type {ti} has no structural class id — the \
                         §4.4.8 signature check cannot be encoded; loud-declining \
                         (#851)"
                    )));
                }
                let argc = *ctx.type_arg_counts.get(ti).ok_or_else(|| {
                    SelectError(format!("call_indirect type {ti}: unknown arg count"))
                })?;
                if argc > 8 {
                    return Err(SelectError(format!(
                        "call_indirect type {ti}: {argc} args — at most 8 register \
                         args are supported; loud-declining (#851)"
                    )));
                }
                let rc = *ctx.type_result_counts.get(ti).ok_or_else(|| {
                    SelectError(format!("call_indirect type {ti}: unknown result count"))
                })?;
                if rc > 1 {
                    return Err(SelectError(format!(
                        "call_indirect type {ti}: {rc} results — multi-result calls \
                         are not supported for aarch64; loud-declining (#851)"
                    )));
                }
                // AAPCS64 returns floats in v0/d0, not x0 — same decline as a
                // direct `call` (pushing x0 would read a stale GP register).
                if rc == 1 && ctx.type_ret_float.get(ti).copied().unwrap_or(false) {
                    return Err(SelectError(format!(
                        "call_indirect type {ti}: float result (returned in v0/d0, \
                         not x0) — not yet supported for aarch64; loud-declining \
                         (#851)"
                    )));
                }
                // The table index is on TOP of the stack, above the arguments.
                let idx = pop_gp(&mut stack, "call_indirect")?;
                if stack.len() != argc as usize {
                    return Err(SelectError(format!(
                        "call_indirect type {ti}: value stack holds {} entries \
                         below the index but needs exactly {argc} (the call \
                         clobbers caller-saved temps below the args); \
                         loud-declining (#851)",
                        stack.len()
                    )));
                }
                for (arg_reg, v) in stack.iter().enumerate() {
                    if v.file != File::Gp {
                        return Err(SelectError(format!(
                            "call_indirect type {ti}: argument {arg_reg} is a \
                             float — FP call args are not supported for aarch64; \
                             loud-declining (#851)"
                        )));
                    }
                }
                // (1) OOB guard. `table_slots` and the class ids were range-
                //     checked against the 12-bit immediate by substrate::plan.
                words.push(enc::cmp_imm(idx, table_slots));
                words.push(enc::bcond(Cond::Lo, 2)); // in range: hop the brk
                words.push(enc::brk(0));
                // (2) Slot address into IP0 (outside the temp pool and the arg
                //     registers, so nothing live can alias it).
                emit_sym_addr(&mut words, &mut sym_relocs, IP0, FUNC_TABLE_SYMBOL);
                words.push(enc::add_ext_uxtw_sh(IP0, IP0, idx, 3));
                let base_bytes = base_slot * crate::substrate::TABLE_SLOT_BYTES;
                if base_bytes > 0 {
                    if base_bytes < 4096 {
                        words.push(enc::add_imm64(IP0, IP0, base_bytes));
                    } else {
                        // Past the imm12 range (a later table in a multi-table
                        // module): materialize the byte offset in IP1 first.
                        for w in enc::mov_imm32(IP1, base_bytes) {
                            words.push(w);
                        }
                        words.push(enc::add64(IP0, IP0, IP1));
                    }
                }
                // (3) Type check — which is the null check too (a null slot
                //     carries class id 0, and `expected` is >= 1).
                words.push(enc::ldr_w(IP1, IP0, 0));
                words.push(enc::cmp_imm(IP1, expected));
                words.push(enc::bcond(Cond::Eq, 2)); // matching type: hop the brk
                words.push(enc::brk(0));
                // (4) Marshal args. Sources are temps (x9..x15), destinations
                //     x0..x7 — disjoint, so the moves need no shuffle, and IP0
                //     (holding the verified slot) is untouched.
                for (arg_reg, v) in stack.iter().enumerate() {
                    if v.reg != arg_reg as u8 {
                        words.push(enc::mov_reg64(arg_reg as u8, v.reg));
                    }
                }
                stack.clear();
                // (5) Branch into the slot's trampoline (slot+4), which tail-
                //     branches to the callee; `blr` sets x30 so the callee
                //     returns straight back here.
                words.push(enc::add_imm64(IP0, IP0, 4));
                words.push(enc::blr(IP0));
                if rc == 1 {
                    let dst = alloc_temp(&stack)?;
                    words.push(enc::mov_reg64(dst, 0));
                    stack.push(Val::gp(dst));
                }
            }
            other => {
                return Err(SelectError(format!(
                    "unsupported wasm op for aarch64 subset: {other:?}"
                )));
            }
        }
    }

    // A body without a trailing `End` still needs an epilogue.
    if !matches!(ops.last(), Some(WasmOp::End)) {
        epilogue(&mut words, stack.last().copied(), frame_size, is_non_leaf);
    }
    Ok((words, call_sites, sym_relocs))
}

/// Emit the function epilogue: move the top-of-stack result into the ABI return
/// register (`x0` for a GP result, `d0` for a float result), restore the stack
/// pointer past any non-param-local frame, and `ret`. A GP result already in
/// `x0` / an FP result already in `v0` skips the move. The 64-bit `mov x0, xN` is
/// correct for i32 results too (w-form producers zero the upper half); the `fmov
/// d0, dN` likewise carries an f32's low 32 bits intact.
///
/// `frame_size` is the byte size of the non-param-local frame (0 when the
/// function has no non-param locals — then no `add sp` is emitted and the output
/// is byte-identical to the pre-#851 epilogue). The result move is done BEFORE
/// the `add sp` (the result lives in a caller-saved temp, unaffected by SP), so
/// the sequence is: funnel result → restore SP → ret.
/// #851 lane L3 — emit `adrp xd, sym` + `add xd, xd, :lo12:sym`, recording the
/// two relocations, so `xd` ends up holding `sym`'s ABSOLUTE address.
///
/// This pair is how the aarch64 backend reaches a region it EMITTED (the
/// globals `.data` image, the funcref table) with NO ambient base register —
/// see [`crate::substrate`] for why that matters (it adds no precondition
/// beside `x28`, and there is no base register to collide with the way #275/
/// #717 collided on ARM).
fn emit_sym_addr(words: &mut Vec<u32>, relocs: &mut Vec<CodeRelocation>, rd: Reg, symbol: &str) {
    let off = (words.len() * 4) as u32;
    relocs.push(CodeRelocation {
        offset: off,
        symbol: symbol.to_string(),
        kind: RelocKind::AArch64AdrPrelPgHi21,
    });
    words.push(enc::adrp(rd, 0));
    relocs.push(CodeRelocation {
        offset: off + 4,
        symbol: symbol.to_string(),
        kind: RelocKind::AArch64AddAbsLo12Nc,
    });
    words.push(enc::add_imm64(rd, rd, 0));
}

/// #851 lane L3 — the AAPCS64 intra-procedure-call scratch registers. `x16`
/// carries the `call_indirect` slot/target address and `x17` the loaded class
/// id. Both are chosen deliberately OUTSIDE the value-stack temp pool
/// (`x9..x15`) and the argument registers (`x0..x7`), so the dispatch's guards
/// can run after the index is popped and before/after argument marshalling
/// without ever aliasing a live value. They are caller-saved and dead
/// immediately after the `blr`.
const IP0: Reg = 16;
const IP1: Reg = 17;

/// Guard an `imm26` (unconditional `b`) displacement (words) against the A64
/// field width (signed 26-bit → ±2^25 words = ±128 MB). Over-range would wrap
/// silently in the encoder's mask, so we LOUD-DECLINE instead (unreachable for
/// any realistic function; "No silent miscompile" is the hard rule).
fn check_imm26(off: i32) -> Result<i32, SelectError> {
    if !(-(1 << 25)..(1 << 25)).contains(&off) {
        return Err(SelectError(format!(
            "branch displacement {off} words exceeds A64 b imm26 range \
             (±2^25) — loud-declining rather than wrap silently"
        )));
    }
    Ok(off)
}

/// Guard an `imm19` (`cbz`/`cbnz`/`b.cond`) displacement (signed 19-bit →
/// ±2^18 words = ±1 MB). Same silent-wrap hazard as [`check_imm26`].
fn check_imm19(off: i32) -> Result<i32, SelectError> {
    if !(-(1 << 18)..(1 << 18)).contains(&off) {
        return Err(SelectError(format!(
            "conditional-branch displacement {off} words exceeds A64 imm19 \
             range (±2^18) — loud-declining rather than wrap silently"
        )));
    }
    Ok(off)
}

/// Re-encode a placeholder FORWARD branch at `words[pos]` to land at `target`
/// (a word index in `words`), preserving its kind. The FOUR kinds we emit as
/// forward placeholders are `b` (0x14…, imm26), `cbnz` (0x35…, imm19+Rt), `cbz`
/// (0x34…, imm19+Rt), and — since VCR-A64-CF-001's `br_table` chain — `b.<cond>`
/// (0x54…, imm19 + a 4-bit condition); the opcode's high bits discriminate them
/// so the Rt field, the condition field and the op class survive the patch.
/// Centralizing this prevents a `cbz` (added in #851) from being mis-patched as
/// a `cbnz`. Over-range displacements LOUD-DECLINE (no silent field wrap).
///
/// The `b.<cond>` case rebuilds the word directly instead of round-tripping
/// through [`enc::bcond`]: that keeps whatever condition the emitter chose
/// without needing to invert the private `Cond` mapping back out of the word.
fn patch_branch(words: &mut [u32], pos: usize, target: usize) -> Result<(), SelectError> {
    let off = (target as i64 - pos as i64) as i32;
    let w = words[pos];
    words[pos] = match w & 0xFF00_0000 {
        0x1400_0000 => enc::b_uncond(check_imm26(off)?),
        0x3500_0000 => enc::cbnz((w & 0x1F) as u8, check_imm19(off)?),
        0x3400_0000 => enc::cbz((w & 0x1F) as u8, check_imm19(off)?),
        0x5400_0000 => 0x5400_0000 | (((check_imm19(off)? as u32) & 0x7FFFF) << 5) | (w & 0xF),
        _ => unreachable!("patch_branch: not a placeholder branch: {w:#010x}"),
    };
    Ok(())
}

fn epilogue(words: &mut Vec<u32>, top: Option<Val>, frame_size: u32, is_non_leaf: bool) {
    match top {
        Some(Val {
            reg,
            file: File::Gp,
        }) if reg != 0 => {
            words.push(enc::mov_reg64(0, reg));
        }
        Some(Val {
            reg,
            file: File::Fp,
        }) if reg != 0 => {
            words.push(enc::fmov_d(0, reg));
        }
        _ => {}
    }
    // Unwind in reverse of the prologue: raise SP past the locals frame, then
    // (#851 non-leaf) restore FP/LR before `ret` — `ret` returns to x30.
    if frame_size > 0 {
        words.push(enc::add_imm64(enc::SP, enc::SP, frame_size));
    }
    if is_non_leaf {
        words.push(enc::ldp_fp_lr_post16());
    }
    words.push(enc::ret());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    // Helper: no-import module, callee `func` has `argc` args and 1 result.
    fn sel_calls(
        ops: &[WasmOp],
        num_params: u32,
        num_imports: u32,
        arg_counts: &[u32],
        result_counts: &[u32],
    ) -> Result<(Vec<u32>, Vec<CallSite>), SelectError> {
        select_typed_cf_calls(
            ops,
            num_params,
            &[],
            &[],
            &[],
            num_imports,
            arg_counts,
            result_counts,
            &[],
            MemBounds::Unchecked,
            &ModuleCtx::default(),
        )
        .map(|(w, s, _)| (w, s))
    }

    #[test]
    fn direct_call_no_args_one_result() {
        // (func (export "run") (result i32) call 0)  — func 0 returns i32, 0 args.
        let ops = vec![WasmOp::Call(0), WasmOp::End];
        let (w, sites) = sel_calls(&ops, 0, 0, &[0], &[1]).unwrap();
        // Non-leaf prologue (stp) ; bl #0 ; mov temp,x0 ; mov x0,temp ; ldp ; ret.
        assert_eq!(w[0], enc::stp_fp_lr_pre16());
        // The bl is the reloc site.
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].callee, 0);
        assert_eq!(w[sites[0].offset as usize / 4], enc::bl(0));
        // Last two words are the LR restore + ret.
        assert_eq!(w[w.len() - 2], enc::ldp_fp_lr_post16());
        assert_eq!(w[w.len() - 1], enc::ret());
    }

    #[test]
    fn direct_call_two_const_args_marshalled_to_x0_x1() {
        // i32.const 20 ; i32.const 22 ; call 0   — func 0: (param i32 i32)->i32.
        let ops = vec![
            WasmOp::I32Const(20),
            WasmOp::I32Const(22),
            WasmOp::Call(0),
            WasmOp::End,
        ];
        let (w, sites) = sel_calls(&ops, 0, 0, &[2], &[1]).unwrap();
        // The two consts land in x9/x10; the call marshals x9->x0, x10->x1.
        assert!(w.contains(&enc::mov_reg64(0, 9)));
        assert!(w.contains(&enc::mov_reg64(1, 10)));
        assert_eq!(sites.len(), 1);
        // bl is right after the two arg moves.
        let bl_word = w[sites[0].offset as usize / 4];
        assert_eq!(bl_word, enc::bl(0));
    }

    #[test]
    fn leaf_function_is_byte_identical_without_call() {
        // A call-free body must not gain the non-leaf LR frame.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let (w, sites) = sel_calls(&ops, 2, 0, &[], &[]).unwrap();
        assert!(sites.is_empty());
        assert_eq!(w, vec![enc::add(9, 0, 1), enc::mov_reg64(0, 9), enc::ret()]);
    }

    /// #851 lane L3 — the exact `call_indirect` guard sequence.
    ///
    /// The execution differential covers BEHAVIOUR, but it cannot distinguish
    /// the UNSIGNED bounds compare (`b.lo`) from a signed one (`b.lt`): under
    /// emulation a negative index passes a signed guard and then faults on the
    /// unmapped scaled address, so it traps either way. On real silicon that
    /// address can be MAPPED, and the dispatch would branch into it. The
    /// condition is therefore pinned here, where it is decidable.
    #[test]
    fn call_indirect_guard_sequence_uses_an_unsigned_bounds_compare() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::CallIndirect {
                type_index: 0,
                table_index: 0,
            },
            WasmOp::End,
        ];
        let ctx = ModuleCtx {
            substrate_emitted: true,
            global_is64: vec![],
            tables: vec![(4, 0)],
            type_class_ids: vec![3],
            type_arg_counts: vec![0],
            type_result_counts: vec![0],
            type_ret_float: vec![false],
        };
        let (w, _sites, relocs) = select_typed_cf_calls(
            &ops,
            1,
            &[],
            &[],
            &[],
            0,
            &[],
            &[],
            &[],
            MemBounds::Unchecked,
            &ctx,
        )
        .unwrap();
        // Prologue: stp x29,x30 ; sub sp,#16 ; str x0,[sp] (param homing) ;
        // ldr x9,[sp] (local.get 0).
        assert_eq!(w[0], enc::stp_fp_lr_pre16());
        assert_eq!(w[2], enc::str_x_imm(0, enc::SP, 0));
        assert_eq!(w[3], enc::ldr_x_imm(9, enc::SP, 0));
        // Guard 1 — OOB. UNSIGNED (`Lo`), so 0xFFFFFFFF is ABOVE 4, not below.
        assert_eq!(w[4], enc::cmp_imm(9, 4));
        assert_eq!(
            w[5],
            enc::bcond(Cond::Lo, 2),
            "the table bounds compare must be UNSIGNED (b.lo): a signed b.lt \
             lets a negative index through, and uxtw then scales it into an \
             address that can be mapped on real silicon"
        );
        assert_eq!(w[6], enc::brk(0));
        // Table address: adrp+add (relocated), then + idx*8.
        assert_eq!(w[7], enc::adrp(IP0, 0));
        assert_eq!(w[8], enc::add_imm64(IP0, IP0, 0));
        assert_eq!(w[9], enc::add_ext_uxtw_sh(IP0, IP0, 9, 3));
        // Guard 2 — the structural class id (which is also the null check).
        assert_eq!(w[10], enc::ldr_w(IP1, IP0, 0));
        assert_eq!(w[11], enc::cmp_imm(IP1, 3));
        assert_eq!(w[12], enc::bcond(Cond::Eq, 2));
        assert_eq!(w[13], enc::brk(0));
        // Branch into the slot's trampoline at slot+4.
        assert_eq!(w[14], enc::add_imm64(IP0, IP0, 4));
        assert_eq!(w[15], enc::blr(IP0));
        // The adrp/add pair must carry its two relocations against the table.
        assert_eq!(relocs.len(), 2);
        assert!(relocs.iter().all(|r| r.symbol == FUNC_TABLE_SYMBOL));
        assert_eq!(relocs[0].offset, 7 * 4);
        assert!(matches!(relocs[0].kind, RelocKind::AArch64AdrPrelPgHi21));
        assert_eq!(relocs[1].offset, 8 * 4);
        assert!(matches!(relocs[1].kind, RelocKind::AArch64AddAbsLo12Nc));
    }

    /// Both module-level features are FAIL-SAFE: with the default context (no
    /// substrate emitted) they LOUD-DECLINE rather than address a region the
    /// driver never placed.
    #[test]
    fn globals_and_call_indirect_decline_without_an_emitted_substrate() {
        for ops in [
            vec![WasmOp::GlobalGet(0), WasmOp::End],
            vec![WasmOp::I32Const(1), WasmOp::GlobalSet(0), WasmOp::End],
            vec![
                WasmOp::I32Const(0),
                WasmOp::CallIndirect {
                    type_index: 0,
                    table_index: 0,
                },
                WasmOp::End,
            ],
        ] {
            let r = sel_calls(&ops, 0, 0, &[0], &[0]);
            assert!(
                r.is_err(),
                "must decline without an emitted substrate: {ops:?}"
            );
        }
    }

    /// The globals lowering addresses `__synth_globals + k*8` with a SIZE-SCALED
    /// immediate: `k*2` for the `w` view, `k` for the `x` view. Getting the
    /// scaling wrong reads a neighbouring slot.
    #[test]
    fn global_get_scales_the_slot_offset_per_access_width() {
        let ctx = ModuleCtx {
            substrate_emitted: true,
            global_is64: vec![false, true, false],
            ..ModuleCtx::default()
        };
        let sel = |ops: Vec<WasmOp>| {
            select_typed_cf_calls(
                &ops,
                0,
                &[],
                &[],
                &[],
                0,
                &[],
                &[],
                &[],
                MemBounds::Unchecked,
                &ctx,
            )
            .unwrap()
        };
        // global 2 is i32 → byte offset 16 → `ldr w` scaled immediate 4.
        let (w, _, _) = sel(vec![WasmOp::GlobalGet(2), WasmOp::End]);
        assert_eq!(w[0], enc::adrp(9, 0));
        assert_eq!(w[1], enc::add_imm64(9, 9, 0));
        assert_eq!(w[2], enc::ldr_w(9, 9, 4));
        // global 1 is i64 → byte offset 8 → `ldr x` scaled immediate 1.
        let (w, _, _) = sel(vec![WasmOp::GlobalGet(1), WasmOp::End]);
        assert_eq!(w[2], enc::ldr_x(9, 9, 1));
        // A store mirrors it, and the base temp must DIFFER from the value.
        let (w, _, _) = sel(vec![WasmOp::I32Const(7), WasmOp::GlobalSet(2), WasmOp::End]);
        let store = w[w.len() - 2];
        assert_eq!(store, enc::str_w(9, 10, 4));
    }

    /// A global index past the emitted region LOUD-DECLINES.
    #[test]
    fn global_index_past_the_region_declines() {
        let ctx = ModuleCtx {
            substrate_emitted: true,
            global_is64: vec![false],
            ..ModuleCtx::default()
        };
        let ops = vec![WasmOp::GlobalGet(5), WasmOp::End];
        let r = select_typed_cf_calls(
            &ops,
            0,
            &[],
            &[],
            &[],
            0,
            &[],
            &[],
            &[],
            MemBounds::Unchecked,
            &ctx,
        );
        assert!(r.is_err());
    }

    #[test]
    fn call_to_import_loud_declines() {
        // func 0 is an import (num_imports = 1); calling it declines.
        let ops = vec![WasmOp::Call(0), WasmOp::End];
        assert!(sel_calls(&ops, 0, 1, &[0], &[0]).is_err());
    }

    /// #851 lane L3 — a non-leaf function that reads a param now HOMES it into
    /// a stack slot at the prologue instead of loud-declining. The homing store
    /// is what makes a post-call read sound (x0..x7 are caller-saved), and it is
    /// the prerequisite for a useful `call_indirect` (the table index almost
    /// always comes from a parameter).
    #[test]
    fn non_leaf_homes_its_params_to_stack_slots() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::Call(1), WasmOp::End];
        // func 1 takes 1 arg (the local.get 0 value).
        let (w, _) = sel_calls(&ops, 1, 0, &[0, 1], &[0, 1]).unwrap();
        // stp x29,x30,[sp,#-16]! ; sub sp,sp,#16 ; str x0,[sp] ; ldr x9,[sp] ...
        assert_eq!(w[0], enc::stp_fp_lr_pre16());
        assert_eq!(w[1], enc::sub_imm64(enc::SP, enc::SP, 16));
        assert_eq!(
            w[2],
            enc::str_x_imm(0, enc::SP, 0),
            "the incoming param x0 must be STORED to its slot at the prologue"
        );
        // The `local.get 0` then LOADS the slot into a temp (a copy), so the
        // value survives the call that follows.
        assert_eq!(w[3], enc::ldr_x_imm(9, enc::SP, 0));
    }

    /// A LEAF function is untouched by homing: its params stay register-
    /// resident, so writing one still loud-declines (that gap is a separate
    /// increment, and its parity-gate entry stays valid).
    #[test]
    fn leaf_param_write_still_loud_declines() {
        let ops = vec![WasmOp::I32Const(42), WasmOp::LocalSet(0), WasmOp::End];
        assert!(sel_calls(&ops, 1, 0, &[0], &[0]).is_err());
        let ops = vec![WasmOp::I32Const(42), WasmOp::LocalTee(0), WasmOp::End];
        assert!(sel_calls(&ops, 1, 0, &[0], &[0]).is_err());
    }

    /// A FLOAT param in a non-leaf function keeps the loud decline: homing a
    /// v-register needs an FP store the encoder does not have, and homing the
    /// wrong register file would be a silent miscompile.
    #[test]
    fn non_leaf_float_param_still_loud_declines() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::Call(1), WasmOp::End];
        let r = select_typed_cf_calls(
            &ops,
            1,
            &[true], // param 0 is f32 → lives in s0
            &[],
            &[],
            0,
            &[0, 1],
            &[0, 1],
            &[false, false],
            MemBounds::Unchecked,
            &ModuleCtx::default(),
        );
        assert!(r.is_err(), "float param homing must loud-decline");
    }

    #[test]
    fn call_with_extra_stack_below_args_loud_declines() {
        // A live value beneath the args does not survive the call → decline.
        // stack: [const_a, const_b] but callee takes only 1 arg → height 2 != 1.
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::Call(0),
            WasmOp::End,
        ];
        assert!(sel_calls(&ops, 0, 0, &[1], &[1]).is_err());
    }

    #[test]
    fn call_with_float_result_loud_declines() {
        // A callee that returns f32/f64 (result in v0/d0, not x0) must decline —
        // pushing x0 would be a silent miscompile.
        let ops = vec![WasmOp::Call(0), WasmOp::End];
        let r = select_typed_cf_calls(
            &ops,
            0,
            &[],
            &[],
            &[],
            0,
            &[0],    // 0 args
            &[1],    // 1 result
            &[true], // ...which is a float
            MemBounds::Unchecked,
            &ModuleCtx::default(),
        );
        assert!(r.is_err(), "float-returning callee must loud-decline");
    }

    // --- #865: software bounds check ---

    fn sel_mem(ops: &[WasmOp], num_params: u32, bounds: MemBounds) -> Vec<u32> {
        let (w, _, _) = select_typed_cf_calls(
            ops,
            num_params,
            &[],
            &[],
            &[],
            0,
            &[],
            &[],
            &[],
            bounds,
            &ModuleCtx::default(),
        )
        .unwrap();
        w
    }

    #[test]
    fn software_bounds_guards_i32_load_exact_sequence() {
        // (memory 1) i32.load: K = 65536 - 0 - 4 = 65532; the check must
        // precede the dereference. Pinned against `llvm-objdump` ground truth:
        //   mov w9,#0xfffc; cmp w0,w9; b.ls +2; brk #0;
        //   add x9,x28,w0,uxtw; ldr w9,[x9]; mov x0,x9; ret
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        let w = sel_mem(&ops, 1, MemBounds::Software { limit_bytes: 65536 });
        assert_eq!(
            w,
            vec![
                0x529F_FF89, // mov w9, #65532
                enc::cmp(0, 9),
                enc::bcond(Cond::Ls, 2),
                enc::brk(0),
                enc::add_ext_uxtw(9, LINMEM_BASE, 0),
                0xB940_0129, // ldr w9, [x9]
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn software_bounds_accounts_offset_and_width() {
        // i32.load offset=65532 with limit 65536: K = 65536 - 65532 - 4 = 0 —
        // only addr 0 is in bounds (bytes 65532..65535). The compare constant
        // must be 0, not 65532 (offset+width accounting, the at-limit edge).
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 65532,
                align: 2,
            },
            WasmOp::End,
        ];
        let w = sel_mem(&ops, 1, MemBounds::Software { limit_bytes: 65536 });
        assert_eq!(w[0], enc::mov_imm32(9, 0)[0], "compare constant must be 0");
        assert!(w.contains(&enc::brk(0)));
    }

    #[test]
    fn software_bounds_offset_past_limit_always_traps() {
        // offset + size > limit: NO i32 address is in bounds — an
        // unconditional brk precedes the (dead) access.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 70000,
                align: 2,
            },
            WasmOp::End,
        ];
        let w = sel_mem(&ops, 1, MemBounds::Software { limit_bytes: 65536 });
        assert_eq!(w[0], enc::brk(0));
    }

    // --- v0.54 L2 (#851): f32/f64 linear-memory access ---

    fn sel_mem_typed(
        ops: &[WasmOp],
        num_params: u32,
        f32s: &[bool],
        f64s: &[bool],
        bounds: MemBounds,
    ) -> Vec<u32> {
        // v0.54 fan-in: lane L3 gave `select_typed_cf_calls` an 11th parameter
        // (`&ModuleCtx`, for globals + the funcref table) and a third return
        // (relocs). This L2 helper needs neither — FP-memory selection carries no
        // module context — so it passes the default and drops both extra values.
        let (w, _sites, _relocs) = select_typed_cf_calls(
            ops,
            num_params,
            f32s,
            f64s,
            &[],
            0,
            &[],
            &[],
            &[],
            bounds,
            &ModuleCtx::default(),
        )
        .unwrap();
        w
    }

    #[test]
    fn f32_load_is_bounds_checked_then_ldr_s() {
        // (param i32) f32.load — the FP load must go through the SAME #865
        // check as i32.load: K = 65536 - 0 - 4 = 65532, compare BEFORE the
        // dereference, `brk` on OOB. Then `ldr s16, [x9]` (FP destination, so
        // the GP `ea` temp is not reused as the data register).
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::F32Load {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        let w = sel_mem_typed(
            &ops,
            1,
            &[],
            &[],
            MemBounds::Software { limit_bytes: 65536 },
        );
        assert_eq!(
            w,
            vec![
                0x529F_FF89, // mov w9, #65532
                enc::cmp(0, 9),
                enc::bcond(Cond::Ls, 2),
                enc::brk(0),
                enc::add_ext_uxtw(9, LINMEM_BASE, 0),
                enc::ldr_s(FTEMPS[0], 9, 0),
                enc::fmov_d(0, FTEMPS[0]),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn f64_store_is_bounds_checked_with_dword_width() {
        // f64.store must account for the 8-byte access width in the bound:
        // K = 65536 - 0 - 8 = 65528 (NOT 65532) — an 8-byte store at 65532
        // would run 4 bytes past the limit.
        let ops = vec![
            WasmOp::LocalGet(0), // i32 address
            WasmOp::LocalGet(1), // f64 value
            WasmOp::F64Store {
                offset: 0,
                align: 3,
            },
            WasmOp::End,
        ];
        let w = sel_mem_typed(
            &ops,
            2,
            &[],
            &[false, true],
            MemBounds::Software { limit_bytes: 65536 },
        );
        assert_eq!(w[0], enc::mov_imm32(9, 65528)[0], "K must be limit - 8");
        assert!(w.contains(&enc::brk(0)), "OOB must trap");
        assert!(
            w.contains(&enc::str_d(0, 9, 0)),
            "must store the d view of the value register; got {w:#010X?}"
        );
    }

    #[test]
    fn fp_mem_offset_folds_into_the_scaled_immediate() {
        // A size-aligned offset within imm12 range folds into the load: for
        // `ldr s` the encoded imm12 is offset/4, for `ldr d` offset/8.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::F32Load {
                offset: 16,
                align: 2,
            },
            WasmOp::End,
        ];
        let w = sel_mem_typed(&ops, 1, &[], &[], MemBounds::Unchecked);
        assert_eq!(
            w,
            vec![
                enc::add_ext_uxtw(9, LINMEM_BASE, 0),
                enc::ldr_s(FTEMPS[0], 9, 4), // imm12 = 16/4
                enc::fmov_d(0, FTEMPS[0]),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn fp_store_rejects_a_gp_value_operand() {
        // Type confusion guard: an i32 on the stack fed to f32.store must ERROR
        // rather than store the wrong register file.
        let ops = vec![
            WasmOp::I32Const(0),
            WasmOp::I32Const(42),
            WasmOp::F32Store {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        assert!(select_typed(&ops, 0, &[], &[]).is_err());
    }

    #[test]
    fn unchecked_mode_emits_no_trap_check() {
        // The explicit opt-out stays byte-identical to the pre-#865 lowering.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Load {
                offset: 0,
                align: 2,
            },
            WasmOp::End,
        ];
        let w = sel_mem(&ops, 1, MemBounds::Unchecked);
        assert_eq!(
            w,
            vec![
                enc::add_ext_uxtw(9, LINMEM_BASE, 0),
                0xB940_0129, // ldr w9, [x9]
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
        assert!(!w.contains(&enc::brk(0)));
    }

    #[test]
    fn void_result_call_pushes_nothing() {
        // call 0 where func 0 returns void: no value pushed, epilogue returns x0
        // as-is (whatever the ABI leaves) — the important part is it lowers.
        let ops = vec![WasmOp::Call(0), WasmOp::End];
        let (w, sites) = sel_calls(&ops, 0, 0, &[0], &[0]).unwrap();
        assert_eq!(sites.len(), 1);
        // No `mov temp, x0` after the bl (nothing pushed): the word after bl is
        // the ldp restore.
        let bl_i = sites[0].offset as usize / 4;
        assert_eq!(w[bl_i + 1], enc::ldp_fp_lr_post16());
    }

    #[test]
    fn add_two_params() {
        // (param i32 i32) (result i32) local.get 0; local.get 1; i32.add
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        // add w9,w0,w1 ; mov x0,x9 ; ret
        assert_eq!(w, vec![enc::add(9, 0, 1), enc::mov_reg64(0, 9), enc::ret()]);
        assert_eq!(bytes(&w).len(), 12);
    }

    #[test]
    fn const_add_uses_movz() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(5),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 1).unwrap();
        assert_eq!(
            w,
            vec![
                enc::movz(9, 5),
                enc::add(9, 0, 9),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn result_already_in_w0_skips_mov() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(w, vec![enc::ret()]);
    }

    #[test]
    fn i64_add_uses_x_form() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I64Add,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(
            w,
            vec![enc::add64(9, 0, 1), enc::mov_reg64(0, 9), enc::ret()]
        );
    }

    #[test]
    fn i32_shl_uses_lslv() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Shl,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(
            w,
            vec![enc::lslv(9, 0, 1), enc::mov_reg64(0, 9), enc::ret()]
        );
    }

    #[test]
    fn i32_lt_s_uses_cmp_cset() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32LtS,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(
            w,
            vec![
                enc::cmp(0, 1),
                enc::cset(9, Cond::Lt),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn i32_eqz_compares_with_zero() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32Eqz, WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(
            w,
            vec![
                enc::cmp(0, enc::WZR),
                enc::cset(9, Cond::Eq),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn i32_ctz_is_rbit_then_clz() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32Ctz, WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(
            w,
            vec![
                enc::rbit(9, 0),
                enc::clz(9, 9),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn i32_rotl_is_neg_then_rorv() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Rotl,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        // #776: -k is computed in k's own register (1), NOT in dst (9) — so a
        // computed `n` reused as dst is never clobbered before rorv reads it.
        assert_eq!(
            w,
            vec![
                enc::neg(1, 1),
                enc::rorv(9, 0, 1),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    // #851 — div/rem now LOWER (SDIV/UDIV + MSUB) with WASM trap guards.
    #[test]
    fn division_and_remainder_lower_with_guards() {
        for op in [
            WasmOp::I32DivS,
            WasmOp::I32DivU,
            WasmOp::I32RemS,
            WasmOp::I32RemU,
            WasmOp::I64DivS,
            WasmOp::I64DivU,
            WasmOp::I64RemS,
            WasmOp::I64RemU,
        ] {
            let ops = vec![
                WasmOp::LocalGet(0),
                WasmOp::LocalGet(1),
                op.clone(),
                WasmOp::End,
            ];
            assert!(select(&ops, 2).is_ok(), "div/rem must lower: {op:?}");
        }
    }

    #[test]
    fn div_u_emits_divisor_zero_guard_only() {
        // i32.div_u: cbnz w1,+2 ; brk ; udiv w9,w0,w1 ; mov x0,x9 ; ret.
        // Exactly ONE brk (÷0), no overflow guard for the unsigned form.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32DivU,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(
            w,
            vec![
                enc::cbnz(1, 2),
                enc::brk(0),
                enc::udiv(9, 0, 1),
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn div_s_emits_zero_and_overflow_guards() {
        // i32.div_s: ÷0 guard + INT_MIN/-1 overflow guard, then sdiv.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32DivS,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        // Temps: q=9 (quotient/result), s0=10 (INT_MIN), s1=11 (-1).
        let mut expect = vec![enc::cbnz(1, 2), enc::brk(0)];
        expect.extend(enc::mov_imm32(10, 0x8000_0000)); // INT_MIN scratch
        expect.extend(enc::mov_imm32(11, 0xFFFF_FFFF)); // -1 scratch
        expect.push(enc::cmp(0, 10)); // dividend == INT_MIN?
        expect.push(enc::bcond(Cond::Ne, 4));
        expect.push(enc::cmp(1, 11)); // divisor == -1?
        expect.push(enc::bcond(Cond::Ne, 2));
        expect.push(enc::brk(0));
        expect.push(enc::sdiv(9, 0, 1));
        expect.push(enc::mov_reg64(0, 9));
        expect.push(enc::ret());
        assert_eq!(w, expect);
    }

    #[test]
    fn rem_s_has_zero_guard_but_no_overflow_guard() {
        // rem_s traps ONLY on ÷0 (rem_s(INT_MIN,-1) == 0). So exactly one brk,
        // and the arithmetic is sdiv + msub.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32RemS,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(
            w,
            vec![
                enc::cbnz(1, 2),
                enc::brk(0),
                enc::sdiv(9, 0, 1),
                enc::msub(9, 9, 1, 0),
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
        // Exactly one brk — no overflow guard.
        assert_eq!(w.iter().filter(|&&x| x == enc::brk(0)).count(), 1);
    }

    #[test]
    fn i64_div_zero_guard_tests_full_width() {
        // The i64 ÷0 guard MUST use the x-form cbnz (all 64 bits).
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I64DivU,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(w[0], enc::cbnz64(1, 2), "i64 ÷0 guard must be 64-bit cbnz");
        assert_eq!(w[1], enc::brk(0));
    }

    #[test]
    fn popcnt_lowers_via_simd_cnt_addv() {
        // i32.popcnt: fmov s16,w0 ; cnt v16.8b ; addv b16 ; fmov w9,s16.
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32Popcnt, WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(
            w,
            vec![
                enc::fmov_s_from_w(16, 0),
                enc::cnt_8b(16, 16),
                enc::addv_8b(16, 16),
                enc::fmov_w_from_s(9, 16),
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn i64_popcnt_uses_d_move() {
        // i64.popcnt fills all 8 bytes: fmov d16,x0.
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I64Popcnt, WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(w[0], enc::fmov_d_from_x(16, 0));
        assert_eq!(w[1], enc::cnt_8b(16, 16));
        assert_eq!(w[2], enc::addv_8b(16, 16));
    }

    #[test]
    fn f64_i64_reinterpret_round_trips_through_fmov() {
        // i64 param → f64.reinterpret → i64.reinterpret: fmov d16,x0; fmov x9,d16.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::F64ReinterpretI64,
            WasmOp::I64ReinterpretF64,
            WasmOp::End,
        ];
        let w = select(&ops, 1).unwrap();
        assert_eq!(
            w,
            vec![
                enc::fmov_d_from_x(16, 0),
                enc::fmov_x_from_d(9, 16),
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
    }

    // ---- milestone 3: scalar float ----

    #[test]
    fn f32_add_uses_v_registers_and_fmov_return() {
        // (param f32 f32) → params in s0, s1. f32.add → fadd v16, s0, s1;
        // fmov d0, d16; ret.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F32Add,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[true, true], &[]).unwrap();
        assert_eq!(
            w,
            vec![enc::fadd_s(16, 0, 1), enc::fmov_d(0, 16), enc::ret()]
        );
    }

    #[test]
    fn f64_mul_uses_d_forms() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F64Mul,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[], &[true, true]).unwrap();
        assert_eq!(
            w,
            vec![enc::fmul_d(16, 0, 1), enc::fmov_d(0, 16), enc::ret()]
        );
    }

    #[test]
    fn mixed_int_float_params_assign_independent_registers() {
        // (param i32 f32 i32): AAPCS64 → w0, s0, w1. `local.get 1` (the f32)
        // must resolve to s0, `local.get 2` (the 2nd i32) to w1.
        let ops = vec![
            WasmOp::LocalGet(1), // f32 → s0
            WasmOp::F32Neg,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 3, &[false, true, false], &[]).unwrap();
        // fneg v16, s0 ; fmov d0, d16 ; ret
        assert_eq!(w, vec![enc::fneg_s(16, 0), enc::fmov_d(0, 16), enc::ret()]);
    }

    #[test]
    fn f32_lt_uses_fcmp_and_mi_cond() {
        // f32.lt → fcmp s0,s1 ; cset w9, mi (NaN-correct) → GP result.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F32Lt,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[true, true], &[]).unwrap();
        assert_eq!(
            w,
            vec![
                enc::fcmp_s(0, 1),
                enc::cset(9, Cond::Mi),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn f32_const_materializes_via_gp_then_fmov() {
        // f32.const 1.0 = 0x3F800000 → movz/movk into a GP temp, fmov s16,w9.
        let ops = vec![WasmOp::F32Const(1.0), WasmOp::End];
        let w = select_typed(&ops, 0, &[], &[]).unwrap();
        let bits = 1.0f32.to_bits();
        let mut expect = enc::mov_imm32(9, bits);
        expect.push(enc::fmov_s_from_w(16, 9));
        expect.push(enc::fmov_d(0, 16));
        expect.push(enc::ret());
        assert_eq!(w, expect);
    }

    #[test]
    fn convert_i32_s_to_f32_pops_gp_pushes_fp() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::F32ConvertI32S, WasmOp::End];
        // param 0 is i32 → w0; scvtf s16, w0 ; fmov d0, d16 ; ret
        let w = select_typed(&ops, 1, &[], &[]).unwrap();
        assert_eq!(
            w,
            vec![enc::scvtf_s_from_w(16, 0), enc::fmov_d(0, 16), enc::ret()]
        );
    }

    #[test]
    fn reinterpret_i32_to_f32_and_back() {
        // i32 param → f32.reinterpret → i32.reinterpret round-trips through FMOV.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::F32ReinterpretI32,
            WasmOp::I32ReinterpretF32,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 1, &[], &[]).unwrap();
        assert_eq!(
            w,
            vec![
                enc::fmov_s_from_w(16, 0),
                enc::fmov_w_from_s(9, 16),
                enc::mov_reg64(0, 9),
                enc::ret()
            ]
        );
    }

    #[test]
    fn promote_demote_round_trip() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::F64PromoteF32,
            WasmOp::F32DemoteF64,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 1, &[true], &[]).unwrap();
        assert_eq!(
            w,
            vec![
                enc::fcvt_d_from_s(16, 0),
                enc::fcvt_s_from_d(16, 16),
                enc::fmov_d(0, 16),
                enc::ret()
            ]
        );
    }

    // ---- milestone 4: guarded trunc, min/max, copysign ----

    #[test]
    fn i32_trunc_f32_s_emits_domain_guard_then_fcvtzs() {
        // #709: the saturating FCVTZS must sit BEHIND the two-sided WASM
        // range guard (fcmp bound; ordered b.cond skips the brk; NaN falls
        // through every ordered condition into the trap).
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32TruncF32S, WasmOp::End];
        let w = select_typed(&ops, 1, &[true], &[]).unwrap();
        let mut expect = Vec::new();
        // hi bound: 2^31 (0x4F000000, exclusive, b.mi)
        expect.extend(enc::mov_imm32(9, 0x4F00_0000));
        expect.push(enc::fmov_s_from_w(16, 9));
        expect.push(enc::fcmp_s(0, 16));
        expect.push(enc::bcond(Cond::Mi, 2));
        expect.push(enc::brk(0));
        // lo bound: -2^31 (0xCF000000, INCLUSIVE, b.ge)
        expect.extend(enc::mov_imm32(9, 0xCF00_0000));
        expect.push(enc::fmov_s_from_w(16, 9));
        expect.push(enc::fcmp_s(0, 16));
        expect.push(enc::bcond(Cond::Ge, 2));
        expect.push(enc::brk(0));
        expect.push(enc::fcvtzs_w_from_s(9, 0));
        expect.push(enc::mov_reg64(0, 9));
        expect.push(enc::ret());
        assert_eq!(w, expect);
    }

    #[test]
    fn i32_trunc_f64_s_lower_bound_is_strict_minus_2pow31_minus_1() {
        // f64 CAN represent values in (-2^31-1, -2^31) (e.g. -2147483648.5)
        // which truncate IN-range — the lower bound must be the STRICT
        // -(2^31)-1 (0xC1E0_0000_0020_0000, b.gt), not an inclusive -2^31.
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32TruncF64S, WasmOp::End];
        let w = select_typed(&ops, 1, &[], &[true]).unwrap();
        let lo = enc::mov_imm64(9, 0xC1E0_0000_0020_0000);
        assert!(
            w.windows(lo.len()).any(|win| win == lo.as_slice()),
            "must materialize the strict -(2^31)-1 f64 bound; got {w:#010X?}"
        );
        assert!(w.contains(&enc::bcond(Cond::Gt, 2)));
        assert!(w.contains(&enc::fcvtzs_w_from_d(9, 0)));
        assert_eq!(w.iter().filter(|&&x| x == enc::brk(0)).count(), 2);
    }

    #[test]
    fn i32_trunc_f32_u_uses_strict_minus_one_lower_bound_and_fcvtzu() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32TruncF32U, WasmOp::End];
        let w = select_typed(&ops, 1, &[true], &[]).unwrap();
        // hi 2^32 = 0x4F800000; lo -1.0 = 0xBF800000 with STRICT b.gt.
        assert!(w.contains(&enc::movz(9, 0)), "movz low half of 0x4F800000");
        assert!(w.contains(&enc::movk(9, 0x4F80, 1)));
        assert!(w.contains(&enc::movk(9, 0xBF80, 1)));
        assert!(w.contains(&enc::bcond(Cond::Gt, 2)));
        assert!(w.contains(&enc::fcvtzu_w_from_s(9, 0)));
    }

    #[test]
    fn trunc_sat_782_i32_forms_are_one_bare_fcvtz() {
        // §4.3.2 trunc_sat is TOTAL — A64 FCVTZS/FCVTZU already saturate and
        // give 0 for NaN, so the lowering is ONE bare convert: no bound
        // materialization, no b.cond, and above all NO brk (a guard would
        // spuriously trap where WASM saturates).
        for (op, f32_src, cvt) in [
            (
                WasmOp::I32TruncSatF32S,
                true,
                enc::fcvtzs_w_from_s as fn(Reg, FReg) -> u32,
            ),
            (WasmOp::I32TruncSatF32U, true, enc::fcvtzu_w_from_s),
            (WasmOp::I32TruncSatF64S, false, enc::fcvtzs_w_from_d),
            (WasmOp::I32TruncSatF64U, false, enc::fcvtzu_w_from_d),
        ] {
            let ops = vec![WasmOp::LocalGet(0), op.clone(), WasmOp::End];
            let (f32s, f64s): (&[bool], &[bool]) = if f32_src {
                (&[true], &[])
            } else {
                (&[], &[true])
            };
            let w = select_typed(&ops, 1, f32s, f64s).unwrap();
            assert_eq!(
                w,
                vec![cvt(9, 0), enc::mov_reg64(0, 9), enc::ret()],
                "{op:?} must be one bare saturating convert"
            );
            assert!(
                !w.contains(&enc::brk(0)),
                "{op:?} is total — a brk guard would spuriously trap"
            );
        }
    }

    #[test]
    fn trunc_sat_782_i64_forms_use_x_destination_fcvtz() {
        // A64 is 64-bit native: the i64-target forms are the same
        // one-instruction shape with an x (sf=1) destination.
        for (op, f32_src, cvt) in [
            (
                WasmOp::I64TruncSatF32S,
                true,
                enc::fcvtzs_x_from_s as fn(Reg, FReg) -> u32,
            ),
            (WasmOp::I64TruncSatF32U, true, enc::fcvtzu_x_from_s),
            (WasmOp::I64TruncSatF64S, false, enc::fcvtzs_x_from_d),
            (WasmOp::I64TruncSatF64U, false, enc::fcvtzu_x_from_d),
        ] {
            let ops = vec![WasmOp::LocalGet(0), op.clone(), WasmOp::End];
            let (f32s, f64s): (&[bool], &[bool]) = if f32_src {
                (&[true], &[])
            } else {
                (&[], &[true])
            };
            let w = select_typed(&ops, 1, f32s, f64s).unwrap();
            assert_eq!(
                w,
                vec![cvt(9, 0), enc::mov_reg64(0, 9), enc::ret()],
                "{op:?} must be one bare x-destination saturating convert"
            );
        }
    }

    // --- v0.54 L2 (#851): rounding + i64-source converts ---

    #[test]
    fn rounding_ops_lower_to_the_mode_pinned_frint() {
        // Each WASM rounding op is ONE FRINT with the mode in the opcode.
        // FRINTN (ties-to-EVEN) is `nearest`; FRINTA (ties-away) is NOT a WASM
        // op and must never appear.
        for (op, f64_src, want) in [
            (
                WasmOp::F32Ceil,
                false,
                enc::frintp_s as fn(FReg, FReg) -> u32,
            ),
            (WasmOp::F32Floor, false, enc::frintm_s),
            (WasmOp::F32Trunc, false, enc::frintz_s),
            (WasmOp::F32Nearest, false, enc::frintn_s),
            (WasmOp::F64Ceil, true, enc::frintp_d),
            (WasmOp::F64Floor, true, enc::frintm_d),
            (WasmOp::F64Trunc, true, enc::frintz_d),
            (WasmOp::F64Nearest, true, enc::frintn_d),
        ] {
            let ops = vec![WasmOp::LocalGet(0), op.clone(), WasmOp::End];
            let (f32s, f64s): (&[bool], &[bool]) = if f64_src {
                (&[], &[true])
            } else {
                (&[true], &[])
            };
            let w = select_typed(&ops, 1, f32s, f64s).unwrap();
            assert_eq!(
                w,
                vec![want(FTEMPS[0], 0), enc::fmov_d(0, FTEMPS[0]), enc::ret()],
                "{op:?} must be one mode-pinned FRINT"
            );
            // TOTAL op: a guard would spuriously trap where WASM returns a value.
            assert!(!w.contains(&enc::brk(0)), "{op:?} never traps");
        }
    }

    #[test]
    fn i64_source_converts_use_the_x_form_scvtf_ucvtf() {
        for (op, want) in [
            (
                WasmOp::F32ConvertI64S,
                enc::scvtf_s_from_x as fn(FReg, Reg) -> u32,
            ),
            (WasmOp::F32ConvertI64U, enc::ucvtf_s_from_x),
            (WasmOp::F64ConvertI64S, enc::scvtf_d_from_x),
            (WasmOp::F64ConvertI64U, enc::ucvtf_d_from_x),
        ] {
            let ops = vec![WasmOp::LocalGet(0), op.clone(), WasmOp::End];
            let w = select_typed(&ops, 1, &[], &[]).unwrap();
            assert_eq!(
                w,
                vec![want(FTEMPS[0], 0), enc::fmov_d(0, FTEMPS[0]), enc::ret()],
                "{op:?} must be one x-source convert"
            );
        }
        // The x-form must NOT be confusable with the (already shipped) w-form:
        // a w-source convert of a value above 2^32 would read only the low half.
        assert_ne!(enc::scvtf_d_from_x(16, 0), enc::scvtf_d_from_w(16, 0));
    }

    #[test]
    fn f32_min_max_use_fmin_fmax() {
        // WASM min/max ≡ A64 FMIN/FMAX (IEEE 754-2019 minimum/maximum) — a
        // single instruction each; FMINNM/FMAXNM would be the WRONG (minNum)
        // NaN semantics.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F32Min,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[true, true], &[]).unwrap();
        assert_eq!(
            w,
            vec![enc::fmin_s(16, 0, 1), enc::fmov_d(0, 16), enc::ret()]
        );
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F64Max,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[], &[true, true]).unwrap();
        assert_eq!(
            w,
            vec![enc::fmax_d(16, 0, 1), enc::fmov_d(0, 16), enc::ret()]
        );
    }

    #[test]
    fn f32_copysign_is_bit_surgery_through_gp() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F32Copysign,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[true, true], &[]).unwrap();
        let mut expect = vec![
            enc::fmov_w_from_s(9, 0),  // z1 bits (magnitude)
            enc::fmov_w_from_s(10, 1), // z2 bits (sign)
        ];
        expect.extend(enc::mov_imm32(11, 0x8000_0000));
        expect.extend([
            enc::and(10, 10, 11),
            enc::bic(9, 9, 11),
            enc::orr(9, 9, 10),
            enc::fmov_s_from_w(16, 9),
            enc::fmov_d(0, 16),
            enc::ret(),
        ]);
        assert_eq!(w, expect);
    }

    #[test]
    fn f64_copysign_uses_x_forms_and_shifted_movz_mask() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::F64Copysign,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 2, &[], &[true, true]).unwrap();
        // The 0x8000_0000_0000_0000 mask must be ONE shifted movz (the
        // mov_imm64 halfword fix), clang: movz x11, #0x8000, lsl #48.
        assert_eq!(
            w,
            vec![
                enc::fmov_x_from_d(9, 0),
                enc::fmov_x_from_d(10, 1),
                0xD2F0_000B, // movz x11, #0x8000, lsl #48
                enc::and64(10, 10, 11),
                enc::bic64(9, 9, 11),
                enc::orr64(9, 9, 10),
                enc::fmov_d_from_x(16, 9),
                enc::fmov_d(0, 16),
                enc::ret()
            ]
        );
    }

    #[test]
    fn trapping_i64_truncations_are_domain_guarded_not_bare() {
        // v0.54 L2 (#851) — the soundness-critical half. A64 FCVTZ{S,U} with
        // an x destination SATURATE (NaN → 0, overflow → INT64_MIN/MAX) where
        // WASM §4.3.3 must TRAP, so each TRAPPING i64-target form must carry
        // the two-sided domain guard: exactly TWO `brk`s, and the convert must
        // be the LAST instruction before the epilogue (nothing may reach it
        // without passing both checks).
        for (op, f64_src, cvt) in [
            (
                WasmOp::I64TruncF32S,
                false,
                enc::fcvtzs_x_from_s as fn(Reg, FReg) -> u32,
            ),
            (WasmOp::I64TruncF32U, false, enc::fcvtzu_x_from_s),
            (WasmOp::I64TruncF64S, true, enc::fcvtzs_x_from_d),
            (WasmOp::I64TruncF64U, true, enc::fcvtzu_x_from_d),
        ] {
            let ops = vec![WasmOp::LocalGet(0), op.clone(), WasmOp::End];
            let (f32s, f64s): (&[bool], &[bool]) = if f64_src {
                (&[], &[true])
            } else {
                (&[true], &[])
            };
            let w = select_typed(&ops, 1, f32s, f64s).unwrap();
            assert_eq!(
                w.iter().filter(|&&x| x == enc::brk(0)).count(),
                2,
                "{op:?} needs BOTH range checks; got {w:#010X?}"
            );
            let cvt_at = w
                .iter()
                .position(|&x| x == cvt(9, 0))
                .unwrap_or_else(|| panic!("{op:?} must end in the x-form convert; got {w:#010X?}"));
            let last_brk = w.iter().rposition(|&x| x == enc::brk(0)).unwrap();
            assert!(
                cvt_at > last_brk,
                "{op:?}: the convert must sit AFTER both guards"
            );
        }
    }

    #[test]
    fn i64_trunc_signed_bounds_are_plus_2pow63_exclusive_minus_2pow63_inclusive() {
        // The two constants that decide whether a legal INT64_MIN input traps.
        // f32: -2^63 = 0xDF000000 is EXACTLY representable and truncates to
        // INT64_MIN (in range) — the bound must be INCLUSIVE (`b.ge`).
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I64TruncF32S, WasmOp::End];
        let w = select_typed(&ops, 1, &[true], &[]).unwrap();
        assert!(w.contains(&enc::movk(9, 0x5F00, 1)), "hi bound 2^63 (f32)");
        assert!(w.contains(&enc::movk(9, 0xDF00, 1)), "lo bound -2^63 (f32)");
        assert!(
            w.contains(&enc::bcond(Cond::Ge, 2)),
            "lo bound is INCLUSIVE"
        );
        assert!(
            w.contains(&enc::bcond(Cond::Mi, 2)),
            "hi bound is ORDERED <"
        );

        // f64: near 2^63 the ULP is 2048, so NO f64 lies in (-2^63-1, -2^63) —
        // the bound is the INCLUSIVE -2^63 (0xC3E0...0), NOT the strict
        // -(2^63)-1 shape the i32/f64 row needs.
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I64TruncF64S, WasmOp::End];
        let w = select_typed(&ops, 1, &[], &[true]).unwrap();
        let hi = enc::mov_imm64(9, 0x43E0_0000_0000_0000);
        let lo = enc::mov_imm64(9, 0xC3E0_0000_0000_0000);
        assert!(w.windows(hi.len()).any(|s| s == hi.as_slice()), "hi 2^63");
        assert!(w.windows(lo.len()).any(|s| s == lo.as_slice()), "lo -2^63");
        assert!(
            w.contains(&enc::bcond(Cond::Ge, 2)),
            "lo bound is INCLUSIVE"
        );
    }

    #[test]
    fn i64_trunc_unsigned_bounds_are_2pow64_and_strict_minus_one() {
        // trunc_u accepts (-1, 2^64): trunc_u(-0.5) = 0 is LEGAL, so the lower
        // bound is the STRICT -1.0 (`b.gt`), and the upper is 2^64 — NOT the
        // 2^32 the i32 forms use (which would trap every legal value above
        // 4294967295).
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I64TruncF32U, WasmOp::End];
        let w = select_typed(&ops, 1, &[true], &[]).unwrap();
        assert!(w.contains(&enc::movk(9, 0x5F80, 1)), "hi bound 2^64 (f32)");
        assert!(
            !w.contains(&enc::movk(9, 0x4F80, 1)),
            "must NOT use the 2^32 i32 bound"
        );
        assert!(w.contains(&enc::movk(9, 0xBF80, 1)), "lo bound -1.0 (f32)");
        assert!(w.contains(&enc::bcond(Cond::Gt, 2)), "lo bound is STRICT");

        let ops = vec![WasmOp::LocalGet(0), WasmOp::I64TruncF64U, WasmOp::End];
        let w = select_typed(&ops, 1, &[], &[true]).unwrap();
        let hi = enc::mov_imm64(9, 0x43F0_0000_0000_0000);
        assert!(w.windows(hi.len()).any(|s| s == hi.as_slice()), "hi 2^64");
        assert!(w.contains(&enc::bcond(Cond::Gt, 2)), "lo bound is STRICT");
    }

    #[test]
    fn type_confusion_gp_op_on_fp_value_errors() {
        // An f32 value fed to an integer op must ERROR (never read the wrong
        // register file) — the value-stack file tag guards this.
        let ops = vec![
            WasmOp::LocalGet(0), // f32 → s0
            WasmOp::LocalGet(1), // f32 → s1
            WasmOp::I32Add,      // GP op on FP operands → error
            WasmOp::End,
        ];
        assert!(select_typed(&ops, 2, &[true, true], &[]).is_err());
    }

    // ---- #538 control-flow increment: void blocks + br/br_if ----

    #[test]
    fn void_block_with_br_if_patches_forward_offset() {
        // (func (param i32 i32) (result i32)
        //   block                      ;; void
        //     local.get 0
        //     br_if 0                  ;; if p0 != 0, skip the add
        //     local.get 0
        //     local.get 1
        //     i32.add
        //     drop                     ;; keep the block void — result via a
        //     ...                      ;; (modeled without drop below: pure void body)
        //   end
        //   local.get 0
        //   end)
        // Simpler shape that stays void: the block body only conditionally traps.
        let ops = vec![
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrIf(0), // cbnz w0, <end>
            WasmOp::Unreachable,
            WasmOp::End, // block end — patch target
            WasmOp::LocalGet(1),
            WasmOp::End, // function end
        ];
        let w = select_typed_cf(&ops, 2, &[], &[], &[(0, 0)]).unwrap();
        // Layout: [0] cbnz w0, +2 ; [1] brk ; [2] mov x0,x1 ; [3] ret
        // The cbnz must skip exactly the brk (offset +2 words to the block end).
        assert_eq!(w[0], enc::cbnz(0, 2), "cbnz must target the block end (+2)");
        assert_eq!(w[1], enc::brk(0));
        assert_eq!(w[2], enc::mov_reg64(0, 1));
        assert_eq!(w[3], enc::ret());
        assert_eq!(w.len(), 4);
    }

    #[test]
    fn void_block_with_unconditional_br() {
        // block ; br 0 ; unreachable ; end ; local.get0 ; end
        // `br 0` unconditionally jumps to the block end, skipping the brk.
        let ops = vec![
            WasmOp::Block,
            WasmOp::Br(0), // b <end>
            WasmOp::Unreachable,
            WasmOp::End,
            WasmOp::LocalGet(0),
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0)]).unwrap();
        // [0] b +2 ; [1] brk ; [2] ret  (local.get 0 is w0 → no mov)
        assert_eq!(w[0], enc::b_uncond(2), "br must jump to the block end (+2)");
        assert_eq!(w[1], enc::brk(0));
        assert_eq!(w[2], enc::ret());
        assert_eq!(w.len(), 3);
    }

    #[test]
    fn nested_void_blocks_br_targets_correct_level() {
        // block            ;; outer (ord 0)
        //   block          ;; inner (ord 1)
        //     local.get 0
        //     br_if 1      ;; branch to OUTER end (2 levels: depth 1)
        //     unreachable
        //   end            ;; inner end
        //   unreachable
        // end              ;; outer end
        // local.get 0
        // end
        let ops = vec![
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrIf(1), // to outer end
            WasmOp::Unreachable,
            WasmOp::End, // inner end
            WasmOp::Unreachable,
            WasmOp::End, // outer end
            WasmOp::LocalGet(0),
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0), (0, 0)]).unwrap();
        // [0] cbnz w0, ? ; [1] brk (inner) ; [2] brk (after inner end) ; [3] ret
        // Outer end is at word index 3. cbnz at 0 → offset +3.
        assert_eq!(
            w[0],
            enc::cbnz(0, 3),
            "br_if 1 must reach the OUTER end (+3)"
        );
        assert_eq!(w[1], enc::brk(0));
        assert_eq!(w[2], enc::brk(0));
        assert_eq!(w[3], enc::ret());
        assert_eq!(w.len(), 4);
    }

    // ---- VCR-A64-CF-001 — value-carrying frames + br_table -----------------

    #[test]
    fn typed_block_reconciles_its_result_into_one_register() {
        // `(func (param i32) (result i32) (block (result i32) (local.get 0)))`
        // — the shape that used to loud-decline. The fall-through `end`
        // deposits into the frame's reserved register; the function epilogue
        // then funnels THAT register into x0.
        let ops = vec![
            WasmOp::Block, // arity (0,1)
            WasmOp::LocalGet(0),
            WasmOp::End,
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 1)]).unwrap();
        // The block reserves x9 (first free temp); `local.get 0` is a leaf
        // param read, so the value is w0 by reference. end: mov x9, x0 ;
        // fn-end: mov x0, x9 ; ret.
        assert_eq!(
            w,
            vec![enc::mov_reg64(9, 0), enc::mov_reg64(0, 9), enc::ret()]
        );
    }

    #[test]
    fn value_carrying_br_if_deposits_into_the_same_register_as_the_fallthrough() {
        // `(block (result i32) (br_if 0 (i32.const 7) (local.get 0))
        //                      (drop) (i32.const 9))` — the two edges into the
        // join must land the result in ONE register. The whole point of the
        // reconciliation slot.
        let ops = vec![
            WasmOp::Block, // (0,1)
            WasmOp::I32Const(7),
            WasmOp::LocalGet(0),
            WasmOp::BrIf(0),
            WasmOp::Drop,
            WasmOp::I32Const(9),
            WasmOp::End,
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 1)]).unwrap();
        // Slot = x9. const 7 -> x10 (x9 reserved). br_if: mov x9, x10 ;
        // cbnz w0, <end>. drop pops x10. const 9 -> x10. end: mov x9, x10.
        // Both edges write x9 — that is the assertion.
        let movs: Vec<usize> = w
            .iter()
            .enumerate()
            .filter(|(_, x)| **x == enc::mov_reg64(9, 10))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(
            movs.len(),
            2,
            "both the br_if edge and the fall-through must deposit into the \
             slot register: {w:#010x?}"
        );
        // The cbnz must target the word AFTER the fall-through's deposit.
        let cbnz_at = w
            .iter()
            .position(|x| x & 0xFF00_0000 == 0x3500_0000)
            .expect("br_if emits a cbnz");
        let off = ((w[cbnz_at] >> 5) & 0x7FFFF) as usize;
        assert_eq!(
            cbnz_at + off,
            movs[1] + 1,
            "the taken edge must land PAST the fall-through's reconciliation \
             move, not on it (or it would re-run with a dead operand)"
        );
    }

    #[test]
    fn value_carrying_loop_does_not_reconcile_on_the_back_edge() {
        // SOUNDNESS-CRITICAL asymmetry. A `br` to a LOOP label carries the
        // loop's PARAMETERS (0 here), NOT its results — so a `loop (result
        // i32)` back-edge must emit NO reconciliation move. If it did, every
        // iteration would stamp a garbage value into the result register.
        //
        // `(block (loop (result i32) ... ) )` is awkward to write with raw
        // ops; use the direct shape: loop (0,1) whose body branches back on a
        // condition, then falls through with the result.
        let ops = vec![
            WasmOp::Loop, // (0,1)
            WasmOp::LocalGet(0),
            WasmOp::BrIf(0), // back-edge: label arity 0 → NO deposit
            WasmOp::I32Const(5),
            WasmOp::End,
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 1)]).unwrap();
        // Words: cbnz w0, -0 (back to header) ; mov x10, #5 ; mov x9, x10 ;
        // mov x0, x9 ; ret. Exactly ONE mov into the slot (the fall-through).
        let deposits = w.iter().filter(|x| **x == enc::mov_reg64(9, 10)).count();
        assert_eq!(
            deposits, 1,
            "a loop's back-edge must NOT reconcile (label arity = PARAMS): \
             {w:#010x?}"
        );
        // And the back-edge is a real backward branch (negative imm19).
        let cbnz = w[0];
        assert_eq!(cbnz & 0xFF00_0000, 0x3500_0000, "back-edge is a cbnz");
        assert_eq!(
            (cbnz >> 5) & 0x7FFFF,
            0,
            "the back-edge targets the loop header at offset 0"
        );
    }

    #[test]
    fn value_producing_if_else_lands_both_arms_in_one_register() {
        // `(if (result i32) (then (i32.const 1)) (else (i32.const 2)))`.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::If, // (0,1)
            WasmOp::I32Const(1),
            WasmOp::Else,
            WasmOp::I32Const(2),
            WasmOp::End,
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 1)]).unwrap();
        let deposits = w.iter().filter(|x| **x == enc::mov_reg64(9, 10)).count();
        assert_eq!(
            deposits, 2,
            "then-arm (at `else`) and else-arm (at `end`) must BOTH deposit \
             into the slot: {w:#010x?}"
        );
    }

    #[test]
    fn block_params_and_multi_value_results_still_loud_decline() {
        // The residuals, named. The slot is ONE register: block PARAMS would
        // need a per-path multi-register shuffle, multi-value more than one
        // slot. Both must decline rather than silently drop a value.
        let block = vec![WasmOp::Block, WasmOp::End, WasmOp::End];
        let e = select_typed_cf(&block, 0, &[], &[], &[(1, 1)]).unwrap_err();
        assert!(
            e.0.contains("PARAMETER-taking block type"),
            "block params must decline by name, got: {}",
            e.0
        );
        let e = select_typed_cf(&block, 0, &[], &[], &[(0, 2)]).unwrap_err();
        assert!(
            e.0.contains("MULTI-VALUE result block type"),
            "multi-value must decline by name, got: {}",
            e.0
        );
        // Same for `loop`: a PARAM loop is the shape whose back-edge would need
        // the value stack live across the header.
        let lp = vec![WasmOp::Loop, WasmOp::End, WasmOp::End];
        assert!(
            select_typed_cf(&lp, 0, &[], &[], &[(1, 0)])
                .unwrap_err()
                .0
                .contains("PARAMETER-taking block type")
        );
    }

    #[test]
    fn br_table_emits_a_compare_chain_with_a_default_fallthrough() {
        // `(block (block (block (br_table 0 1 2 (local.get 0)))))` — three
        // targets at depths 0/1/2, default = 2.
        let ops = vec![
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0, 1],
                default: 2,
            },
            WasmOp::End,
            WasmOp::End,
            WasmOp::End,
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 3, &[], &[], &[(0, 0), (0, 0), (0, 0)]).unwrap();
        // idx = w0 (leaf param, by reference). Chain:
        //   [0] cbz  w0, <innermost end>      (entry 0)
        //   [1] cmp  w0, #1
        //   [2] b.eq <middle end>             (entry 1)
        //   [3] b    <outer end>              (default)
        //   [4] ret
        assert_eq!(w.len(), 5, "{w:#010x?}");
        assert_eq!(
            w[0],
            enc::cbz(0, 4),
            "entry 0 is a bare cbz to the innermost end"
        );
        assert_eq!(w[1], enc::cmp_imm(0, 1));
        assert_eq!(w[2], enc::bcond(Cond::Eq, 2), "entry 1 -> middle end");
        assert_eq!(w[3], enc::b_uncond(1), "default -> outer end");
        assert_eq!(w[4], enc::ret());
    }

    #[test]
    fn br_table_can_target_a_loop_header_backward_and_a_block_end_forward() {
        // One table, MIXED destinations: depth 0 = the enclosing loop (its
        // HEADER, backward, eagerly resolved) and depth 1 = a block END
        // (forward, patched). A lowering that assumed one direction would
        // emit a wrong offset for the other.
        let ops = vec![
            WasmOp::Block, // depth 1 from inside the loop
            WasmOp::Loop,  // depth 0
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0],
                default: 1,
            },
            WasmOp::End, // loop end
            WasmOp::End, // block end
            WasmOp::End, // fn end
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0), (0, 0)]).unwrap();
        // [0] cbz w0, 0   (loop header is word 0 → offset 0-0 = 0, BACKWARD/self)
        // [1] b   +1      (default → block end at word 2)
        // [2] ret
        assert_eq!(w.len(), 3, "{w:#010x?}");
        assert_eq!(
            w[0],
            enc::cbz(0, 0),
            "loop target resolves eagerly to the header"
        );
        assert_eq!(
            w[1],
            enc::b_uncond(1),
            "default is a patched forward branch"
        );
        assert_eq!(w[2], enc::ret());
    }

    #[test]
    fn br_table_residuals_loud_decline_by_name() {
        // (1) Past the compare-chain threshold.
        let big = vec![
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0; BR_TABLE_MAX_TARGETS + 1],
                default: 0,
            },
            WasmOp::End,
            WasmOp::End,
        ];
        let e = select_typed_cf(&big, 1, &[], &[], &[(0, 0)]).unwrap_err();
        assert!(
            e.0.contains("exceeds the aarch64 compare-chain threshold"),
            "oversized br_table must decline by name, got: {}",
            e.0
        );
        // Exactly at the threshold still lowers (the boundary is not off-by-one).
        let at = vec![
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0; BR_TABLE_MAX_TARGETS],
                default: 0,
            },
            WasmOp::End,
            WasmOp::End,
        ];
        assert!(select_typed_cf(&at, 1, &[], &[], &[(0, 0)]).is_ok());

        // (2) A VALUE-CARRYING target. The flat chain has no per-path edge to
        //     deposit a result on, so it refuses rather than miscompile.
        let vc = vec![
            WasmOp::Block, // (0,1) — value-carrying label
            WasmOp::I32Const(1),
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0],
                default: 0,
            },
            WasmOp::End,
            WasmOp::End,
        ];
        let e = select_typed_cf(&vc, 1, &[], &[], &[(0, 1)]).unwrap_err();
        assert!(
            e.0.contains("VALUE-CARRYING targets"),
            "value-carrying br_table must decline by name, got: {}",
            e.0
        );
    }

    #[test]
    fn void_if_without_else_emits_cbz_skip() {
        // `if (then unreachable)` with cond in w0: cbz w0, <past-then> ; brk ;
        // then fall-through. The cbz skips the then-arm when cond == 0.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::Unreachable,
            WasmOp::End, // if-end
            WasmOp::End, // fn-end
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0)]).unwrap();
        // cbz w0, .+8 (skip the brk) ; brk #0 ; ret
        assert_eq!(w[0], enc::cbz(0, 2));
        assert_eq!(w[1], enc::brk(0));
        assert_eq!(w[2], enc::ret());
    }

    #[test]
    fn void_if_else_patches_both_edges() {
        // if(cond){} else{} — void arms. cbz skips to the else entry; the
        // then-arm's trailing `b` skips the else-arm to the join.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::If,
            WasmOp::Else,
            WasmOp::Unreachable,
            WasmOp::End,
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0)]).unwrap();
        // cbz w0, else ; b end ; brk ; ret
        // then-arm is empty: cbz lands at the `b`? No — cbz skips the then-arm
        // to the else entry. then-arm empty → cbz to the b's fall-through.
        // Layout: [0] cbz w0, else_entry ; [1] b end ; [2] brk ; [3] ret
        assert_eq!(w[0], enc::cbz(0, 2)); // to word 2 (else entry = brk)
        assert_eq!(w[1], enc::b_uncond(2)); // skip else-arm to word 3 (ret)
        assert_eq!(w[2], enc::brk(0));
        assert_eq!(w[3], enc::ret());
    }

    #[test]
    fn loop_back_edge_is_negative_offset() {
        // block { loop { <body> br 0 } } — the `br 0` targets the loop header
        // (BACKWARD), resolving to a negative offset. A `local.tee`/`local.get`
        // on a NON-PARAM local emits real instructions ahead of the `br`, so
        // the back-edge offset is strictly negative. Frame: 1 non-param local
        // (idx 1) → a sub-sp + str-xzr prologue, then the loop body.
        let ops = vec![
            WasmOp::Block,
            WasmOp::Loop,
            WasmOp::LocalGet(1), // non-param local read → ldr (real instr)
            WasmOp::LocalSet(1), // → str (real instr) — loop body has 2 instrs
            WasmOp::Br(0),       // back-edge to loop header
            WasmOp::End,         // loop end
            WasmOp::End,         // block end
            WasmOp::End,         // fn end
        ];
        // arity table: Block, Loop → two (0,0) entries.
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0), (0, 0)]).unwrap();
        // Find the back-edge `b` (0x14…): it must carry a NEGATIVE imm26.
        let br = w
            .iter()
            .find(|&&x| x & 0xFC00_0000 == 0x1400_0000)
            .expect("a back-edge b must be emitted");
        let imm26 = (br & 0x03FF_FFFF) as i32;
        let signed = (imm26 << 6) >> 6; // sign-extend 26 bits
        assert!(
            signed < 0,
            "loop back-edge must be a negative offset, got {signed}"
        );
    }

    #[test]
    fn early_return_emits_epilogue_ret() {
        // `local.get 0 ; return` — funnels w0 and rets early, then the trailing
        // fn-end epilogue rets again (unreachable).
        let ops = vec![WasmOp::LocalGet(0), WasmOp::Return, WasmOp::End];
        let w = select_typed_cf(&ops, 1, &[], &[], &[]).unwrap();
        // local.get 0 → mov x9,x0 ; return → mov x0,x9 ; ret
        assert_eq!(*w.last().unwrap(), enc::ret());
        assert!(w.contains(&enc::ret()));
    }

    #[test]
    fn br_beyond_open_nesting_declines() {
        // `br 1` with only one open block targets the function body — unsupported.
        let ops = vec![
            WasmOp::Block,
            WasmOp::Br(1), // depth 1 but only 1 block open → decline
            WasmOp::End,
            WasmOp::End,
        ];
        assert!(select_typed_cf(&ops, 0, &[], &[], &[(0, 0)]).is_err());
    }

    #[test]
    fn empty_arity_table_defaults_to_void_block() {
        // Hand-built op streams (empty arity table) treat a block as void (0,0),
        // matching the decoder's `unwrap_or((0,0))` convention.
        let ops = vec![
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrIf(0),
            WasmOp::Unreachable,
            WasmOp::End,
            WasmOp::LocalGet(0),
            WasmOp::End,
        ];
        let w = select_typed_cf(&ops, 1, &[], &[], &[]).unwrap();
        assert_eq!(w[0], enc::cbnz(0, 2));
    }

    // --- #851 non-param locals ---

    #[test]
    fn no_non_param_locals_is_byte_identical() {
        // A function that only touches params emits NO frame — byte-identical to
        // the pre-#851 lowering (the localizing guard).
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 2).unwrap();
        assert_eq!(w, vec![enc::add(9, 0, 1), enc::mov_reg64(0, 9), enc::ret()]);
    }

    #[test]
    fn two_non_param_locals_frame_and_ops() {
        // (result i32) (local i32 i32)
        // local.set 0 (const 5); local.set 1 (const 7); local.get 0 + local.get 1
        // 0 params, 2 non-param locals → frame rounds 2*8=16 to 16.
        let ops = vec![
            WasmOp::I32Const(5),
            WasmOp::LocalSet(0),
            WasmOp::I32Const(7),
            WasmOp::LocalSet(1),
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 0).unwrap();
        assert_eq!(
            w,
            vec![
                // prologue: sub sp,sp,#16 ; zero both slots
                enc::sub_imm64(enc::SP, enc::SP, 16),
                enc::str_x_imm(enc::XZR, enc::SP, 0),
                enc::str_x_imm(enc::XZR, enc::SP, 8),
                // const 5 -> w9 ; set local 0 (slot 0)
                enc::movz(9, 5),
                enc::str_x_imm(9, enc::SP, 0),
                // const 7 -> w9 (freed) ; set local 1 (slot 8)
                enc::movz(9, 7),
                enc::str_x_imm(9, enc::SP, 8),
                // get local 0 -> w9 ; get local 1 -> w10
                enc::ldr_x_imm(9, enc::SP, 0),
                enc::ldr_x_imm(10, enc::SP, 8),
                enc::add(9, 9, 10),
                enc::mov_reg64(0, 9),
                // epilogue: restore sp ; ret
                enc::add_imm64(enc::SP, enc::SP, 16),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn non_param_local_zero_init_read_before_write() {
        // A non-param local read BEFORE any write must read 0. With 1 param and
        // one non-param local (index 1), get local 1 loads the zeroed slot.
        // 1 param + 1 non-param local → frame 8 rounds to 16.
        let ops = vec![
            WasmOp::LocalGet(0), // param
            WasmOp::LocalGet(1), // non-param local, read-first → must be 0
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 1).unwrap();
        assert_eq!(
            w,
            vec![
                enc::sub_imm64(enc::SP, enc::SP, 16),
                enc::str_x_imm(enc::XZR, enc::SP, 0), // zero the one slot
                enc::ldr_x_imm(9, enc::SP, 0),        // get local 1 (zeroed)
                enc::add(9, 0, 9),                    // param0 + local1
                enc::mov_reg64(0, 9),
                enc::add_imm64(enc::SP, enc::SP, 16),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn local_get_set_get_no_alias() {
        // THE aliasing regression: get local 1 (push), set local 1 := 5, get
        // local 1 (push), add. Stack slots make each get a FRESH load, so the
        // first pushed value is the OLD slot (0), not clobbered by the set.
        // wasmtime: 0 + 5 = 5. A read-by-reference model would give 5 + 5 = 10.
        // 0 params, 1 non-param local (index 0) → frame 8 rounds to 16.
        let ops = vec![
            WasmOp::LocalGet(0), // load slot (0) into w9
            WasmOp::I32Const(5),
            WasmOp::LocalSet(0), // slot := 5 (does NOT touch w9 on the stack)
            WasmOp::LocalGet(0), // load slot (5) into a fresh temp
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let w = select(&ops, 0).unwrap();
        assert_eq!(
            w,
            vec![
                enc::sub_imm64(enc::SP, enc::SP, 16),
                enc::str_x_imm(enc::XZR, enc::SP, 0), // zero-init
                enc::ldr_x_imm(9, enc::SP, 0),        // get -> w9 (=0, on stack)
                enc::movz(10, 5),                     // const 5 -> w10 (w9 live)
                enc::str_x_imm(10, enc::SP, 0),       // set slot := 5
                enc::ldr_x_imm(10, enc::SP, 0),       // get -> w10 (=5, fresh)
                enc::add(9, 9, 10),                   // 0 + 5
                enc::mov_reg64(0, 9),
                enc::add_imm64(enc::SP, enc::SP, 16),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn local_tee_stores_and_keeps_value() {
        // tee local 0 := (const 9) leaves 9 on the stack; then double it.
        let ops = vec![
            WasmOp::I32Const(9),
            WasmOp::LocalTee(0), // slot := w9, w9 stays on stack
            WasmOp::LocalGet(0), // reload slot -> w10
            WasmOp::I32Add,      // 9 + 9
            WasmOp::End,
        ];
        let w = select(&ops, 0).unwrap();
        assert_eq!(
            w,
            vec![
                enc::sub_imm64(enc::SP, enc::SP, 16),
                enc::str_x_imm(enc::XZR, enc::SP, 0),
                enc::movz(9, 9),
                enc::str_x_imm(9, enc::SP, 0), // tee stores WITHOUT popping
                enc::ldr_x_imm(10, enc::SP, 0),
                enc::add(9, 9, 10),
                enc::mov_reg64(0, 9),
                enc::add_imm64(enc::SP, enc::SP, 16),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn set_param_loud_declines() {
        // Writing a PARAMETER is declined (params are read-by-reference; homing
        // written params is a later increment) — never silently miscompiled.
        let ops = vec![WasmOp::I32Const(1), WasmOp::LocalSet(0), WasmOp::End];
        assert!(select(&ops, 1).is_err());
    }

    #[test]
    fn local_across_void_block_balances_sp() {
        // A non-param local read/written across a void block with a br_if out.
        // The frame `sub sp` is emitted ONCE at prologue and the block never
        // touches SP; the single `add sp` fires only at the OUTER End (the block
        // End takes the ctrl-pop path, no epilogue). So SP is balanced on every
        // path: exactly one `sub sp` and exactly one matching `add sp`.
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::LocalSet(1),
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrIf(0),
            WasmOp::I32Const(2),
            WasmOp::LocalSet(1),
            WasmOp::End, // block end — NO epilogue, NO sp adjust
            WasmOp::LocalGet(1),
            WasmOp::End, // function end — the one epilogue
        ];
        // 1 param, 1 non-param local (index 1) → frame 8 rounds to 16.
        let w = select_typed_cf(&ops, 1, &[], &[], &[(0, 0)]).unwrap();
        let subs = w
            .iter()
            .filter(|&&x| x == enc::sub_imm64(enc::SP, enc::SP, 16))
            .count();
        let adds = w
            .iter()
            .filter(|&&x| x == enc::add_imm64(enc::SP, enc::SP, 16))
            .count();
        assert_eq!(subs, 1, "exactly one prologue sub sp");
        assert_eq!(adds, 1, "exactly one epilogue add sp — SP balanced");
        // The prologue sub is the very first word; the epilogue add is the
        // second-to-last (before ret).
        assert_eq!(w[0], enc::sub_imm64(enc::SP, enc::SP, 16));
        assert_eq!(w[w.len() - 1], enc::ret());
        assert_eq!(w[w.len() - 2], enc::add_imm64(enc::SP, enc::SP, 16));
    }

    // --- #851 / VCR-SEL-005 third-backend op-surface closes ---

    #[test]
    fn select_gp_lowers_to_cmp_csel() {
        // (param i32 i32 i32) select(v1=p0, v2=p1, c=p2):
        //   cmp w2, wzr ; csel x9, x0, x1, ne ; mov x0, x9 ; ret
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(2),
            WasmOp::Select,
            WasmOp::End,
        ];
        let w = select(&ops, 3).unwrap();
        assert_eq!(
            w,
            vec![
                enc::cmp(2, enc::WZR),
                enc::csel64(9, 0, 1, Cond::Ne),
                enc::mov_reg64(0, 9),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn select_fp_lowers_to_cmp_fcsel() {
        // (param f32 f32 i32): FP operands (s0, s1 under the independent NSRN
        // counter), GP condition (w0). fcsel on NE picks v1.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::LocalGet(2),
            WasmOp::Select,
            WasmOp::End,
        ];
        let w = select_typed(&ops, 3, &[true, true, false], &[]).unwrap();
        assert_eq!(
            w,
            vec![
                enc::cmp(0, enc::WZR),
                enc::fcsel_d(16, 0, 1, Cond::Ne),
                enc::fmov_d(0, 16),
                enc::ret(),
            ]
        );
    }

    #[test]
    fn select_mixed_files_loud_declines() {
        // v1 GP, v2 FP — a register-file mismatch must be loud, never silent.
        let ops = vec![
            WasmOp::I32Const(1),
            WasmOp::F32Const(1.0),
            WasmOp::I32Const(1),
            WasmOp::Select,
            WasmOp::End,
        ];
        assert!(select(&ops, 0).is_err());
    }

    #[test]
    fn drop_pops_and_emits_nothing() {
        // const 7 (movz) is dropped; result is p0 already in x0 → just ret.
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::I32Const(7),
            WasmOp::Drop,
            WasmOp::End,
        ];
        let w = select(&ops, 1).unwrap();
        assert_eq!(w, vec![enc::movz(9, 7), enc::ret()]);
    }

    #[test]
    fn nop_emits_nothing() {
        let ops = vec![WasmOp::Nop, WasmOp::LocalGet(0), WasmOp::Nop, WasmOp::End];
        let w = select(&ops, 1).unwrap();
        assert_eq!(w, vec![enc::ret()]);
    }

    #[test]
    fn wrap_and_extends_lower_to_mov_sxt() {
        for (op, want) in [
            (WasmOp::I32WrapI64, enc::mov_reg(9, 0)),
            (WasmOp::I64ExtendI32U, enc::mov_reg(9, 0)),
            (WasmOp::I64ExtendI32S, enc::sxtw(9, 0)),
            (WasmOp::I64Extend32S, enc::sxtw(9, 0)),
            (WasmOp::I32Extend8S, enc::sxtb(9, 0)),
            (WasmOp::I32Extend16S, enc::sxth(9, 0)),
            (WasmOp::I64Extend8S, enc::sxtb64(9, 0)),
            (WasmOp::I64Extend16S, enc::sxth64(9, 0)),
        ] {
            let ops = vec![WasmOp::LocalGet(0), op.clone(), WasmOp::End];
            let w = select(&ops, 1).unwrap();
            assert_eq!(
                w,
                vec![want, enc::mov_reg64(0, 9), enc::ret()],
                "lowering mismatch for {op:?}"
            );
        }
    }

    #[test]
    fn memory_size_is_page_count_constant() {
        // (memory 2) → 131072 bytes → memory.size = 2.
        let ops = vec![WasmOp::MemorySize(0), WasmOp::End];
        let w = sel_mem(
            &ops,
            0,
            MemBounds::Software {
                limit_bytes: 131072,
            },
        );
        assert_eq!(w, vec![enc::movz(9, 2), enc::mov_reg64(0, 9), enc::ret()]);
    }

    #[test]
    fn memory_grow_zero_is_size_nonzero_is_minus_one() {
        // grow(delta): mov t0,#pages ; mov t1,#-1 ; cmp delta,wzr ; csel eq.
        let ops = vec![WasmOp::LocalGet(0), WasmOp::MemoryGrow(0), WasmOp::End];
        let w = sel_mem(&ops, 1, MemBounds::Software { limit_bytes: 65536 });
        let mut expect = vec![enc::movz(9, 1)];
        expect.extend(enc::mov_imm32(10, u32::MAX));
        expect.push(enc::cmp(0, enc::WZR));
        expect.push(enc::csel(9, 9, 10, Cond::Eq));
        expect.push(enc::mov_reg64(0, 9));
        expect.push(enc::ret());
        assert_eq!(w, expect);
    }

    #[test]
    fn memory_size_declines_without_limit() {
        // Under --safety-bounds none no limit is threaded — decline loudly.
        let ops = vec![WasmOp::MemorySize(0), WasmOp::End];
        let r = select_typed_cf_calls(
            &ops,
            0,
            &[],
            &[],
            &[],
            0,
            &[],
            &[],
            &[],
            MemBounds::Unchecked,
            &ModuleCtx::default(),
        );
        assert!(r.is_err());
    }

    #[test]
    fn three_locals_frame_rounds_to_32() {
        // 0 params, 3 non-param locals → 3*8 = 24 rounds up to 32.
        let ops = vec![
            WasmOp::LocalGet(2), // touch index 2 → 3 locals (0,1,2)
            WasmOp::End,
        ];
        let w = select(&ops, 0).unwrap();
        assert_eq!(w[0], enc::sub_imm64(enc::SP, enc::SP, 32));
        // three zeroing stores at offsets 0,8,16
        assert_eq!(w[1], enc::str_x_imm(enc::XZR, enc::SP, 0));
        assert_eq!(w[2], enc::str_x_imm(enc::XZR, enc::SP, 8));
        assert_eq!(w[3], enc::str_x_imm(enc::XZR, enc::SP, 16));
        // slot for local 2 is at offset 16
        assert_eq!(w[4], enc::ldr_x_imm(9, enc::SP, 16));
        // epilogue restores 32
        assert_eq!(w[w.len() - 2], enc::add_imm64(enc::SP, enc::SP, 32));
    }
}
