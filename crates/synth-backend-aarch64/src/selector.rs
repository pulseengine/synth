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
//! **Deliberately still declined (loud-skip, never wrong code):**
//! - `div_s/div_u/rem_s/rem_u` (i32 and i64): A64 `SDIV`/`UDIV` do NOT trap on
//!   divide-by-zero or `INT_MIN÷-1`, whereas WASM requires a trap. Lowering them
//!   naively is the "ARM more-total-than-WASM" silent-miscompile class; they are
//!   left for a later milestone that adds the explicit trap guards.
//! - `popcnt`: no scalar A64 popcount pre-SVE (needs SIMD `CNT`+`ADDV`).
//! - memory, calls, spilling. (Forward void-block control flow lands in the
//!   #538-cf increment; NON-PARAM LOCALS land in #851 — see below.)
//!
//! **#851 — non-param locals:** GP locals beyond the params (index >=
//! `num_params`) get zero-initialized 8-byte stack slots (`[sp, #(idx -
//! num_params)*8]`, frame rounded to a 16-byte SP-aligned multiple), only when
//! the function actually declares one. `local.get` LOADS the slot into a fresh
//! temp (copy-semantics — a later `local.set` of the same index cannot alias a
//! stacked value), `local.set`/`local.tee` store it (tee without popping).
//! 64-bit slots preserve both i32 and i64. Still declined here: writing a
//! PARAMETER (params live in arg registers by reference — a later increment
//! homes them) and FP non-param locals (their types are not threaded to the
//! backend, so an FP `local.set` is caught by the GP file-check and declined).
//!
//! **Milestone 3 adds scalar floating point** (the separate V/D/S register file):
//! f32/f64 const, add/sub/mul/div, abs/neg/sqrt, the full compare family, the
//! f32<->f64 conversions (promote/demote), the int->float conversions
//! (`convert_i32_{s,u}` → SCVTF/UCVTF), and the reinterprets (FMOV GP<->FP).
//! The value stack now tags each entry with its register FILE (GP vs FP) so an
//! f32 param (delivered in `s0..` under AAPCS64, a counter INDEPENDENT of the
//! GP arg registers) is never confused with a GP operand.
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

/// The GP value-stack temp registers: caller-saved `w9/x9..w15/x15` (7 slots).
/// `w0..w7` hold incoming integer params; results funnel back through `x0`.
const TEMPS: [Reg; 7] = [9, 10, 11, 12, 13, 14, 15];

/// The FP value-stack temp registers: caller-saved `v16..v23` (the low `v0..v7`
/// carry incoming float params, `v8..v15` are callee-saved). 8 scratch slots.
const FTEMPS: [FReg; 8] = [16, 17, 18, 19, 20, 21, 22, 23];

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
/// OOB-trap, data-segment init, and memory.{size,grow}).
const LINMEM_BASE: Reg = 28;

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
    let (words, _sites) = select_typed_cf_calls(
        ops,
        num_params,
        params_f32,
        params_f64,
        block_arity,
        0,
        &[],
        &[],
        &[],
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
) -> Result<(Vec<u32>, Vec<CallSite>), SelectError> {
    if num_params > 8 {
        return Err(SelectError(format!(
            "{num_params} params — supports at most 8 register params"
        )));
    }

    // #851 — is this function NON-LEAF (contains a `call` we will lower)? A `bl`
    // clobbers x30, so a non-leaf must save/restore LR. Computed up front so the
    // prologue can emit the frame; call-free functions stay byte-identical.
    let is_non_leaf = ops.iter().any(|op| matches!(op, WasmOp::Call(_)));

    // A non-leaf function that reads a PARAMETER is loud-declined: params arrive
    // in x0..x7 (caller-saved), a `bl` clobbers them, and this backend does not
    // yet HOME params to callee-saved storage — reading `local.get p` after a
    // call would be garbage. Declining here ALSO makes arg marshalling
    // hazard-free: with no param-Vals, every value-stack entry lives in a temp
    // (x9..x15), disjoint from the arg destinations (x0..x7), so an argument
    // move `mov x{arg}, x{temp}` never overwrites a not-yet-read source.
    if is_non_leaf
        && ops.iter().any(
            |op| matches!(op, WasmOp::LocalGet(i) | WasmOp::LocalSet(i) | WasmOp::LocalTee(i) if *i < num_params),
        )
    {
        return Err(SelectError(
            "non-leaf function references a parameter — param homing across a \
             call is not yet supported for aarch64; loud-declining (#851)"
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
    let num_non_param_locals = match max_local_idx {
        Some(m) if m >= num_params => m - num_params + 1,
        _ => 0,
    };
    // Frame size in bytes: one 8-byte slot per non-param local, rounded UP to a
    // 16-byte multiple (the ABI requires 16-byte SP alignment).
    let frame_size: u32 = if num_non_param_locals == 0 {
        0
    } else {
        (num_non_param_locals * 8).div_ceil(16) * 16
    };
    // Byte offset of non-param local `idx`'s slot from SP.
    let local_slot_off = |idx: u32| -> u32 { (idx - num_params) * 8 };

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
        for k in 0..num_non_param_locals {
            words.push(enc::str_x_imm(enc::XZR, enc::SP, k * 8));
        }
    }

    // #851 — direct-call sites recorded during selection (byte offset of the
    // `bl`, callee full index) for the backend's R_AARCH64_CALL26 relocations.
    let mut call_sites: Vec<CallSite> = Vec::new();

    // Control-flow state (#538 cf increment). Each open `block` pushes a frame;
    // the matching `End` pops it and patches the recorded forward branches to
    // land at the current instruction position (the block's fall-through point).
    struct Frame {
        /// Word positions in `words` of branches targeting this block's END,
        /// awaiting fix-up when the block closes.
        pending: Vec<usize>,
        /// Value-stack height on entry — a void block must restore it at `End`.
        stack_entry: usize,
    }
    let mut ctrl: Vec<Frame> = Vec::new();
    // Ordinal counter over Block/Loop/If in op order — the key into
    // `block_arity`. Incremented on EVERY control op encountered (even declined
    // ones, though a decline aborts the whole compile so alignment is moot).
    let mut ctrl_ord: usize = 0;

    // Pick a GP temp not holding a live GP value-stack entry.
    let alloc_temp = |stack: &[Val]| -> Result<Reg, SelectError> {
        TEMPS
            .iter()
            .copied()
            .find(|t| !stack.iter().any(|v| v.file == File::Gp && v.reg == *t))
            .ok_or_else(|| SelectError("value-stack too deep (GP temp regs exhausted)".into()))
    };
    // Pick an FP temp not holding a live FP value-stack entry.
    let alloc_ftemp = |stack: &[Val]| -> Result<FReg, SelectError> {
        FTEMPS
            .iter()
            .copied()
            .find(|t| !stack.iter().any(|v| v.file == File::Fp && v.reg == *t))
            .ok_or_else(|| SelectError("value-stack too deep (FP temp regs exhausted)".into()))
    };

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
    let trunc_guarded = |words: &mut Vec<u32>,
                         stack: &mut Vec<Val>,
                         is_f64: bool,
                         signed: bool|
     -> Result<(), SelectError> {
        let a = pop_fp(stack, "trunc")?;
        // Keep `a` live across temp allocation: it is read by both fcmps and
        // the final convert, so the bound register must never alias it.
        stack.push(Val::fp(a));
        let dst = alloc_temp(stack)?; // GP: const scratch, then the result
        let bound = alloc_ftemp(stack)?;
        stack.pop();
        let (hi_bits, lo_bits, lo_cond): (u64, u64, Cond) = match (is_f64, signed) {
            (false, true) => (0x4F00_0000, 0xCF00_0000, Cond::Ge),
            (false, false) => (0x4F80_0000, 0xBF80_0000, Cond::Gt),
            (true, true) => (0x41E0_0000_0000_0000, 0xC1E0_0000_0020_0000, Cond::Gt),
            (true, false) => (0x41F0_0000_0000_0000, 0xBFF0_0000_0000_0000, Cond::Gt),
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
        words.push(match (is_f64, signed) {
            (false, true) => enc::fcvtzs_w_from_s(dst, a),
            (false, false) => enc::fcvtzu_w_from_s(dst, a),
            (true, true) => enc::fcvtzs_w_from_d(dst, a),
            (true, false) => enc::fcvtzu_w_from_d(dst, a),
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
            let mut free = TEMPS
                .iter()
                .copied()
                .filter(|t| !stack.iter().any(|v| v.file == File::Gp && v.reg == *t));
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
    // SOUNDNESS / honest frontier: this computes the WASM effective address and
    // dereferences it against the ambient base — it does NOT bounds-check. WASM
    // requires an out-of-bounds access to TRAP; the host-native subset has no
    // memory-size convention yet, so OOB is UNTRAPPED (reads/writes adjacent host
    // memory). In-bounds load/store is execution-verified vs wasmtime; OOB-trap,
    // data-segment init, and memory.{size,grow} are the documented follow-ons.
    let form_ea = |words: &mut Vec<u32>,
                   stack: &mut Vec<Val>,
                   addr: Reg,
                   offset: u32,
                   size_log2: u32|
     -> Result<(Reg, Option<u32>), SelectError> {
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

    for op in ops {
        match op {
            WasmOp::LocalGet(i) => {
                if *i >= num_params {
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
            // Non-param locals live in stack slots (`str` the value). A param
            // target is LOUD-DECLINED: params live in arg registers BY REFERENCE
            // on the value stack, so writing one could alias a value already
            // pushed (the miscompile the slot model avoids for non-param locals);
            // homing written params is a later increment.
            WasmOp::LocalSet(i) => {
                if *i >= num_params {
                    let src = pop_gp(&mut stack, "local.set")?;
                    words.push(enc::str_x_imm(src, enc::SP, local_slot_off(*i)));
                } else {
                    return Err(SelectError(format!(
                        "local.set {i}: writing a PARAMETER is not yet supported \
                         for aarch64 (params live in arg registers by reference; \
                         writing one could alias a stacked value) — loud-declining"
                    )));
                }
            }
            // `local.tee i` — like `local.set` but leaves the value on the stack.
            // Store the top value WITHOUT popping it (peek + `str`); a param
            // target is declined for the same reason as `local.set`.
            WasmOp::LocalTee(i) => {
                if *i >= num_params {
                    let top = *stack
                        .last()
                        .ok_or_else(|| SelectError("local.tee underflow".into()))?;
                    if top.file != File::Gp {
                        return Err(SelectError("local.tee: expected GP operand, got FP".into()));
                    }
                    words.push(enc::str_x_imm(top.reg, enc::SP, local_slot_off(*i)));
                } else {
                    return Err(SelectError(format!(
                        "local.tee {i}: writing a PARAMETER is not yet supported \
                         for aarch64 — loud-declining"
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
            WasmOp::Unreachable => words.push(enc::brk(0)),

            // --- control flow (#538 cf increment): VOID-result forward blocks ---
            //
            // `block` opens a new control frame. Only a `(0,0)` (void, no params,
            // no result) block is accepted — a typed block would leave a value on
            // the stack whose result register the branch would have to reconcile,
            // which this straight-line model does not do. The arity comes from the
            // decoder's ordinal side-table (`unreachable`-polymorphic fall-through
            // makes a stack-height proxy UNSOUND — the arity table is the signal).
            WasmOp::Block => {
                let ord = ctrl_ord;
                ctrl_ord += 1;
                let arity = block_arity.get(ord).copied().unwrap_or((0, 0));
                if arity != (0, 0) {
                    return Err(SelectError(format!(
                        "block #{ord} has type {arity:?} — only void (0,0) blocks \
                         are supported (value-carrying blocks need result-register \
                         reconciliation across the branch); loud-declining"
                    )));
                }
                ctrl.push(Frame {
                    pending: Vec::new(),
                    stack_entry: stack.len(),
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
                let pos = words.len();
                words.push(enc::b_uncond(0)); // placeholder; patched at End
                ctrl[target].pending.push(pos);
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
                let pos = words.len();
                words.push(enc::cbnz(cond, 0)); // placeholder; patched at End
                ctrl[target].pending.push(pos);
            }
            // `loop` (backward branch target), `if`/`else` (join reconciliation),
            // and `br_table` (jump table) are OUT of this increment — decline by
            // name rather than miscompile. (BrTable/If/Else hit the catch-all
            // `other` arm below; loop is explicit so its arity ordinal is
            // consumed with a clear message.)
            WasmOp::Loop => {
                // (no ctrl_ord bump needed: a decline aborts the whole compile,
                // so the arity-ordinal alignment is moot from here on.)
                return Err(SelectError(
                    "loop: backward-branch control flow not yet supported for \
                     aarch64 — loud-declining (only forward void blocks)"
                        .into(),
                ));
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

            // --- trapping float→int truncations (m4): domain-guarded #709 ---
            WasmOp::I32TruncF32S => trunc_guarded(&mut words, &mut stack, false, true)?,
            WasmOp::I32TruncF32U => trunc_guarded(&mut words, &mut stack, false, false)?,
            WasmOp::I32TruncF64S => trunc_guarded(&mut words, &mut stack, true, true)?,
            WasmOp::I32TruncF64U => trunc_guarded(&mut words, &mut stack, true, false)?,

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

            // --- bit-cast reinterprets (pure FMOV, no numeric change) ---
            WasmOp::F32ReinterpretI32 => {
                reinterpret_gp_to_fp(&mut words, &mut stack, enc::fmov_s_from_w)?
            }
            WasmOp::I32ReinterpretF32 => {
                reinterpret_fp_to_gp(&mut words, &mut stack, enc::fmov_w_from_s)?
            }

            // `End` is overloaded: it closes the innermost open `block`, or —
            // when no block is open — ends the FUNCTION body (funnel the result
            // into x0/d0 and return).
            WasmOp::End => {
                if let Some(frame) = ctrl.pop() {
                    // Block close: every recorded forward branch targets HERE
                    // (the block's fall-through). Patch each placeholder with the
                    // word-relative offset from the branch to the current position.
                    let here = words.len();
                    for pos in frame.pending {
                        let off = (here as i64 - pos as i64) as i32;
                        let branch = words[pos];
                        // Re-encode with the resolved offset, preserving the
                        // opcode/register bits set at emission (b vs cbnz).
                        words[pos] = if branch & 0xFF00_0000 == 0x1400_0000 {
                            enc::b_uncond(off)
                        } else {
                            // cbnz: keep the Rt field, set the imm19.
                            enc::cbnz((branch & 0x1F) as u8, off)
                        };
                    }
                    // A void block leaves the value stack exactly as on entry.
                    debug_assert!(
                        stack.len() == frame.stack_entry,
                        "void block must restore stack height: entry={} now={}",
                        frame.stack_entry,
                        stack.len()
                    );
                    stack.truncate(frame.stack_entry);
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
    Ok((words, call_sites))
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
        )
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

    #[test]
    fn call_to_import_loud_declines() {
        // func 0 is an import (num_imports = 1); calling it declines.
        let ops = vec![WasmOp::Call(0), WasmOp::End];
        assert!(sel_calls(&ops, 0, 1, &[0], &[0]).is_err());
    }

    #[test]
    fn non_leaf_referencing_param_loud_declines() {
        // A function that both reads a param AND makes a call declines (param
        // homing across a call is unsupported — reading x0 after bl is garbage).
        let ops = vec![WasmOp::LocalGet(0), WasmOp::Call(1), WasmOp::End];
        // func 1 takes 1 arg (the local.get 0 value).
        assert!(sel_calls(&ops, 1, 0, &[0, 1], &[0, 1]).is_err());
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
        );
        assert!(r.is_err(), "float-returning callee must loud-decline");
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

    #[test]
    fn division_is_loud_declined() {
        // A64 SDIV/UDIV do not trap → we refuse rather than silently miscompile.
        for op in [
            WasmOp::I32DivS,
            WasmOp::I32DivU,
            WasmOp::I32RemS,
            WasmOp::I32RemU,
            WasmOp::I64DivS,
            WasmOp::I64DivU,
        ] {
            let ops = vec![WasmOp::LocalGet(0), WasmOp::LocalGet(1), op, WasmOp::End];
            assert!(select(&ops, 2).is_err(), "division must loud-decline");
        }
    }

    #[test]
    fn popcnt_is_loud_declined() {
        let ops = vec![WasmOp::LocalGet(0), WasmOp::I32Popcnt, WasmOp::End];
        assert!(select(&ops, 1).is_err());
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
    fn rounding_and_i64_float_converts_are_loud_declined() {
        // The m4 honesty frontier: rounding ops and i64<->float conversions
        // stay DECLINED (never silent wrong code) until a later increment.
        for op in [
            WasmOp::F32Ceil,
            WasmOp::F32Floor,
            WasmOp::F32Trunc,
            WasmOp::F32Nearest,
            WasmOp::F64Ceil,
            WasmOp::F64Floor,
            WasmOp::F64Trunc,
            WasmOp::F64Nearest,
        ] {
            let ops = vec![WasmOp::LocalGet(0), op, WasmOp::End];
            assert!(
                select_typed(&ops, 1, &[true], &[true]).is_err(),
                "rounding ops not yet supported — must loud-decline"
            );
        }
        for op in [WasmOp::I64TruncF64S, WasmOp::I64TruncF64U] {
            let ops = vec![WasmOp::LocalGet(0), op, WasmOp::End];
            assert!(
                select_typed(&ops, 1, &[], &[true]).is_err(),
                "i64<->float conversions not yet supported — must loud-decline"
            );
        }
        for op in [WasmOp::F64ConvertI64S, WasmOp::F32ConvertI64U] {
            let ops = vec![WasmOp::LocalGet(0), op, WasmOp::End];
            assert!(
                select_typed(&ops, 1, &[], &[]).is_err(),
                "i64<->float conversions not yet supported — must loud-decline"
            );
        }
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

    #[test]
    fn typed_block_is_loud_declined() {
        // A value-carrying block (result i32) must decline — the straight-line
        // model can't reconcile the result register across the branch.
        let ops = vec![
            WasmOp::Block, // arity (0,1) → declined
            WasmOp::LocalGet(0),
            WasmOp::End,
            WasmOp::End,
        ];
        assert!(
            select_typed_cf(&ops, 1, &[], &[], &[(0, 1)]).is_err(),
            "typed (0,1) block must loud-decline"
        );
    }

    #[test]
    fn loop_and_br_table_and_if_are_loud_declined() {
        // Backward-branch / join / jump-table control is out of this increment.
        let loop_ops = vec![WasmOp::Loop, WasmOp::End, WasmOp::End];
        assert!(select_typed_cf(&loop_ops, 0, &[], &[], &[(0, 0)]).is_err());

        let brtable = vec![
            WasmOp::Block,
            WasmOp::LocalGet(0),
            WasmOp::BrTable {
                targets: vec![0],
                default: 0,
            },
            WasmOp::End,
            WasmOp::End,
        ];
        assert!(select_typed_cf(&brtable, 1, &[], &[], &[(0, 0)]).is_err());

        let if_ops = vec![WasmOp::LocalGet(0), WasmOp::If, WasmOp::End, WasmOp::End];
        assert!(select_typed_cf(&if_ops, 1, &[], &[], &[(0, 0)]).is_err());
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
