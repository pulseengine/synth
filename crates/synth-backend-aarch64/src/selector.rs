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
//! - memory, calls, control flow, non-param locals, spilling.
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

/// Lower a single function body with per-param type info. `params_f32[k]` /
/// `params_f64[k]` mark which params are float (delivered in V registers). The
/// integer path (empty masks) is byte-identical to the m2 behavior.
pub fn select_typed(
    ops: &[WasmOp],
    num_params: u32,
    params_f32: &[bool],
    params_f64: &[bool],
) -> Result<Vec<u32>, SelectError> {
    if num_params > 8 {
        return Err(SelectError(format!(
            "{num_params} params — supports at most 8 register params"
        )));
    }
    let params = param_map(num_params, params_f32, params_f64);
    let mut words: Vec<u32> = Vec::new();
    let mut stack: Vec<Val> = Vec::new();

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

    for op in ops {
        match op {
            WasmOp::LocalGet(i) => {
                if *i >= num_params {
                    return Err(SelectError(format!(
                        "local.get {i}: non-param locals not yet supported"
                    )));
                }
                // Resolve the param to its AAPCS64 register + file (GP or FP).
                stack.push(params[*i as usize]);
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

            // End of the function body: funnel the result into x0/d0 and return.
            WasmOp::End => {
                epilogue(&mut words, stack.last().copied());
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
        epilogue(&mut words, stack.last().copied());
    }
    Ok(words)
}

/// Emit the function epilogue: move the top-of-stack result into the ABI return
/// register (`x0` for a GP result, `d0` for a float result) and `ret`. A GP
/// result already in `x0` / an FP result already in `v0` skips the move. The
/// 64-bit `mov x0, xN` is correct for i32 results too (w-form producers zero the
/// upper half); the `fmov d0, dN` likewise carries an f32's low 32 bits intact.
fn epilogue(words: &mut Vec<u32>, top: Option<Val>) {
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
    words.push(enc::ret());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
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
}
