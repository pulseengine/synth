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
//! - floats, memory, calls, control flow, non-param locals, spilling.

use crate::encoder as enc;
use crate::encoder::{Cond, Reg};
use synth_core::WasmOp;

/// The value-stack temp registers: caller-saved `w9/x9..w15/x15` (7 slots).
/// `w0..w7` hold incoming params; results funnel back through `x0`.
const TEMPS: [Reg; 7] = [9, 10, 11, 12, 13, 14, 15];

#[derive(Debug)]
pub struct SelectError(pub String);

impl std::fmt::Display for SelectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "aarch64 selector: {}", self.0)
    }
}

/// Lower a single function body (its wasm op stream + declared param count) to a
/// vector of A64 instruction words. `num_params` params are assumed resident in
/// `w0/x0..w7/x7` on entry (up to 8 register params).
pub fn select(ops: &[WasmOp], num_params: u32) -> Result<Vec<u32>, SelectError> {
    if num_params > 8 {
        return Err(SelectError(format!(
            "{num_params} params — supports at most 8 register params"
        )));
    }
    let mut words: Vec<u32> = Vec::new();
    let mut stack: Vec<Reg> = Vec::new();

    // Pick a temp register not currently holding a live value-stack entry.
    let alloc_temp = |stack: &[Reg]| -> Result<Reg, SelectError> {
        TEMPS
            .iter()
            .copied()
            .find(|t| !stack.contains(t))
            .ok_or_else(|| SelectError("value-stack too deep (temp regs exhausted)".into()))
    };

    // A binary `dst = a OP b` where `f` is the width-specialized encoder fn.
    let binop = |words: &mut Vec<u32>,
                 stack: &mut Vec<Reg>,
                 f: fn(Reg, Reg, Reg) -> u32|
     -> Result<(), SelectError> {
        let b = stack
            .pop()
            .ok_or_else(|| SelectError("binop underflow".into()))?;
        let a = stack
            .pop()
            .ok_or_else(|| SelectError("binop underflow".into()))?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a, b));
        stack.push(dst);
        Ok(())
    };

    // A unary `dst = OP a`.
    let unop = |words: &mut Vec<u32>,
                stack: &mut Vec<Reg>,
                f: fn(Reg, Reg) -> u32|
     -> Result<(), SelectError> {
        let a = stack
            .pop()
            .ok_or_else(|| SelectError("unop underflow".into()))?;
        let dst = alloc_temp(stack)?;
        words.push(f(dst, a));
        stack.push(dst);
        Ok(())
    };

    // `ctz` = `rbit` then `clz` (A64 has no direct CTZ). `sf` selects width.
    let ctz = |words: &mut Vec<u32>, stack: &mut Vec<Reg>, sf: bool| -> Result<(), SelectError> {
        let a = stack
            .pop()
            .ok_or_else(|| SelectError("ctz underflow".into()))?;
        let dst = alloc_temp(stack)?;
        if sf {
            words.push(enc::rbit64(dst, a));
            words.push(enc::clz64(dst, dst));
        } else {
            words.push(enc::rbit(dst, a));
            words.push(enc::clz(dst, dst));
        }
        stack.push(dst);
        Ok(())
    };

    // `rotl rd, rn, rk` = `neg rtmp, rk; rorv rd, rn, rtmp` (mod-width neg gives
    // the equivalent right-rotate; correct including k=0 → neg 0 = 0).
    let rotl = |words: &mut Vec<u32>, stack: &mut Vec<Reg>, sf: bool| -> Result<(), SelectError> {
        let k = stack
            .pop()
            .ok_or_else(|| SelectError("rotl underflow".into()))?;
        let n = stack
            .pop()
            .ok_or_else(|| SelectError("rotl underflow".into()))?;
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
        stack.push(dst);
        Ok(())
    };

    // A comparison `dst = (a CMP b)` as `cmp` + `cset cond`. `sf` selects width.
    let cmp_op = |words: &mut Vec<u32>,
                  stack: &mut Vec<Reg>,
                  sf: bool,
                  cond: Cond|
     -> Result<(), SelectError> {
        let b = stack
            .pop()
            .ok_or_else(|| SelectError("compare underflow".into()))?;
        let a = stack
            .pop()
            .ok_or_else(|| SelectError("compare underflow".into()))?;
        let dst = alloc_temp(stack)?;
        words.push(if sf { enc::cmp64(a, b) } else { enc::cmp(a, b) });
        words.push(enc::cset(dst, cond));
        stack.push(dst);
        Ok(())
    };

    // `eqz`: `dst = (a == 0)` as `cmp a, zr` + `cset eq`.
    let eqz = |words: &mut Vec<u32>, stack: &mut Vec<Reg>, sf: bool| -> Result<(), SelectError> {
        let a = stack
            .pop()
            .ok_or_else(|| SelectError("eqz underflow".into()))?;
        let dst = alloc_temp(stack)?;
        words.push(if sf {
            enc::cmp64(a, enc::XZR)
        } else {
            enc::cmp(a, enc::WZR)
        });
        words.push(enc::cset(dst, Cond::Eq));
        stack.push(dst);
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
                // params are in w0/x0..w7/x7 — same architectural number.
                stack.push(*i as Reg);
            }
            WasmOp::I32Const(c) => {
                let dst = alloc_temp(&stack)?;
                for w in enc::mov_imm32(dst, *c as u32) {
                    words.push(w);
                }
                stack.push(dst);
            }
            WasmOp::I64Const(c) => {
                let dst = alloc_temp(&stack)?;
                for w in enc::mov_imm64(dst, *c as u64) {
                    words.push(w);
                }
                stack.push(dst);
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

            // End of the function body: move the result to x0 and return. The
            // 64-bit `mov x0, xN` is correct for i32 results too — every w-form
            // producer zeroes the upper half, so `w0` still reads the right
            // low 32 bits.
            WasmOp::End => {
                if let Some(top) = stack.last().copied()
                    && top != 0
                {
                    words.push(enc::mov_reg64(0, top));
                }
                words.push(enc::ret());
            }
            other => {
                return Err(SelectError(format!(
                    "unsupported wasm op for aarch64 integer subset: {other:?}"
                )));
            }
        }
    }

    // A body without a trailing `End` still needs an epilogue.
    if !matches!(ops.last(), Some(WasmOp::End)) {
        if let Some(top) = stack.last().copied()
            && top != 0
        {
            words.push(enc::mov_reg64(0, top));
        }
        words.push(enc::ret());
    }
    Ok(words)
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
}
