(module
  ;; #633: i64.div_s(INT64_MIN, -1) must trap (WASM Core 4.3.2 idiv_s —
  ;; +2^63 is unrepresentable). The i64 signed-div expansion emitted only
  ;; the divide-by-zero guard, negated INT64_MIN onto itself, and returned
  ;; INT64_MIN silently. Dividend assembled from two u32 halves (lo, hi),
  ;; divisor the constant -1 — the issue's exact shape.
  (func (export "div_s_m1") (param i32 i32) (result i32)
    (i32.wrap_i64
      (i64.div_s
        (i64.or (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32))
                (i64.extend_i32_u (local.get 0)))
        (i64.const -1))))
  ;; Fix-guard twin (#633): rem_s(INT64_MIN, -1) is DEFINED as 0 and must
  ;; NOT trap — the overflow guard belongs to div_s only.
  (func (export "rem_s_m1") (param i32 i32) (result i32)
    (i32.wrap_i64
      (i64.rem_s
        (i64.or (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32))
                (i64.extend_i32_u (local.get 0)))
        (i64.const -1))))
  ;; General two-i64-param forms (both operands runtime values).
  (func (export "div_s") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.div_s (local.get 0) (local.get 1))))
  (func (export "rem_s") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.rem_s (local.get 0) (local.get 1))))
  ;; hi-word twin so both halves of the quotient are checked through the
  ;; i32 return register.
  (func (export "div_s_hi") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (i64.div_s (local.get 0) (local.get 1))
                             (i64.const 32)))))
