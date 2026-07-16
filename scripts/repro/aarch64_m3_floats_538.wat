;; #538 milestone-3 — the aarch64 scalar-FLOAT acceptance module.
;; Every export is a leaf float function the m3 A64 selector lowers: f32/f64
;; add/sub/mul/div, abs/neg/sqrt, the full compare family (eq/ne/lt/le/gt/ge),
;; the f32<->f64 promote/demote conversions, the i32->float conversions
;; (convert_i32_s/u), and the f32<->i32 reinterprets. Params that are float
;; arrive in V registers (s0.. / d0..) under AAPCS64 — an INDEPENDENT counter
;; from the GP arg registers — which the file-tagged value stack tracks.
;;
;; The differential (aarch64_m3_floats_538_differential.py) runs each under
;; unicorn UC_ARCH_ARM64 (FPEN enabled) AND natively on the arm64 host, and
;; diffs wasmtime ground truth — including NaN inputs (the compare NaN-ordering
;; and the sign-of-NaN / ±0 edge cases).
;;
;; NOTE: the TRAPPING float->int truncations (i32.trunc_f32_s/_u, i32.trunc_f64_*)
;; are deliberately ABSENT — A64 FCVTZS/FCVTZU SATURATE where WASM traps (#709),
;; so the m3 selector loud-declines them (asserted in the unit tests + decline
;; matrix). min/max/copysign/rounding are likewise declined.
(module
  ;; ---- f32 arithmetic ----
  (func (export "f32_add") (param f32 f32) (result f32)
    (f32.add (local.get 0) (local.get 1)))
  (func (export "f32_sub") (param f32 f32) (result f32)
    (f32.sub (local.get 0) (local.get 1)))
  (func (export "f32_mul") (param f32 f32) (result f32)
    (f32.mul (local.get 0) (local.get 1)))
  (func (export "f32_div") (param f32 f32) (result f32)
    (f32.div (local.get 0) (local.get 1)))
  (func (export "f32_abs") (param f32) (result f32)
    (f32.abs (local.get 0)))
  (func (export "f32_neg") (param f32) (result f32)
    (f32.neg (local.get 0)))

  ;; ---- f32 comparisons (result i32) ----
  (func (export "f32_eq") (param f32 f32) (result i32)
    (f32.eq (local.get 0) (local.get 1)))
  (func (export "f32_ne") (param f32 f32) (result i32)
    (f32.ne (local.get 0) (local.get 1)))
  (func (export "f32_lt") (param f32 f32) (result i32)
    (f32.lt (local.get 0) (local.get 1)))
  (func (export "f32_le") (param f32 f32) (result i32)
    (f32.le (local.get 0) (local.get 1)))
  (func (export "f32_gt") (param f32 f32) (result i32)
    (f32.gt (local.get 0) (local.get 1)))
  (func (export "f32_ge") (param f32 f32) (result i32)
    (f32.ge (local.get 0) (local.get 1)))

  ;; ---- f64 arithmetic ----
  (func (export "f64_add") (param f64 f64) (result f64)
    (f64.add (local.get 0) (local.get 1)))
  (func (export "f64_sub") (param f64 f64) (result f64)
    (f64.sub (local.get 0) (local.get 1)))
  (func (export "f64_mul") (param f64 f64) (result f64)
    (f64.mul (local.get 0) (local.get 1)))
  (func (export "f64_div") (param f64 f64) (result f64)
    (f64.div (local.get 0) (local.get 1)))
  (func (export "f64_abs") (param f64) (result f64)
    (f64.abs (local.get 0)))
  (func (export "f64_neg") (param f64) (result f64)
    (f64.neg (local.get 0)))
  (func (export "f64_sqrt") (param f64) (result f64)
    (f64.sqrt (local.get 0)))

  ;; ---- f64 comparisons (result i32) ----
  (func (export "f64_eq") (param f64 f64) (result i32)
    (f64.eq (local.get 0) (local.get 1)))
  (func (export "f64_ne") (param f64 f64) (result i32)
    (f64.ne (local.get 0) (local.get 1)))
  (func (export "f64_lt") (param f64 f64) (result i32)
    (f64.lt (local.get 0) (local.get 1)))
  (func (export "f64_le") (param f64 f64) (result i32)
    (f64.le (local.get 0) (local.get 1)))
  (func (export "f64_gt") (param f64 f64) (result i32)
    (f64.gt (local.get 0) (local.get 1)))
  (func (export "f64_ge") (param f64 f64) (result i32)
    (f64.ge (local.get 0) (local.get 1)))

  ;; ---- precision conversions ----
  (func (export "f64_promote_f32") (param f32) (result f64)
    (f64.promote_f32 (local.get 0)))
  (func (export "f32_demote_f64") (param f64) (result f32)
    (f32.demote_f64 (local.get 0)))

  ;; ---- int -> float conversions ----
  (func (export "f32_convert_i32_s") (param i32) (result f32)
    (f32.convert_i32_s (local.get 0)))
  (func (export "f32_convert_i32_u") (param i32) (result f32)
    (f32.convert_i32_u (local.get 0)))
  (func (export "f64_convert_i32_s") (param i32) (result f64)
    (f64.convert_i32_s (local.get 0)))
  (func (export "f64_convert_i32_u") (param i32) (result f64)
    (f64.convert_i32_u (local.get 0)))

  ;; ---- reinterprets (bit-casts) ----
  (func (export "f32_reinterpret_i32") (param i32) (result f32)
    (f32.reinterpret_i32 (local.get 0)))
  (func (export "i32_reinterpret_f32") (param f32) (result i32)
    (i32.reinterpret_f32 (local.get 0)))

  ;; ---- mixed int/float param register assignment (AAPCS64) ----
  ;; (param i32 f32 i32) → w0, s0, w1. Return the f32 param negated to prove
  ;; the f32 resolves to s0 (not a GP register).
  (func (export "mixed_params") (param i32 f32 i32) (result f32)
    (f32.neg (local.get 1))))
