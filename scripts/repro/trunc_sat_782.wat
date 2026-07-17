;; #782a — the nontrapping saturating float->int truncation acceptance module
;; (WASM saturating-float-to-int proposal, 0xFC prefix, Core §4.3.2 trunc_sat).
;;
;; Semantics under test (TOTAL — never traps):
;;   NaN -> 0; x < INT_MIN -> INT_MIN; x > INT_MAX -> INT_MAX (for _u:
;;   negatives -> 0, above UINT_MAX -> UINT_MAX); else truncate toward zero.
;;
;; The i32-target quartet is what falcon-flight-v1.123 carries (7x
;; i32.trunc_sat_f64_s + 1x i32.trunc_sat_f32_s, #782) — Rust emits trunc_sat
;; for `as` casts. The i64-target quartet lowers on aarch64 only (A64 is
;; 64-bit native); 32-bit ARM LOUD-declines it (see trunc_sat_782_decline in
;; the differential).
;;
;; The differential (trunc_sat_782_differential.py) executes each export under
;; unicorn (Thumb-2 cortex-m7dp AND aarch64) and natively on an arm64 host,
;; diffing wasmtime ground truth over the full boundary table: NaN, ±inf, the
;; exact INT_MIN/INT_MAX boundaries, ±0.5 fractions, and in-range values. NO
;; case may trap anywhere — a UDF/brk stop is a failure by construction.
(module
  ;; ---- i32-target trunc_sat (the falcon quartet) ----
  (func (export "i32_trunc_sat_f32_s") (param f32) (result i32)
    (i32.trunc_sat_f32_s (local.get 0)))
  (func (export "i32_trunc_sat_f32_u") (param f32) (result i32)
    (i32.trunc_sat_f32_u (local.get 0)))
  (func (export "i32_trunc_sat_f64_s") (param f64) (result i32)
    (i32.trunc_sat_f64_s (local.get 0)))
  (func (export "i32_trunc_sat_f64_u") (param f64) (result i32)
    (i32.trunc_sat_f64_u (local.get 0)))

  ;; ---- i64-target trunc_sat (aarch64-only; ARM32 loud-declines) ----
  (func (export "i64_trunc_sat_f32_s") (param f32) (result i64)
    (i64.trunc_sat_f32_s (local.get 0)))
  (func (export "i64_trunc_sat_f32_u") (param f32) (result i64)
    (i64.trunc_sat_f32_u (local.get 0)))
  (func (export "i64_trunc_sat_f64_s") (param f64) (result i64)
    (i64.trunc_sat_f64_s (local.get 0)))
  (func (export "i64_trunc_sat_f64_u") (param f64) (result i64)
    (i64.trunc_sat_f64_u (local.get 0))))
