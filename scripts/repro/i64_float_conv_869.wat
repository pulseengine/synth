;; #869 — gale's self-contained repro: the ARM 64-bit integer<->float
;; conversion family. RED before the fix: the six i64<->float exports are
;; skipped (absent from `nm`); the four i32 rows lower and prove the 32-bit
;; family was never the gap. GREEN after: all ten exports reach `nm` -> T on
;; cortex-m7dp.
(module
  (func (export "i64u_to_f32")   (param i64) (result f32) local.get 0 f32.convert_i64_u)
  (func (export "i64s_to_f32")   (param i64) (result f32) local.get 0 f32.convert_i64_s)
  (func (export "i64u_to_f64")   (param i64) (result f64) local.get 0 f64.convert_i64_u)
  (func (export "i64s_to_f64")   (param i64) (result f64) local.get 0 f64.convert_i64_s)
  (func (export "f32_to_i64s")   (param f32) (result i64) local.get 0 i64.trunc_f32_s)
  (func (export "f32_to_i64u")   (param f32) (result i64) local.get 0 i64.trunc_f32_u)
  ;; #756 completeness rows — the f64-source trunc twins.
  (func (export "f64_to_i64s")   (param f64) (result i64) local.get 0 i64.trunc_f64_s)
  (func (export "f64_to_i64u")   (param f64) (result i64) local.get 0 i64.trunc_f64_u)
  (func (export "i32u_to_f32")   (param i32) (result f32) local.get 0 f32.convert_i32_u)
  (func (export "i32s_to_f32")   (param i32) (result f32) local.get 0 f32.convert_i32_s)
  (func (export "f32_to_i32s")   (param f32) (result i32) local.get 0 i32.trunc_f32_s)
  (func (export "wrap_then_i32u")(param i64) (result f32) local.get 0 i32.wrap_i64 f32.convert_i32_u))
