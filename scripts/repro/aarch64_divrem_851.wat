(module
  ;; #851 — aarch64 integer div/rem lowering (SDIV/UDIV + MSUB) with the WASM
  ;; trap guards. Exercised by aarch64_divrem_851_differential.py against
  ;; wasmtime (value + trap), executed natively (SIGTRAP) and under unicorn.
  (func (export "i32_div_s") (param i32 i32) (result i32)
    (i32.div_s (local.get 0) (local.get 1)))
  (func (export "i32_div_u") (param i32 i32) (result i32)
    (i32.div_u (local.get 0) (local.get 1)))
  (func (export "i32_rem_s") (param i32 i32) (result i32)
    (i32.rem_s (local.get 0) (local.get 1)))
  (func (export "i32_rem_u") (param i32 i32) (result i32)
    (i32.rem_u (local.get 0) (local.get 1)))
  (func (export "i64_div_s") (param i64 i64) (result i64)
    (i64.div_s (local.get 0) (local.get 1)))
  (func (export "i64_div_u") (param i64 i64) (result i64)
    (i64.div_u (local.get 0) (local.get 1)))
  (func (export "i64_rem_s") (param i64 i64) (result i64)
    (i64.rem_s (local.get 0) (local.get 1)))
  (func (export "i64_rem_u") (param i64 i64) (result i64)
    (i64.rem_u (local.get 0) (local.get 1)))
  ;; popcnt (SIMD CNT/ADDV) — i32 zero-fills upper lanes, i64 fills all 8.
  (func (export "i32_popcnt") (param i32) (result i32)
    (i32.popcnt (local.get 0)))
  (func (export "i64_popcnt") (param i64) (result i64)
    (i64.popcnt (local.get 0)))
  ;; f64<->i64 reinterpret round-trips (bit-preserving fmov) — a full round
  ;; trip is the identity, so f(x) must equal the input bits for every x.
  (func (export "i64_reinterpret_rt") (param i64) (result i64)
    (i64.reinterpret_f64 (f64.reinterpret_i64 (local.get 0))))
)
