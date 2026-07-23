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
)
