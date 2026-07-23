(module
  (memory 1)

  ;; --- i32 round-trips: store the value at [addr], read it back. The result
  ;; is the loaded value, so a correct store+load returns the input verbatim
  ;; (sub-word forms truncate/extend, exercising the ldr*/str* width + sign). ---
  (func (export "rt_i32") (param i32 i32) (result i32)
    (i32.store (local.get 0) (local.get 1))
    (i32.load (local.get 0)))

  (func (export "rt_i32_off") (param i32 i32) (result i32)
    (i32.store offset=8 (local.get 0) (local.get 1))
    (i32.load offset=8 (local.get 0)))

  ;; A large offset that does NOT fit the scaled imm12 (word: 4096*4 = 16384)
  ;; — forces the materialize-and-add address path in form_ea.
  (func (export "rt_i32_bigoff") (param i32 i32) (result i32)
    (i32.store offset=20000 (local.get 0) (local.get 1))
    (i32.load offset=20000 (local.get 0)))

  (func (export "rt_i32_8u") (param i32 i32) (result i32)
    (i32.store8 (local.get 0) (local.get 1))
    (i32.load8_u (local.get 0)))

  (func (export "rt_i32_8s") (param i32 i32) (result i32)
    (i32.store8 (local.get 0) (local.get 1))
    (i32.load8_s (local.get 0)))

  (func (export "rt_i32_16u") (param i32 i32) (result i32)
    (i32.store16 (local.get 0) (local.get 1))
    (i32.load16_u (local.get 0)))

  (func (export "rt_i32_16s") (param i32 i32) (result i32)
    (i32.store16 (local.get 0) (local.get 1))
    (i32.load16_s (local.get 0)))

  ;; --- i64 round-trips ---
  (func (export "rt_i64") (param i32 i64) (result i64)
    (i64.store (local.get 0) (local.get 1))
    (i64.load (local.get 0)))

  (func (export "rt_i64_8u") (param i32 i64) (result i64)
    (i64.store8 (local.get 0) (local.get 1))
    (i64.load8_u (local.get 0)))

  (func (export "rt_i64_8s") (param i32 i64) (result i64)
    (i64.store8 (local.get 0) (local.get 1))
    (i64.load8_s (local.get 0)))

  (func (export "rt_i64_16u") (param i32 i64) (result i64)
    (i64.store16 (local.get 0) (local.get 1))
    (i64.load16_u (local.get 0)))

  (func (export "rt_i64_16s") (param i32 i64) (result i64)
    (i64.store16 (local.get 0) (local.get 1))
    (i64.load16_s (local.get 0)))

  (func (export "rt_i64_32u") (param i32 i64) (result i64)
    (i64.store32 (local.get 0) (local.get 1))
    (i64.load32_u (local.get 0)))

  (func (export "rt_i64_32s") (param i32 i64) (result i64)
    (i64.store32 (local.get 0) (local.get 1))
    (i64.load32_s (local.get 0)))

  ;; --- cross-function sharing via the shared x28 base: `wr` stores to a fixed
  ;; address, `rd` reads it. Proves the dedicated-base convention (not sp-scratch)
  ;; — two separate functions agree on the same linear-memory location. ---
  (func (export "wr") (param i32)
    (i32.store offset=64 (i32.const 0) (local.get 0)))
  (func (export "rd") (result i32)
    (i32.load offset=64 (i32.const 0)))
)
