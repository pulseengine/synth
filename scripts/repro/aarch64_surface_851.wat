(module
  ;; #851 v0.53 op-surface differential module. Memory pinned min=max so
  ;; memory.grow(n>0) MUST fail (-1) in wasmtime too — bit-identical to the
  ;; aarch64 fixed-buffer lowering (growth failure is spec-permitted; pinning
  ;; max makes it spec-forced, so the differential asserts real parity).
  (memory 2 2)

  ;; select — all four value types, condition as a runtime param so both arms
  ;; are exercised by the case list.
  (func (export "sel32") (param i32 i32 i32) (result i32)
    (select (local.get 0) (local.get 1) (local.get 2)))
  (func (export "sel64") (param i64 i64 i32) (result i64)
    (select (local.get 0) (local.get 1) (local.get 2)))
  (func (export "self32") (param f32 f32 i32) (result f32)
    (select (local.get 0) (local.get 1) (local.get 2)))
  (func (export "self64") (param f64 f64 i32) (result f64)
    (select (local.get 0) (local.get 1) (local.get 2)))

  ;; width conversions / in-place sign extensions
  (func (export "wrap") (param i64) (result i32) (i32.wrap_i64 (local.get 0)))
  (func (export "ext32s") (param i32) (result i64) (i64.extend_i32_s (local.get 0)))
  (func (export "ext32u") (param i32) (result i64) (i64.extend_i32_u (local.get 0)))
  (func (export "e8") (param i32) (result i32) (i32.extend8_s (local.get 0)))
  (func (export "e16") (param i32) (result i32) (i32.extend16_s (local.get 0)))
  (func (export "e648") (param i64) (result i64) (i64.extend8_s (local.get 0)))
  (func (export "e6416") (param i64) (result i64) (i64.extend16_s (local.get 0)))
  (func (export "e6432") (param i64) (result i64) (i64.extend32_s (local.get 0)))

  ;; nop + drop (no code / stack bookkeeping only)
  (func (export "dn") (param i32) (result i32)
    (nop) (drop (i32.const 9)) (i32.add (local.get 0) (i32.const 1)))

  ;; fixed-memory memory.size / memory.grow (grow(0) == size; grow(n>0) == -1)
  (func (export "msize") (result i32) (memory.size))
  (func (export "mgrow") (param i32) (result i32) (memory.grow (local.get 0)))
  ;; grow-then-size on one instance: a failed grow must NOT change the size.
  (func (export "growsize") (param i32) (result i32)
    (drop (memory.grow (local.get 0)))
    (memory.size))
)
