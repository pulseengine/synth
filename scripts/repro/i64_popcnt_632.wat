(module
  ;; #632: assemble a u64 from two u32 halves, popcnt, wrap. The i64.or/shl/
  ;; extend construction adds enough register pressure that the allocator
  ;; hands the I64Popcnt expansion a result register (rd) inside its own
  ;; scratch set {R3,R4,R5} — the expansion's restore `POP {R3,R4,R5}`
  ;; then clobbered the freshly computed count (0 for every input on qemu).
  (func (export "popcnt64") (param i32 i32) (result i32)
    (i32.wrap_i64
      (i64.popcnt
        (i64.or
          (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32))
          (i64.extend_i32_u (local.get 0))))))
  ;; Direct form — control, correct before the fix (rd landed outside
  ;; the expansion's scratch set).
  (func (export "popcnt_direct") (param i64) (result i32)
    (i32.wrap_i64 (i64.popcnt (local.get 0))))
  ;; hi-word probe: the count is an i64 (lo = count, hi = 0); shift the pair
  ;; right 32 so the wrapped result exposes the HI word of the popcnt pair.
  (func (export "popcnt64_hi") (param i32 i32) (result i32)
    (i32.wrap_i64
      (i64.shr_u
        (i64.popcnt
          (i64.or
            (i64.shl (i64.extend_i32_u (local.get 1)) (i64.const 32))
            (i64.extend_i32_u (local.get 0))))
        (i64.const 32)))))
