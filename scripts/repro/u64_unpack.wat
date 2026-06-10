(module
  ;; #311 minimal: i64 unpack — mask/shift constants vs the live u64 pair.
  ;; Inlined form (loom did this): r = ((a+b+1) << 32) | 1; check action/val.
  (func (export "check") (param $a i32) (param $b i32) (result i32)
    (local $r i64)
    (local.set $r
      (i64.or
        (i64.shl
          (i64.extend_i32_u (i32.add (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
          (i64.const 32))
        (i64.const 1)))
    (select
      (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 32)))
      (i32.const 0xDEAD)
      (i32.eq
        (i32.wrap_i64 (i64.and (local.get $r) (i64.const 255)))
        (i32.const 1))))
  ;; post-call form: u64 returned in r0/r1, then unpacked.
  (func $make (param $a i32) (param $b i32) (result i64)
    (i64.or
      (i64.shl
        (i64.extend_i32_u (i32.add (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
        (i64.const 32))
      (i64.const 1)))
  (func (export "check_call") (param $a i32) (param $b i32) (result i32)
    (local $r i64)
    (local.set $r (call $make (local.get $a) (local.get $b)))
    (select
      (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 32)))
      (i32.const 0xDEAD)
      (i32.eq
        (i32.wrap_i64 (i64.and (local.get $r) (i64.const 255)))
        (i32.const 1)))))
