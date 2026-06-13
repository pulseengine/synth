(module
  ;; #313 minimal: the if-with-result analogue of u64_unpack.wat.
  ;; Same payload (r = ((a+b+1) << 32) | 1) but the unpack uses an
  ;; `(if (result i32) …)` with ASYMMETRIC arms instead of `select`.
  ;; The buggy ARM selector tracked the operand stack textually through
  ;; both arms with no checkpoint/reconciliation, so `End`/return read the
  ;; ELSE-arm's register unconditionally — the then-path returned garbage.
  ;; check_call(3,4) must be 8 (then-arm: r>>32 = a+b+1); was 0xDEAD/garbage.
  (func (export "check") (param $a i32) (param $b i32) (result i32)
    (local $r i64)
    (local.set $r
      (i64.or
        (i64.shl
          (i64.extend_i32_u (i32.add (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
          (i64.const 32))
        (i64.const 1)))
    (if (result i32)
      (i32.eq
        (i32.wrap_i64 (i64.and (local.get $r) (i64.const 255)))
        (i32.const 1))
      (then (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 32))))
      (else (i32.const 0xDEAD))))
  ;; post-call form: u64 returned in r0/r1, then unpacked through an if.
  (func $make (param $a i32) (param $b i32) (result i64)
    (i64.or
      (i64.shl
        (i64.extend_i32_u (i32.add (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
        (i64.const 32))
      (i64.const 1)))
  (func (export "check_call") (param $a i32) (param $b i32) (result i32)
    (local $r i64)
    (local.set $r (call $make (local.get $a) (local.get $b)))
    (if (result i32)
      (i32.eq
        (i32.wrap_i64 (i64.and (local.get $r) (i64.const 255)))
        (i32.const 1))
      (then (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 32))))
      (else (i32.const 0xDEAD))))
  (func $make_hot (param $a i32) (param $b i32) (result i64)
    ;; enough live i32 values to push the if-result destinations into high regs
    (local $t1 i32) (local $t2 i32) (local $t3 i32)
    (local.set $t1 (i32.add (local.get $a) (i32.const 3)))
    (local.set $t2 (i32.mul (local.get $b) (i32.const 5)))
    (local.set $t3 (i32.xor (local.get $t1) (local.get $t2)))
    (i64.or
      (i64.shl
        (i64.extend_i32_u
          (i32.add (i32.add (local.get $a) (local.get $b))
                   (i32.and (local.get $t3) (i32.const 0))))
        (i64.const 32))
      (i64.extend_i32_u (i32.add (i32.const 1) (i32.and (local.get $t3) (i32.const 0))))))
  (func (export "check_hot") (param $a i32) (param $b i32) (result i32)
    (local $r i64)
    (local.set $r (call $make_hot (local.get $a) (local.get $b)))
    (if (result i32)
      (i32.eq
        (i32.wrap_i64 (i64.and (local.get $r) (i64.const 255)))
        (i32.const 1))
      (then (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 32))))
      (else (i32.const 0xDEAD))))
  ;; #313 reservation stress: the else-arm builds a DEEP expression with many
  ;; simultaneously-live i32 temps, driving the round-robin temp allocator
  ;; toward the THEN-arm's result register. The then-arm result (r>>32) must
  ;; stay protected across the whole else-arm — if the reservation threading is
  ;; incomplete, the else-arm clobbers the then register, reconcile sees
  ;; then==else (no mov), and the then-path silently returns the else value.
  ;; cond is true when (r & 255) == 1 (it is, by construction), so the then-arm
  ;; runs and MUST return a+b+1; a wrong reservation makes it return garbage.
  (func (export "check_press") (param $a i32) (param $b i32) (result i32)
    (local $r i64)
    (local.set $r
      (i64.or
        (i64.shl
          (i64.extend_i32_u (i32.add (i32.add (local.get $a) (local.get $b)) (i32.const 1)))
          (i64.const 32))
        (i64.const 1)))
    (if (result i32)
      (i32.eq
        (i32.wrap_i64 (i64.and (local.get $r) (i64.const 255)))
        (i32.const 1))
      (then (i32.wrap_i64 (i64.shr_u (local.get $r) (i64.const 32))))
      ;; else: a 7-deep live chain of distinct sub-sums (never reached when the
      ;; cond is true, but its register demand must NOT touch the then result).
      (else
        (i32.add
          (i32.add
            (i32.add (i32.add (local.get $a) (i32.const 11))
                     (i32.add (local.get $b) (i32.const 22)))
            (i32.add (i32.add (local.get $a) (i32.const 33))
                     (i32.add (local.get $b) (i32.const 44))))
          (i32.add
            (i32.add (i32.add (local.get $a) (i32.const 55))
                     (i32.add (local.get $b) (i32.const 66)))
            (i32.add (local.get $a) (local.get $b))))))))
