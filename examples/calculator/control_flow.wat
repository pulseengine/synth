;; Control flow tests - if/else, loop, block, br
(module
  ;; max(a, b) using if/else
  (func (export "max") (param $a i32) (param $b i32) (result i32)
    (if (result i32) (i32.gt_s (local.get $a) (local.get $b))
      (then (local.get $a))
      (else (local.get $b))
    )
  )

  ;; abs(x) using if/else
  (func (export "abs") (param $x i32) (result i32)
    (if (result i32) (i32.lt_s (local.get $x) (i32.const 0))
      (then (i32.sub (i32.const 0) (local.get $x)))
      (else (local.get $x))
    )
  )

  ;; is_zero(x) using select
  (func (export "is_zero") (param $x i32) (result i32)
    (select
      (i32.const 0)
      (i32.const 1)
      (local.get $x)
    )
  )

  ;; negate(x)
  (func (export "negate") (param $x i32) (result i32)
    i32.const 0
    local.get $x
    i32.sub
  )
)
