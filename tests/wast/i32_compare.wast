;; Comparison tests for Synth
;; Tests integer comparison operations

(module
  ;; Equal
  (func (export "eq") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.eq)

  ;; Not equal
  (func (export "ne") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.ne)

  ;; Less than (signed)
  (func (export "lt_s") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.lt_s)

  ;; Less than (unsigned)
  (func (export "lt_u") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.lt_u)

  ;; Greater than (signed)
  (func (export "gt_s") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.gt_s)

  ;; Greater than (unsigned)
  (func (export "gt_u") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.gt_u)

  ;; Equal to zero
  (func (export "eqz") (param i32) (result i32)
    local.get 0
    i32.eqz)
)

;; Equality tests
(assert_return (invoke "eq" (i32.const 5) (i32.const 5)) (i32.const 1))
(assert_return (invoke "eq" (i32.const 5) (i32.const 3)) (i32.const 0))
(assert_return (invoke "ne" (i32.const 5) (i32.const 3)) (i32.const 1))
(assert_return (invoke "ne" (i32.const 5) (i32.const 5)) (i32.const 0))

;; Less than tests
(assert_return (invoke "lt_s" (i32.const 3) (i32.const 5)) (i32.const 1))
(assert_return (invoke "lt_s" (i32.const 5) (i32.const 3)) (i32.const 0))
(assert_return (invoke "lt_s" (i32.const -1) (i32.const 1)) (i32.const 1))
(assert_return (invoke "lt_u" (i32.const 3) (i32.const 5)) (i32.const 1))

;; Greater than tests
(assert_return (invoke "gt_s" (i32.const 5) (i32.const 3)) (i32.const 1))
(assert_return (invoke "gt_s" (i32.const 3) (i32.const 5)) (i32.const 0))
(assert_return (invoke "gt_u" (i32.const 5) (i32.const 3)) (i32.const 1))

;; Equal to zero tests
(assert_return (invoke "eqz" (i32.const 0)) (i32.const 1))
(assert_return (invoke "eqz" (i32.const 1)) (i32.const 0))
(assert_return (invoke "eqz" (i32.const -1)) (i32.const 0))
