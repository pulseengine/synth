;; Division and trap tests for Synth
;; Tests integer division and division by zero traps

(module
  ;; Signed division
  (func (export "div_s") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.div_s)

  ;; Unsigned division
  (func (export "div_u") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.div_u)
)

;; Normal division tests
(assert_return (invoke "div_s" (i32.const 10) (i32.const 2)) (i32.const 5))
(assert_return (invoke "div_s" (i32.const 10) (i32.const 3)) (i32.const 3))
(assert_return (invoke "div_s" (i32.const -10) (i32.const 2)) (i32.const -5))
(assert_return (invoke "div_u" (i32.const 10) (i32.const 2)) (i32.const 5))

;; Division by zero trap tests
(assert_trap (invoke "div_s" (i32.const 1) (i32.const 0)) "integer divide by zero")
(assert_trap (invoke "div_u" (i32.const 1) (i32.const 0)) "integer divide by zero")
