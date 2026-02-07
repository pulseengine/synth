;; Control flow tests - Phase 3b: if-else blocks
;; These test conditional execution with branching

(module
  ;; Simple if-else returning a value
  ;; Returns 1 if condition != 0, else returns 0
  (func (export "if_else_simple") (param i32) (result i32)
    local.get 0
    if (result i32)
      i32.const 1
    else
      i32.const 0
    end)

  ;; Nested select equivalent using if-else
  ;; Returns first param if cond != 0, else second param
  (func (export "if_else_select") (param i32 i32 i32) (result i32)
    local.get 2  ;; condition
    if (result i32)
      local.get 0  ;; true value
    else
      local.get 1  ;; false value
    end)
)

;; Basic if-else tests
(assert_return (invoke "if_else_simple" (i32.const 1)) (i32.const 1))
(assert_return (invoke "if_else_simple" (i32.const 0)) (i32.const 0))
(assert_return (invoke "if_else_simple" (i32.const 42)) (i32.const 1))
(assert_return (invoke "if_else_simple" (i32.const -1)) (i32.const 1))

;; if_else_select should behave like select
(assert_return (invoke "if_else_select" (i32.const 10) (i32.const 20) (i32.const 1)) (i32.const 10))
(assert_return (invoke "if_else_select" (i32.const 10) (i32.const 20) (i32.const 0)) (i32.const 20))
