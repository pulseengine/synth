;; Control flow tests - Phase 3a: select (ternary operator)
;; select pops (val1, val2, cond) and pushes val1 if cond!=0, else val2

(module
  ;; Select based on condition: returns first arg if cond!=0, else second arg
  (func (export "select_i32") (param i32 i32 i32) (result i32)
    local.get 0    ;; val1 (true case)
    local.get 1    ;; val2 (false case)
    local.get 2    ;; condition
    select)
)

;; Basic select tests
(assert_return (invoke "select_i32" (i32.const 10) (i32.const 20) (i32.const 1)) (i32.const 10))
(assert_return (invoke "select_i32" (i32.const 10) (i32.const 20) (i32.const 0)) (i32.const 20))
(assert_return (invoke "select_i32" (i32.const 10) (i32.const 20) (i32.const 42)) (i32.const 10))
(assert_return (invoke "select_i32" (i32.const 10) (i32.const 20) (i32.const -1)) (i32.const 10))

;; Edge cases
(assert_return (invoke "select_i32" (i32.const 0) (i32.const 1) (i32.const 1)) (i32.const 0))
(assert_return (invoke "select_i32" (i32.const 0) (i32.const 1) (i32.const 0)) (i32.const 1))
