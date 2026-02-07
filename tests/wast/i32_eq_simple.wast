;; Simple equality test - single function
(module
  (func (export "eq") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.eq))

(assert_return (invoke "eq" (i32.const 5) (i32.const 5)) (i32.const 1))
(assert_return (invoke "eq" (i32.const 5) (i32.const 3)) (i32.const 0))
