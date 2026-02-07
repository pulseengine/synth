;; Remainder tests for Synth
;; Tests integer remainder operations

(module
  ;; Signed remainder
  (func (export "rem_s") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.rem_s)

  ;; Unsigned remainder
  (func (export "rem_u") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.rem_u)
)

;; Normal remainder tests
(assert_return (invoke "rem_s" (i32.const 10) (i32.const 3)) (i32.const 1))
(assert_return (invoke "rem_s" (i32.const 10) (i32.const 2)) (i32.const 0))
(assert_return (invoke "rem_s" (i32.const 7) (i32.const 4)) (i32.const 3))
(assert_return (invoke "rem_s" (i32.const -7) (i32.const 3)) (i32.const -1))
(assert_return (invoke "rem_u" (i32.const 10) (i32.const 3)) (i32.const 1))
(assert_return (invoke "rem_u" (i32.const 7) (i32.const 4)) (i32.const 3))
