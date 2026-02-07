;; Basic i32 arithmetic tests for Synth
;; These tests verify that Synth correctly compiles arithmetic operations
;; and produces correct results when executed on Cortex-M

(module
  ;; Simple addition
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add)

  ;; Subtraction
  (func (export "sub") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.sub)

  ;; Multiplication
  (func (export "mul") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.mul)

  ;; Bitwise AND
  (func (export "and") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.and)

  ;; Bitwise OR
  (func (export "or") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.or)

  ;; Bitwise XOR
  (func (export "xor") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.xor)
)

;; Addition tests
(assert_return (invoke "add" (i32.const 5) (i32.const 3)) (i32.const 8))
(assert_return (invoke "add" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "add" (i32.const 1) (i32.const -1)) (i32.const 0))
(assert_return (invoke "add" (i32.const 100) (i32.const 200)) (i32.const 300))
(assert_return (invoke "add" (i32.const -5) (i32.const -3)) (i32.const -8))

;; Subtraction tests
(assert_return (invoke "sub" (i32.const 10) (i32.const 4)) (i32.const 6))
(assert_return (invoke "sub" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "sub" (i32.const 5) (i32.const 10)) (i32.const -5))

;; Multiplication tests
(assert_return (invoke "mul" (i32.const 3) (i32.const 4)) (i32.const 12))
(assert_return (invoke "mul" (i32.const 0) (i32.const 100)) (i32.const 0))
(assert_return (invoke "mul" (i32.const -2) (i32.const 3)) (i32.const -6))
(assert_return (invoke "mul" (i32.const -2) (i32.const -3)) (i32.const 6))

;; Bitwise AND tests
(assert_return (invoke "and" (i32.const 0xFF) (i32.const 0x0F)) (i32.const 0x0F))
(assert_return (invoke "and" (i32.const 0x12345678) (i32.const 0x0000FFFF)) (i32.const 0x00005678))

;; Bitwise OR tests
(assert_return (invoke "or" (i32.const 0xF0) (i32.const 0x0F)) (i32.const 0xFF))
(assert_return (invoke "or" (i32.const 0) (i32.const 0)) (i32.const 0))

;; Bitwise XOR tests
(assert_return (invoke "xor" (i32.const 0xFF) (i32.const 0xFF)) (i32.const 0))
(assert_return (invoke "xor" (i32.const 0xAAAA) (i32.const 0x5555)) (i32.const 0xFFFF))
