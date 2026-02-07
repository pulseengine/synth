;; i64 arithmetic tests for Synth
;; Tests basic 64-bit integer operations on ARM Cortex-M (32-bit)

(module
  ;; 64-bit addition using register pairs
  (func (export "add") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.add)

  ;; 64-bit subtraction using register pairs
  (func (export "sub") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.sub)

  ;; 64-bit bitwise AND
  (func (export "and") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.and)

  ;; 64-bit bitwise OR
  (func (export "or") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.or)

  ;; 64-bit bitwise XOR
  (func (export "xor") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.xor)
)

;; Addition tests
(assert_return (invoke "add" (i64.const 1) (i64.const 2)) (i64.const 3))
(assert_return (invoke "add" (i64.const 0) (i64.const 0)) (i64.const 0))
(assert_return (invoke "add" (i64.const 0x100000000) (i64.const 1)) (i64.const 0x100000001))
(assert_return (invoke "add" (i64.const 0xFFFFFFFF) (i64.const 1)) (i64.const 0x100000000))
(assert_return (invoke "add" (i64.const 0x7FFFFFFFFFFFFFFF) (i64.const 1)) (i64.const 0x8000000000000000))

;; Subtraction tests
(assert_return (invoke "sub" (i64.const 5) (i64.const 3)) (i64.const 2))
(assert_return (invoke "sub" (i64.const 0) (i64.const 0)) (i64.const 0))
(assert_return (invoke "sub" (i64.const 0x100000000) (i64.const 1)) (i64.const 0xFFFFFFFF))
(assert_return (invoke "sub" (i64.const 0x100000001) (i64.const 0x100000000)) (i64.const 1))

;; Bitwise AND tests
(assert_return (invoke "and" (i64.const 0xFF00FF00FF00FF00) (i64.const 0x00FF00FF00FF00FF)) (i64.const 0))
(assert_return (invoke "and" (i64.const 0xFFFFFFFFFFFFFFFF) (i64.const 0x123456789ABCDEF0)) (i64.const 0x123456789ABCDEF0))

;; Bitwise OR tests
(assert_return (invoke "or" (i64.const 0xFF00FF00FF00FF00) (i64.const 0x00FF00FF00FF00FF)) (i64.const 0xFFFFFFFFFFFFFFFF))
(assert_return (invoke "or" (i64.const 0) (i64.const 0x123456789ABCDEF0)) (i64.const 0x123456789ABCDEF0))

;; Bitwise XOR tests
(assert_return (invoke "xor" (i64.const 0xFFFFFFFFFFFFFFFF) (i64.const 0xFFFFFFFFFFFFFFFF)) (i64.const 0))
(assert_return (invoke "xor" (i64.const 0x123456789ABCDEF0) (i64.const 0)) (i64.const 0x123456789ABCDEF0))
