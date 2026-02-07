;; Bit count tests for Synth
;; Tests CLZ, CTZ, POPCNT operations

(module
  ;; Count leading zeros
  (func (export "clz") (param i32) (result i32)
    local.get 0
    i32.clz)

  ;; Count trailing zeros
  (func (export "ctz") (param i32) (result i32)
    local.get 0
    i32.ctz)

  ;; Population count (count 1 bits)
  (func (export "popcnt") (param i32) (result i32)
    local.get 0
    i32.popcnt)
)

;; CLZ tests
(assert_return (invoke "clz" (i32.const 0)) (i32.const 32))
(assert_return (invoke "clz" (i32.const 1)) (i32.const 31))
(assert_return (invoke "clz" (i32.const 2)) (i32.const 30))
(assert_return (invoke "clz" (i32.const 0x80000000)) (i32.const 0))
(assert_return (invoke "clz" (i32.const 0x7FFFFFFF)) (i32.const 1))

;; CTZ tests
(assert_return (invoke "ctz" (i32.const 0)) (i32.const 32))
(assert_return (invoke "ctz" (i32.const 1)) (i32.const 0))
(assert_return (invoke "ctz" (i32.const 2)) (i32.const 1))
(assert_return (invoke "ctz" (i32.const 0x80000000)) (i32.const 31))
(assert_return (invoke "ctz" (i32.const 0x7FFFFFFF)) (i32.const 0))

;; POPCNT tests
(assert_return (invoke "popcnt" (i32.const 0)) (i32.const 0))
(assert_return (invoke "popcnt" (i32.const 1)) (i32.const 1))
(assert_return (invoke "popcnt" (i32.const 0xFFFFFFFF)) (i32.const 32))
(assert_return (invoke "popcnt" (i32.const 0x55555555)) (i32.const 16))
