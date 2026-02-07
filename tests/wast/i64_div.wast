;; i64 division and remainder tests for Synth
;; Tests 64-bit integer division on ARM Cortex-M (32-bit)

(module
  ;; 64-bit unsigned division
  (func (export "div_u") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.div_u)

  ;; 64-bit signed division
  (func (export "div_s") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.div_s)

  ;; 64-bit unsigned remainder
  (func (export "rem_u") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.rem_u)

  ;; 64-bit signed remainder
  (func (export "rem_s") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.rem_s)
)

;; ===== Unsigned Division Tests =====

;; Basic division
(assert_return (invoke "div_u" (i64.const 10) (i64.const 2)) (i64.const 5))
(assert_return (invoke "div_u" (i64.const 10) (i64.const 3)) (i64.const 3))
(assert_return (invoke "div_u" (i64.const 0) (i64.const 1)) (i64.const 0))
(assert_return (invoke "div_u" (i64.const 1) (i64.const 1)) (i64.const 1))

;; Larger values
(assert_return (invoke "div_u" (i64.const 100) (i64.const 7)) (i64.const 14))
(assert_return (invoke "div_u" (i64.const 0x100000000) (i64.const 2)) (i64.const 0x80000000))
(assert_return (invoke "div_u" (i64.const 0x100000000) (i64.const 0x100000000)) (i64.const 1))

;; Large 64-bit values
(assert_return (invoke "div_u" (i64.const 0xFFFFFFFFFFFFFFFF) (i64.const 2)) (i64.const 0x7FFFFFFFFFFFFFFF))
(assert_return (invoke "div_u" (i64.const 0xFFFFFFFFFFFFFFFF) (i64.const 0xFFFFFFFFFFFFFFFF)) (i64.const 1))

;; ===== Signed Division Tests =====

;; Basic positive division
(assert_return (invoke "div_s" (i64.const 10) (i64.const 2)) (i64.const 5))
(assert_return (invoke "div_s" (i64.const 10) (i64.const 3)) (i64.const 3))

;; Negative dividend
(assert_return (invoke "div_s" (i64.const -10) (i64.const 2)) (i64.const -5))
(assert_return (invoke "div_s" (i64.const -10) (i64.const 3)) (i64.const -3))

;; Negative divisor
(assert_return (invoke "div_s" (i64.const 10) (i64.const -2)) (i64.const -5))
(assert_return (invoke "div_s" (i64.const 10) (i64.const -3)) (i64.const -3))

;; Both negative
(assert_return (invoke "div_s" (i64.const -10) (i64.const -2)) (i64.const 5))
(assert_return (invoke "div_s" (i64.const -10) (i64.const -3)) (i64.const 3))

;; ===== Unsigned Remainder Tests =====

;; Basic remainder
(assert_return (invoke "rem_u" (i64.const 10) (i64.const 3)) (i64.const 1))
(assert_return (invoke "rem_u" (i64.const 10) (i64.const 2)) (i64.const 0))
(assert_return (invoke "rem_u" (i64.const 0) (i64.const 1)) (i64.const 0))
(assert_return (invoke "rem_u" (i64.const 7) (i64.const 7)) (i64.const 0))

;; Larger values
(assert_return (invoke "rem_u" (i64.const 100) (i64.const 7)) (i64.const 2))
(assert_return (invoke "rem_u" (i64.const 0x100000001) (i64.const 0x100000000)) (i64.const 1))

;; ===== Signed Remainder Tests =====
;; Note: Remainder sign follows dividend sign

;; Basic positive remainder
(assert_return (invoke "rem_s" (i64.const 10) (i64.const 3)) (i64.const 1))
(assert_return (invoke "rem_s" (i64.const 10) (i64.const 2)) (i64.const 0))

;; Negative dividend (remainder is negative)
(assert_return (invoke "rem_s" (i64.const -10) (i64.const 3)) (i64.const -1))
(assert_return (invoke "rem_s" (i64.const -10) (i64.const -3)) (i64.const -1))

;; Positive dividend (remainder is positive)
(assert_return (invoke "rem_s" (i64.const 10) (i64.const -3)) (i64.const 1))
