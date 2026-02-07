;; i64 comparison tests for Synth
;; Tests 64-bit integer comparison operations on ARM Cortex-M (32-bit)
;; i64 comparisons take two i64 params and return an i32 result (0 or 1)
;; On ARM Thumb-2: compare R0:R1 vs R2:R3 register pairs, result in R0

(module
  ;; 64-bit equality
  (func (export "eq") (param i64 i64) (result i32)
    local.get 0
    local.get 1
    i64.eq)

  ;; 64-bit not-equal
  (func (export "ne") (param i64 i64) (result i32)
    local.get 0
    local.get 1
    i64.ne)

  ;; 64-bit signed less-than
  (func (export "lt_s") (param i64 i64) (result i32)
    local.get 0
    local.get 1
    i64.lt_s)

  ;; 64-bit signed greater-than
  (func (export "gt_s") (param i64 i64) (result i32)
    local.get 0
    local.get 1
    i64.gt_s)

  ;; 64-bit equal-to-zero (unary: single i64 param)
  (func (export "eqz") (param i64) (result i32)
    local.get 0
    i64.eqz)
)

;; ===== i64.eq tests =====
;; Same values -> 1
(assert_return (invoke "eq" (i64.const 0) (i64.const 0)) (i32.const 1))
(assert_return (invoke "eq" (i64.const 1) (i64.const 1)) (i32.const 1))
(assert_return (invoke "eq" (i64.const 0x100000000) (i64.const 0x100000000)) (i32.const 1))
;; Different values -> 0
(assert_return (invoke "eq" (i64.const 0) (i64.const 1)) (i32.const 0))
(assert_return (invoke "eq" (i64.const 1) (i64.const 0)) (i32.const 0))
;; Same low word, different high word
(assert_return (invoke "eq" (i64.const 0x100000001) (i64.const 0x200000001)) (i32.const 0))
;; Same high word, different low word
(assert_return (invoke "eq" (i64.const 0x100000001) (i64.const 0x100000002)) (i32.const 0))

;; ===== i64.ne tests =====
;; Same values -> 0
(assert_return (invoke "ne" (i64.const 0) (i64.const 0)) (i32.const 0))
(assert_return (invoke "ne" (i64.const 42) (i64.const 42)) (i32.const 0))
;; Different values -> 1
(assert_return (invoke "ne" (i64.const 0) (i64.const 1)) (i32.const 1))
(assert_return (invoke "ne" (i64.const 0x100000000) (i64.const 0x200000000)) (i32.const 1))
;; Differ only in high word
(assert_return (invoke "ne" (i64.const 0x100000000) (i64.const 0)) (i32.const 1))

;; ===== i64.lt_s tests =====
;; Basic ordering
(assert_return (invoke "lt_s" (i64.const 1) (i64.const 2)) (i32.const 1))
(assert_return (invoke "lt_s" (i64.const 2) (i64.const 1)) (i32.const 0))
(assert_return (invoke "lt_s" (i64.const 1) (i64.const 1)) (i32.const 0))
;; Negative values (signed)
(assert_return (invoke "lt_s" (i64.const -1) (i64.const 0)) (i32.const 1))
(assert_return (invoke "lt_s" (i64.const -2) (i64.const -1)) (i32.const 1))
(assert_return (invoke "lt_s" (i64.const 0) (i64.const -1)) (i32.const 0))
;; Large positive values spanning high word
(assert_return (invoke "lt_s" (i64.const 0xFFFFFFFF) (i64.const 0x100000000)) (i32.const 1))
(assert_return (invoke "lt_s" (i64.const 0x100000000) (i64.const 0xFFFFFFFF)) (i32.const 0))

;; ===== i64.gt_s tests =====
;; Basic ordering
(assert_return (invoke "gt_s" (i64.const 2) (i64.const 1)) (i32.const 1))
(assert_return (invoke "gt_s" (i64.const 1) (i64.const 2)) (i32.const 0))
(assert_return (invoke "gt_s" (i64.const 1) (i64.const 1)) (i32.const 0))
;; Negative values (signed)
(assert_return (invoke "gt_s" (i64.const 0) (i64.const -1)) (i32.const 1))
(assert_return (invoke "gt_s" (i64.const -1) (i64.const -2)) (i32.const 1))
(assert_return (invoke "gt_s" (i64.const -1) (i64.const 0)) (i32.const 0))
;; Large values
(assert_return (invoke "gt_s" (i64.const 0x100000000) (i64.const 0xFFFFFFFF)) (i32.const 1))

;; ===== i64.eqz tests =====
;; Zero -> 1
(assert_return (invoke "eqz" (i64.const 0)) (i32.const 1))
;; Non-zero -> 0
(assert_return (invoke "eqz" (i64.const 1)) (i32.const 0))
(assert_return (invoke "eqz" (i64.const -1)) (i32.const 0))
;; Only high word is non-zero
(assert_return (invoke "eqz" (i64.const 0x100000000)) (i32.const 0))
;; Only low word is non-zero
(assert_return (invoke "eqz" (i64.const 0x00000001)) (i32.const 0))
