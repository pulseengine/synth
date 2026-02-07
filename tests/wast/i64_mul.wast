;; i64 multiplication tests for Synth
;; Tests 64-bit integer multiplication on ARM Cortex-M (32-bit)
;; On ARM Thumb-2: uses UMULL for the low*low part, plus MUL + MLA for cross terms
;; Full formula: result_lo = lo(a_lo * b_lo), result_hi = hi(a_lo * b_lo) + a_lo * b_hi + a_hi * b_lo

(module
  ;; 64-bit multiplication
  (func (export "mul") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.mul)
)

;; ===== i64.mul tests =====
;; Basic multiplication
(assert_return (invoke "mul" (i64.const 0) (i64.const 0)) (i64.const 0))
(assert_return (invoke "mul" (i64.const 1) (i64.const 0)) (i64.const 0))
(assert_return (invoke "mul" (i64.const 0) (i64.const 1)) (i64.const 0))
(assert_return (invoke "mul" (i64.const 1) (i64.const 1)) (i64.const 1))
(assert_return (invoke "mul" (i64.const 2) (i64.const 3)) (i64.const 6))
(assert_return (invoke "mul" (i64.const 7) (i64.const 11)) (i64.const 77))

;; Multiply by powers of 2 (equivalent to shifts)
(assert_return (invoke "mul" (i64.const 1) (i64.const 2)) (i64.const 2))
(assert_return (invoke "mul" (i64.const 5) (i64.const 4)) (i64.const 20))

;; Results crossing 32-bit boundary
(assert_return (invoke "mul" (i64.const 0x80000000) (i64.const 2)) (i64.const 0x100000000))
(assert_return (invoke "mul" (i64.const 0xFFFFFFFF) (i64.const 2)) (i64.const 0x1FFFFFFFE))

;; Both operands in high word
(assert_return (invoke "mul" (i64.const 0x100000000) (i64.const 0)) (i64.const 0))
(assert_return (invoke "mul" (i64.const 0x100000000) (i64.const 1)) (i64.const 0x100000000))

;; Negative values (two's complement wrapping)
(assert_return (invoke "mul" (i64.const -1) (i64.const 1)) (i64.const -1))
(assert_return (invoke "mul" (i64.const -1) (i64.const -1)) (i64.const 1))
(assert_return (invoke "mul" (i64.const -2) (i64.const 3)) (i64.const -6))
(assert_return (invoke "mul" (i64.const 3) (i64.const -2)) (i64.const -6))
