;; Calculator -- comprehensive WAST test suite
;;
;; Exercises the calculator example's i32 arithmetic, bitwise ops,
;; accumulator (memory load/store), and comparison/selection logic.
;; Derived from examples/zephyr-calculator/calculator.wat

(module
  ;; One page of linear memory for accumulator state
  (memory (export "memory") 1)

  ;; ---------------------------------------------------------------
  ;; Basic arithmetic
  ;; ---------------------------------------------------------------

  ;; add(a, b) -> a + b
  (func (export "add") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
  )

  ;; sub(a, b) -> a - b
  (func (export "sub") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.sub
  )

  ;; mul(a, b) -> a * b
  (func (export "mul") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.mul
  )

  ;; div_safe(a, b) -> a / b, returns 0 when b == 0
  (func (export "div_safe") (param $a i32) (param $b i32) (result i32)
    (if (result i32) (i32.eqz (local.get $b))
      (then (i32.const 0))
      (else (i32.div_s (local.get $a) (local.get $b)))
    )
  )

  ;; ---------------------------------------------------------------
  ;; Accumulator operations (use linear memory at offset 0)
  ;; ---------------------------------------------------------------

  ;; acc_set(v) -- store v to memory[0..3]
  (func (export "acc_set") (param $v i32)
    i32.const 0
    local.get $v
    i32.store
  )

  ;; acc_get() -> value at memory[0..3]
  (func (export "acc_get") (result i32)
    i32.const 0
    i32.load
  )

  ;; acc_add(v) -> acc += v, return new accumulator value
  (func (export "acc_add") (param $v i32) (result i32)
    (local $new i32)
    ;; new = memory[0] + v
    i32.const 0
    i32.load
    local.get $v
    i32.add
    local.set $new
    ;; memory[0] = new
    i32.const 0
    local.get $new
    i32.store
    ;; return new
    local.get $new
  )

  ;; ---------------------------------------------------------------
  ;; Bitwise operations
  ;; ---------------------------------------------------------------

  ;; bit_and(a, b) -> a & b
  (func (export "bit_and") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.and
  )

  ;; bit_or(a, b) -> a | b
  (func (export "bit_or") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.or
  )

  ;; bit_xor(a, b) -> a ^ b
  (func (export "bit_xor") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.xor
  )

  ;; bit_not(a) -> ~a  (implemented as a XOR 0xFFFFFFFF)
  (func (export "bit_not") (param $a i32) (result i32)
    local.get $a
    i32.const -1
    i32.xor
  )

  ;; ---------------------------------------------------------------
  ;; Comparison / selection
  ;; ---------------------------------------------------------------

  ;; max(a, b) -> the larger value (signed)
  (func (export "max") (param $a i32) (param $b i32) (result i32)
    (if (result i32) (i32.gt_s (local.get $a) (local.get $b))
      (then (local.get $a))
      (else (local.get $b))
    )
  )

  ;; min(a, b) -> the smaller value (signed)
  (func (export "min") (param $a i32) (param $b i32) (result i32)
    (if (result i32) (i32.lt_s (local.get $a) (local.get $b))
      (then (local.get $a))
      (else (local.get $b))
    )
  )

  ;; abs(x) -> |x|
  (func (export "abs") (param $x i32) (result i32)
    (if (result i32) (i32.lt_s (local.get $x) (i32.const 0))
      (then (i32.sub (i32.const 0) (local.get $x)))
      (else (local.get $x))
    )
  )
)

;; =============================================================================
;; Addition tests
;; =============================================================================
(assert_return (invoke "add" (i32.const 5) (i32.const 3)) (i32.const 8))
(assert_return (invoke "add" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "add" (i32.const -1) (i32.const 1)) (i32.const 0))
(assert_return (invoke "add" (i32.const 100) (i32.const 200)) (i32.const 300))
(assert_return (invoke "add" (i32.const -5) (i32.const -3)) (i32.const -8))
(assert_return (invoke "add" (i32.const 0x7FFFFFFF) (i32.const 1)) (i32.const 0x80000000))  ;; overflow wraps

;; =============================================================================
;; Subtraction tests
;; =============================================================================
(assert_return (invoke "sub" (i32.const 10) (i32.const 3)) (i32.const 7))
(assert_return (invoke "sub" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "sub" (i32.const 5) (i32.const 10)) (i32.const -5))
(assert_return (invoke "sub" (i32.const -1) (i32.const -1)) (i32.const 0))
(assert_return (invoke "sub" (i32.const 1000) (i32.const 1)) (i32.const 999))

;; =============================================================================
;; Multiplication tests
;; =============================================================================
(assert_return (invoke "mul" (i32.const 6) (i32.const 7)) (i32.const 42))
(assert_return (invoke "mul" (i32.const 0) (i32.const 100)) (i32.const 0))
(assert_return (invoke "mul" (i32.const -2) (i32.const 3)) (i32.const -6))
(assert_return (invoke "mul" (i32.const -2) (i32.const -3)) (i32.const 6))
(assert_return (invoke "mul" (i32.const 1) (i32.const 42)) (i32.const 42))
(assert_return (invoke "mul" (i32.const 100) (i32.const 100)) (i32.const 10000))

;; =============================================================================
;; Safe division tests (returns 0 on divide-by-zero)
;; =============================================================================
(assert_return (invoke "div_safe" (i32.const 10) (i32.const 3)) (i32.const 3))
(assert_return (invoke "div_safe" (i32.const 10) (i32.const 0)) (i32.const 0))     ;; safe div by zero
(assert_return (invoke "div_safe" (i32.const 0) (i32.const 5)) (i32.const 0))
(assert_return (invoke "div_safe" (i32.const 100) (i32.const 10)) (i32.const 10))
(assert_return (invoke "div_safe" (i32.const -10) (i32.const 3)) (i32.const -3))    ;; signed division
(assert_return (invoke "div_safe" (i32.const 7) (i32.const 2)) (i32.const 3))       ;; truncation
(assert_return (invoke "div_safe" (i32.const -7) (i32.const 2)) (i32.const -3))     ;; signed truncation
(assert_return (invoke "div_safe" (i32.const 1) (i32.const 1)) (i32.const 1))

;; =============================================================================
;; Accumulator tests
;; Memory starts at zero, each test runs in a fresh machine so acc starts at 0
;; =============================================================================

;; acc_get reads memory[0] which starts at 0
(assert_return (invoke "acc_get") (i32.const 0))

;; acc_add adds to memory[0] (starts at 0): 0 + 42 = 42
(assert_return (invoke "acc_add" (i32.const 42)) (i32.const 42))

;; acc_add with 0: 0 + 0 = 0
(assert_return (invoke "acc_add" (i32.const 0)) (i32.const 0))

;; acc_add with negative: 0 + (-10) = -10
(assert_return (invoke "acc_add" (i32.const -10)) (i32.const -10))

;; =============================================================================
;; Bitwise AND tests
;; =============================================================================
(assert_return (invoke "bit_and" (i32.const 0xFF) (i32.const 0x0F)) (i32.const 0x0F))
(assert_return (invoke "bit_and" (i32.const 0x12345678) (i32.const 0x0000FFFF)) (i32.const 0x00005678))
(assert_return (invoke "bit_and" (i32.const 0) (i32.const 0xFFFFFFFF)) (i32.const 0))
(assert_return (invoke "bit_and" (i32.const -1) (i32.const -1)) (i32.const -1))

;; =============================================================================
;; Bitwise OR tests
;; =============================================================================
(assert_return (invoke "bit_or" (i32.const 0xF0) (i32.const 0x0F)) (i32.const 0xFF))
(assert_return (invoke "bit_or" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "bit_or" (i32.const 0xAAAA0000) (i32.const 0x0000BBBB)) (i32.const 0xAAAABBBB))

;; =============================================================================
;; Bitwise XOR tests
;; =============================================================================
(assert_return (invoke "bit_xor" (i32.const 0xFF) (i32.const 0xFF)) (i32.const 0))
(assert_return (invoke "bit_xor" (i32.const 0xAAAA) (i32.const 0x5555)) (i32.const 0xFFFF))
(assert_return (invoke "bit_xor" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "bit_xor" (i32.const 123) (i32.const 0)) (i32.const 123))

;; =============================================================================
;; Bitwise NOT tests (~a via XOR -1)
;; =============================================================================
(assert_return (invoke "bit_not" (i32.const 0)) (i32.const -1))
(assert_return (invoke "bit_not" (i32.const -1)) (i32.const 0))
(assert_return (invoke "bit_not" (i32.const 0x0000FFFF)) (i32.const 0xFFFF0000))
(assert_return (invoke "bit_not" (i32.const 1)) (i32.const -2))

;; =============================================================================
;; Max tests (signed comparison)
;; =============================================================================
(assert_return (invoke "max" (i32.const 5) (i32.const 10)) (i32.const 10))
(assert_return (invoke "max" (i32.const 10) (i32.const 5)) (i32.const 10))
(assert_return (invoke "max" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "max" (i32.const -5) (i32.const 5)) (i32.const 5))
(assert_return (invoke "max" (i32.const -1) (i32.const -10)) (i32.const -1))
(assert_return (invoke "max" (i32.const 7) (i32.const 7)) (i32.const 7))           ;; equal values

;; =============================================================================
;; Min tests (signed comparison)
;; =============================================================================
(assert_return (invoke "min" (i32.const 5) (i32.const 10)) (i32.const 5))
(assert_return (invoke "min" (i32.const 10) (i32.const 5)) (i32.const 5))
(assert_return (invoke "min" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "min" (i32.const -5) (i32.const 5)) (i32.const -5))
(assert_return (invoke "min" (i32.const -1) (i32.const -10)) (i32.const -10))
(assert_return (invoke "min" (i32.const 7) (i32.const 7)) (i32.const 7))           ;; equal values

;; =============================================================================
;; Abs tests
;; =============================================================================
(assert_return (invoke "abs" (i32.const -5)) (i32.const 5))
(assert_return (invoke "abs" (i32.const 5)) (i32.const 5))
(assert_return (invoke "abs" (i32.const 0)) (i32.const 0))
(assert_return (invoke "abs" (i32.const -1)) (i32.const 1))
(assert_return (invoke "abs" (i32.const -100)) (i32.const 100))
(assert_return (invoke "abs" (i32.const 1)) (i32.const 1))
