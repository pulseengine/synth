;; Calculator -- integer arithmetic, bitwise ops, accumulator, and comparisons
;;
;; A comprehensive example for Synth, the WASM-to-ARM Cortex-M compiler.
;; Exercises i32 arithmetic, memory load/store, bitwise operations,
;; and if/else control flow.
;;
;; Compile:
;;   synth compile examples/zephyr-calculator/calculator.wat \
;;     -o calculator.elf --cortex-m --all-exports

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
