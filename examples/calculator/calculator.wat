;; Calculator — basic integer arithmetic operations
;;
;; A starter example for Synth, the WASM-to-ARM Cortex-M compiler.
;; Each function takes two i32 parameters and returns an i32 result.
;;
;; Compile:
;;   synth compile examples/calculator/calculator.wat -o calculator.elf --cortex-m --all-exports
;;
;; Verify (with Z3 translation validation):
;;   synth compile examples/calculator/calculator.wat -o calculator.elf --cortex-m --all-exports --verify

(module
  ;; Addition: a + b
  (func (export "add") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
  )

  ;; Subtraction: a - b
  (func (export "subtract") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.sub
  )

  ;; Multiplication: a * b
  (func (export "multiply") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.mul
  )

  ;; Signed division: a / b
  ;; Traps on division by zero or signed overflow (INT32_MIN / -1).
  (func (export "divide") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.div_s
  )

  ;; Signed remainder: a % b
  ;; Traps on division by zero. The result has the same sign as the dividend.
  (func (export "modulo") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.rem_s
  )
)
