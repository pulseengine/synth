;; Calculator - four basic arithmetic operations
;; Tests the core WASM-to-ARM compilation pipeline
(module
  ;; Add two i32 numbers
  (func (export "add") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
  )

  ;; Subtract: a - b
  (func (export "sub") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.sub
  )

  ;; Multiply two i32 numbers
  (func (export "mul") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.mul
  )

  ;; Bitwise AND
  (func (export "and") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.and
  )

  ;; Bitwise OR
  (func (export "or") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.or
  )

  ;; Bitwise XOR
  (func (export "xor") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.xor
  )
)
