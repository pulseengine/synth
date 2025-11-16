;; Simple WebAssembly module that adds two numbers
(module
  ;; Memory: 1 page (64KB)
  (memory (export "memory") 1)

  ;; Add two i32 numbers
  (func (export "add") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
  )

  ;; Fibonacci function (recursive)
  (func (export "fib") (param $n i32) (result i32)
    (if (result i32) (i32.le_u (local.get $n) (i32.const 1))
      (then (local.get $n))
      (else
        (i32.add
          (call 1 (i32.sub (local.get $n) (i32.const 1)))
          (call 1 (i32.sub (local.get $n) (i32.const 2)))
        )
      )
    )
  )

  ;; Store value to memory
  (func (export "store_value") (param $addr i32) (param $value i32)
    local.get $addr
    local.get $value
    i32.store
  )

  ;; Load value from memory
  (func (export "load_value") (param $addr i32) (result i32)
    local.get $addr
    i32.load
  )
)
