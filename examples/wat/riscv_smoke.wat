;; Minimal WAT exercising the i32 ops the RISC-V selector currently supports.
;; No `call` (cross-function calls aren't lowered yet — out of scope for B2/B3).
;; No `fib`-style recursion. Just leaf arithmetic + comparison + memory ops.
(module
  (memory (export "memory") 1)

  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add)

  (func (export "subtract") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.sub)

  (func (export "max") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.gt_s
    if (result i32) (local.get 0)
    else (local.get 1)
    end))
