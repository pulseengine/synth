(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 4096))
  (func (export "rw") (param i32) (result i32)
    i32.const 4160
    local.get 0
    i32.store
    i32.const 4160
    i32.load))
