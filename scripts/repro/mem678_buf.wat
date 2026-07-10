(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 4096))
  (data (i32.const 4160) "\2a\00\00\00")
  (func (export "run") (result i32)
    i32.const 4160
    i32.load
    i32.const 4200
    i32.load
    i32.add))
