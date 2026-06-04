(module
  (memory (export "memory") 1)
  (data (i32.const 256) "\01\00\00\00")
  (func (export "unlock") (param $mtx i32) (result i32)
    (i32.store (i32.const 256) (i32.const 7))
    (i32.load (local.get $mtx))))
