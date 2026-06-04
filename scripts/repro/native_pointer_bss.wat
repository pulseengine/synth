(module
  (memory (export "memory") 1)
  (func (export "unlock") (param $mtx i32) (result i32)
    (i32.store (i32.const 256) (i32.const 1))
    (i32.load (local.get $mtx))))
