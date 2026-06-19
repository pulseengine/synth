(module
  (memory 1)
  (func (export "cpy") (param i32 i32 i32) local.get 0 local.get 1 local.get 2 memory.copy)
  (func (export "fil") (param i32 i32 i32) local.get 0 local.get 1 local.get 2 memory.fill)
  (func (export "ld32") (param i32) (result i32) local.get 0 i32.load))
