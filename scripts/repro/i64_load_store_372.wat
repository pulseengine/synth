(module
  (memory 1)
  (func (export "ld64") (param i32) (result i64) local.get 0 i64.load)
  (func (export "st64") (param i32) (param i64) local.get 0 local.get 1 i64.store)
  (func (export "ld32") (param i32) (result i32) local.get 0 i32.load)
  (func (export "add64") (param i64 i64) (result i64) local.get 0 local.get 1 i64.add))
