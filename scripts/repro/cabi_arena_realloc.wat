(module
  (import "env" "__cabi_arena_realloc"
    (func $arena (param i32 i32 i32 i32) (result i32)))
  (memory 1)
  (func (export "do_realloc") (param i32 i32) (result i32)
    (call $arena (local.get 0) (i32.const 0) (i32.const 8) (local.get 1))))
