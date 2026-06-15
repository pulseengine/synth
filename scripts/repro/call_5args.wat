(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 65536))
  ;; callee packs each arg into a distinct nibble: a | b<<4 | c<<8 | d<<12 | e<<16.
  ;; Any dropped/shifted/mis-assigned argument changes the result.
  (func $callee (param i32 i32 i32 i32 i32) (result i32)
    (i32.or
      (i32.or
        (i32.or (local.get 0) (i32.shl (local.get 1) (i32.const 4)))
        (i32.or (i32.shl (local.get 2) (i32.const 8)) (i32.shl (local.get 3) (i32.const 12))))
      (i32.shl (local.get 4) (i32.const 16))))
  (func (export "caller") (param i32 i32 i32 i32 i32) (result i32)
    (call $callee (local.get 0) (local.get 1) (local.get 2) (local.get 3) (local.get 4))))
