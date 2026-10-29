(module
  (memory $m0 1 1)
  (memory $m1 1 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (memory $m0) (i32.const 0x1000) "\01\02\03\04")
  ;; tenant: stores a static pointer in its frame and reads through it (Rust &str style)
  (func (export "tenant") (result i32) (local $fp i32)
    (local.set $fp (i32.sub (global.get $sp) (i32.const 16)))
    (i32.store $m0 (local.get $fp) (i32.const 0x1000))
    (i32.load $m0 (i32.load $m0 (local.get $fp))))
  ;; supervisor: follows a pointer stored in its own memory
  (func (export "sup") (result i32) (i32.load $m1 (i32.load $m1 (i32.const 0x10))))
  ;; adapter: copies a buffer across
  (func (export "adapter") (param i32 i32 i32) (memory.copy $m1 $m0 (local.get 0) (local.get 1) (local.get 2))))
