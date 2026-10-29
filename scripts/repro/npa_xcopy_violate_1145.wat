(module
  (memory $m0 1 1)
  (memory $m1 1 1)
  (global $sp (mut i32) (i32.const 0x800))
  (data (memory $m0) (i32.const 0x1000) "\01\02\03\04")
  (data (memory $m1) (i32.const 0x1000) "\a1\a2\a3\a4")
  ;; tenant: writes a STATIC POINTER into its buffer and also reads through it
  (func (export "tenant") (result i32)
    (i32.store $m0 (i32.const 0x900) (i32.const 0x1000))
    (i32.load $m0 (i32.load $m0 (i32.const 0x900))))
  ;; adapter: copies the buffer — the pointer inside it — into memory 1
  (func (export "adapter")
    (memory.copy $m1 $m0 (i32.const 0x20) (i32.const 0x900) (i32.const 4)))
  ;; supervisor: dereferences the copied pointer IN MEMORY 1 (violates the obligation)
  (func (export "sup") (result i32) (i32.load $m1 (i32.load $m1 (i32.const 0x20)))))
