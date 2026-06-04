(module
  (memory (export "memory") 1)
  ;; NON-exported helper (func 0) — the loom-left non-inlinable callee analogue
  (func $helper (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 1)))
  ;; exported function (func 1) that calls the helper
  (func (export "caller") (param i32) (result i32)
    (call $helper (local.get 0))))
