(module
  ;; leaf: no locals at all -> frame_size 0 -> NO `sub sp` emitted,
  ;; yet it still consumes DIRECT_PROLOGUE_BYTES (24) on entry.
  (func $leaf (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add)
  (func $mid (param i32) (result i32) (local i32 i32 i32)
    local.get 0
    call $leaf
    local.set 1
    local.get 1
    local.get 0
    i32.add)
  (func $top (param i32) (result i32) (local i32 i32 i32 i32 i32)
    local.get 0
    call $mid
    local.set 1
    local.get 1
    i32.const 3
    i32.mul)
  (export "top" (func $top)))
