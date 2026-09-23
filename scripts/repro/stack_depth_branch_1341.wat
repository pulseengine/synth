(module
  ;; A BRANCHING call graph, so "sum over all frames" and "max over the call
  ;; tree" give different answers. top calls a and b; both call leaf.
  ;; Only ONE root-to-leaf path is live at a time.
  (func $leaf (param i32) (result i32)
    local.get 0 i32.const 1 i32.add)
  (func $a (param i32) (result i32) (local i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 0 call $leaf local.set 1
    local.get 1 local.get 0 i32.add)
  (func $b (param i32) (result i32) (local i32 i32)
    local.get 0 call $leaf local.set 1
    local.get 1 i32.const 7 i32.xor)
  (func $top (param i32) (result i32) (local i32 i32 i32)
    local.get 0 call $a local.set 1
    local.get 0 call $b local.set 2
    local.get 1 local.get 2 i32.add)
  (export "top" (func $top)))
