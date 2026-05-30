(module
  (import "env" "host_fn" (func $host (param i32) (result i32)))
  (func $caller (export "caller") (param i32) (result i32)
    local.get 0  call $host))
