(module
  (func $callee (param i32) (result i32)
    local.get 0  i32.const 7  i32.add)
  (func $caller (export "caller") (param i32) (result i32)
    local.get 0  call $callee  i32.const 2  i32.mul)
  (export "callee" (func $callee)))
