(module
  (memory 1)
  (func $load_field (export "load_field") (param i32) (result i32)
    local.get 0
    i32.load offset=0))
