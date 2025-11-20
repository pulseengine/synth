;; Simple WASM program: Add two i32 constants
;; Expected result: 42 + 13 = 55

(module
  (func $add_test (result i32)
    i32.const 42
    i32.const 13
    i32.add
  )
  (export "test" (func $add_test))
)
