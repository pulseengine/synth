;; Minimal WAT module for ELF integration test
;; Exports a single i32 add function
(module
  (func (export "add") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add
  )
)
