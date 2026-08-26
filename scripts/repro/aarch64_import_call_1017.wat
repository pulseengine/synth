;; RQ-60-A64IMPORT (#1017): a DIRECT call to an imported function.
;; The Wasker/wasm2c/ARM-#197 pattern: the import becomes an UNDEFINED
;; symbol (its wasm field name) the host linker resolves.
(module
  (import "env" "host_add" (func $host_add (param i32 i32) (result i32)))
  (func (export "run") (param i32) (result i32)
    local.get 0
    i32.const 5
    call $host_add))
