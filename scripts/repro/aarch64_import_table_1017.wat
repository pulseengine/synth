;; RQ-60-A64IMPORT (#1017): a funcref TABLE SLOT holding an imported function
;; (the shape blocking ~121 real-world modules / 88 of 101 components).
;; The slot's trampoline becomes `b <field>` relocated against the UNDEFINED
;; import symbol (R_AARCH64_JUMP26).
(module
  (import "env" "ext_inc" (func $ext_inc (param i32) (result i32)))
  (table 2 funcref)
  (elem (i32.const 0) $ext_inc $local_dbl)
  (func $local_dbl (param i32) (result i32)
    local.get 0
    local.get 0
    i32.add)
  (func (export "run") (param i32 i32) (result i32)
    local.get 1
    local.get 0
    call_indirect (param i32) (result i32)))
