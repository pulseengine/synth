(module
  ;; DECLINE-HONESTY fixture for RQ-71-STACKDEPTH (#1341). A reachable
  ;; `call_indirect` makes the call graph unresolvable, so no finite stack
  ;; bound exists. synth must say so LOUDLY. Emitting a lower bound here —
  ;; "what we could see" — is exactly the silent under-report that corrupted
  ;; the reporter's RTOS pointer, so this fixture exists to keep the refusal.
  (type $sig (func (param i32) (result i32)))
  (table 2 2 funcref)
  (elem (i32.const 0) $one $two)
  (func $one (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (func $two (param i32) (result i32) (local i32 i32 i32)
    local.get 0 i32.const 2 i32.mul)
  (func $top (param i32) (result i32) (local i32)
    local.get 0
    local.get 0
    i32.const 1
    i32.and
    call_indirect (type $sig))
  (export "top" (func $top)))
