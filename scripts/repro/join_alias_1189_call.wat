;; #1189 — the CALL-containing control. A function with a `call` frame-backs
;; its params on the ARM direct selector (#204/#193: read through the slot,
;; never the home register), so `local.get 0` in the then-arm loads a fresh
;; temp and the join cannot alias a home. Kept in its own module because the
;; `bl` relocation is resolved by the harness for the ARM legs only (the
;; mechanism it controls for is ARM-direct-selector specific).
(module
  (func $g (param i32) (result i32) (i32.add (local.get 0) (i32.const 1)))
  (func (export "icall") (param i32) (result i32)
    (call $g (local.get 0)) drop
    (if (result i32) (local.get 0) (then (local.get 0)) (else (i32.const 9)))
    (local.get 0) i32.add))
