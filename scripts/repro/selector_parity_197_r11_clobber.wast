;; RQ-65-PARITY (#197) — the R11-CLOBBER witness (a PINNED known divergence).
;;
;; `leaf` is tests/wast/control_nested_select.wast's `nested_if_else`
;; verbatim. On the optimized path it leaves R11 = 0 or 1 on return — R11
;; is callee-saved under AAPCS and, in a self-contained image, the direct
;; selector's linear-memory base. `caller` is diverted to the direct selector
;; by its br_table: it stores 7 at wasm byte 0, calls `leaf`, then loads
;; wasm byte 0 through R11 — and reads through R11 = 0 instead.
;;
;; Measured (shipped Reset_Handler under unicorn): `caller(0)` = 1792 where
;; wasmtime returns 7; exit 0, no decline. `caller(1)` takes the br_table arm
;; that never touches memory and agrees (11) — the "correct by accident" shape
;; v0.65 is named after.
;;
;; Executed by scripts/repro/selector_parity_197_differential.py; the
;; divergence is pinned there by exact count with its issue, so the oracle
;; is RED when it disappears (the fix landed — move the pin) and RED when it
;; grows (a new instance).
(module
  (memory 1)
  (func $leaf (export "leaf") (param $a i32) (param $b i32) (result i32)
    (if (result i32) (local.get $a)
      (then (if (result i32) (local.get $b) (then (i32.const 10)) (else (i32.const 20))))
      (else (i32.const 30))))
  (func (export "caller") (param $sel i32) (result i32)
    (i32.store (i32.const 0) (i32.const 7))
    (drop (call $leaf (local.get $sel) (i32.const 1)))
    (block (block (block (local.get $sel) (br_table 0 1 2))
      (return (i32.load (i32.const 0))))
      (return (i32.const 11)))
    (i32.const 22))
)

(assert_return (invoke "leaf" (i32.const 1) (i32.const 1)) (i32.const 10))
(assert_return (invoke "leaf" (i32.const 0) (i32.const 1)) (i32.const 30))
(assert_return (invoke "caller" (i32.const 0)) (i32.const 7))
(assert_return (invoke "caller" (i32.const 1)) (i32.const 11))
(assert_return (invoke "caller" (i32.const 2)) (i32.const 22))
