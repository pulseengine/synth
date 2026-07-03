;; #594: call_indirect on the A32 path (--target cortex-r5) compiled to a
;; literal NOP (0xE1A00000) — the call never happened and `run` returned the
;; leftover table-index value instead of the callee's result.
;; wasmtime oracle: run() = 42.
(module
  (type $s (func (result i32)))
  (table 1 funcref)
  (elem (i32.const 0) $t)
  (func $t (result i32) (i32.const 42))
  (func (export "run") (result i32)
    (call_indirect (type $s) (i32.const 0))))
