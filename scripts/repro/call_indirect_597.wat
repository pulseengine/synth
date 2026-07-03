;; #597: the Thumb-2 CallIndirect expansion encoded its `LSL #2` shift amount
;; into the TYPE field of the mov.w (bits 5:4, giving ASR #32) instead of
;; imm2 (bits 7:6) — the table index was destroyed and every call_indirect
;; dispatched entry 0. A single-entry table (the #594 probe) cannot see it;
;; this table has distinct results at indexes 0, 1 and 3.
;; wasmtime oracle: run(0)=10, run(1)=11, run(3)=13.
(module
  (type $s (func (result i32)))
  (table 4 funcref)
  (elem (i32.const 0) $f0 $f1 $f0 $f3)
  (func $f0 (result i32) (i32.const 10))
  (func $f1 (result i32) (i32.const 11))
  (func $f3 (result i32) (i32.const 13))
  (func (export "run") (param i32) (result i32)
    (call_indirect (type $s) (local.get 0))))
