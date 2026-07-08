;; #664 — sparse funcref table: null (uninitialized) slots must TRAP, not
;; decline the whole function. 4 slots, only 1 and 3 initialized (by two
;; separate element segments — the falcon fused-component shape); slots 0
;; and 2 are null funcrefs. WASM Core §4.4.8: call_indirect through a null
;; slot traps ("uninitialized element" in wasmtime); through 1/3 it calls
;; $f1/$f3; index >= 4 is the OOB trap.
;;
;; Layout contract (#650/#664): the runtime/harness links the table as raw
;; 4-byte code pointers at R11 and MUST link every uninitialized slot as a
;; ZERO word — the emitted null check (`cmp ip, #0; bne ok; udf`) turns
;; that zero into the §4.4.8 trap.
(module
  (type $t (func (param i32) (result i32)))
  (table 4 4 funcref)
  (func $f1 (type $t) (i32.add (local.get 0) (i32.const 100)))
  (func $f3 (type $t) (i32.sub (i32.const 1000) (local.get 0)))
  (elem (i32.const 1) func $f1)
  (elem (i32.const 3) func $f3)
  (func (export "via") (param $x i32) (param $sel i32) (result i32)
    (call_indirect (type $t) (local.get $x) (local.get $sel))))
