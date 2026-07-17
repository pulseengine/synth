;; #275 — self-contained call_indirect emission/decline fixture.
;;
;; `entry` dispatches through a constant table (index loaded from linmem[100]).
;;
;; HISTORY: the naive self-contained dispatch loaded the function pointer from
;; the contiguous R11 table region — but R11 is the LINEAR-MEMORY base and
;; NOTHING populates that region in a self-contained image, so
;; `ldr ip,[r11,idx*4]` read function pointers from linear-memory DATA (a
;; silent miscompile). v0.42 (#717) loud-declined; v0.47 CONVERTED the
;; Thumb-2 `--cortex-m` path: the funcref table now ships in FLASH and the
;; dispatch reaches it PC-relative (`__synth_func_table`), never via R11 —
;; `entry` EMITS again. The A32/Cortex-R5 self-contained path (no flash-table
;; builder) keeps the loud decline (AFD-008).
;;
;; The `--relocatable` path (where a runtime places the table region at R11)
;; keeps emitting the guarded dispatch — see the #642/#650/#664/#676 oracles.
;; Execution semantics are gated by the companion
;; call_indirect_275_selfcontained_execution_differential.py.
(module
  (memory (export "memory") 1)
  (type $ret (func (result i32)))
  (func (export "entry")
    (i32.store (i32.const 0)
      (call_indirect (type $ret) (i32.load (i32.const 100)))))
  (func $f0 (type $ret) (i32.const 100))
  (func $f1 (type $ret) (i32.const 200))
  (func $f2 (type $ret) (i32.const 300))
  (table 3 funcref) (elem (i32.const 0) $f0 $f1 $f2))
