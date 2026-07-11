;; #275 — self-contained `--cortex-m` call_indirect silent-miscompile repro.
;;
;; `entry` dispatches through a constant table (index loaded from linmem[100]).
;; wasmtime stores 100/200/300 to linmem[0] for table indices 0/1/2.
;;
;; On the SELF-CONTAINED image path (build_multi_func_cortex_m_elf, i.e. NO
;; --relocatable) the dispatch loads the function pointer from the contiguous
;; R11 table region — but R11 is the LINEAR-MEMORY base and NOTHING populates
;; that region in a self-contained image, so `ldr ip,[r11,idx*4]` reads
;; function pointers from linear-memory DATA (a silent miscompile). Until the
;; dedicated func-table fix (silicon-gated) lands, the self-contained path must
;; DECLINE this loudly (AFD-008) rather than emit the colliding dispatch.
;;
;; The `--relocatable` path (where a runtime places the table region at R11)
;; keeps emitting the guarded dispatch — see the #642/#650/#664/#676 oracles.
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
