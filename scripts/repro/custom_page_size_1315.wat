;; RQ-69-PAGESIZE (#1315, reported by gale): a memory whose DECLARED page size
;; is not the default 64 KiB. Before v0.69 this compiled with rc=0 and no
;; diagnostic on every path measured, and `__synth_mem_size_0` reported 65536
;; for a memory the module declares as ONE BYTE — the number an embedder
;; programs one MPU region from (#1145).
(module
  (memory $a 1 1 (pagesize 1))
  (func (export "ld") (param i32) (result i32) (i32.load $a (local.get 0))))
