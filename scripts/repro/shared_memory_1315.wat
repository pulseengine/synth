;; RQ-69-PAGESIZE (#1315) sweep, second member: a SHARED memory. Before v0.69
;; this compiled rc=0 with no diagnostic — synth emits no synchronization and
;; declines every atomic operator, so the sharing the declaration promises
;; cannot hold. `WasmMemory.shared` had exactly one reader outside the decoder:
;; a copy into the frontend's parallel struct.
(module
  (memory 1 1 shared)
  (func (export "ld") (param i32) (result i32) (i32.load (local.get 0))))
