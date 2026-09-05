;; RQ-62-MEMISOLATE (#1145) — gale's two-tenant isolation fixture, verbatim
;; shape from the issue: two linear memories, one per tenant, each with its
;; own init data. Tenant A owns memory 0 (the R11 base region); tenant B owns
;; memory 1 (the linker-placed `.synth.wasm_mem_1` region, addressed via
;; `__synth_wasm_data_1` / `__synth_mem_base_1`).
;;
;; The kill-criterion this fixture exists to execute (gale's, adopted
;; verbatim on #1145): "a two-tenant image where tenant A writes outside its
;; region and the write lands in tenant B's memory instead of faulting."
;; `write_a` is tenant A's guardless store — with the two regions placed
;; adjacent and no MPU, `write_a(0x10000 + i, v)` lands at tenant B's byte i,
;; observable via `read_b(i)`. That is the RED leg
;; (scripts/repro/mem_isolation_red_1145.py). The GREEN leg (the same write
;; FAULTS once the embedder programs one MPU region per memory from the
;; #1145 region table) needs an MPU-modeling venue — gale's Renode M4
;; platform or the STM32G474RE bench — and is theirs to execute.
(module
  (memory $a 1 1)
  (memory $b 1 1)
  (data $da (memory $a) (i32.const 0) "tenantA")
  (data $db (memory $b) (i32.const 0) "tenantB")
  (func (export "read_a") (param i32) (result i32) (i32.load8_u $a (local.get 0)))
  (func (export "read_b") (param i32) (result i32) (i32.load8_u $b (local.get 0)))
  (func (export "write_a") (param i32 i32) (i32.store8 $a (local.get 0) (local.get 1)))
)
