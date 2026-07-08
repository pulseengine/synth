;; #377 — --safety-bounds software must be enforced on the OPTIMIZED codegen
;; path (not just the direct selector). Each export is a minimal dynamic-address
;; linear-memory access of one of the four optimized-path memory opcodes
;; (MemStore, MemLoad, MemStoreSubword, MemLoadSubword). All bodies are simple
;; i32 leaf functions so the optimized path (ir_to_arm) accepts them — the
;; whole point is to exercise THAT path; the same module compiled with
;; --no-optimize exercises the direct selector for path parity.
(module
  (memory (export "memory") 1)

  ;; i32.store: mem[a+4] = v   (static offset so the guard covers offset+size-1)
  (func (export "st") (param i32 i32)
    local.get 0
    local.get 1
    i32.store offset=4)

  ;; i32.load: return mem[a]
  (func (export "ld") (param i32) (result i32)
    local.get 0
    i32.load)

  ;; i32.store16: subword store
  (func (export "st16") (param i32 i32)
    local.get 0
    local.get 1
    i32.store16)

  ;; i32.load8_u: subword load
  (func (export "ld8") (param i32) (result i32)
    local.get 0
    i32.load8_u))
