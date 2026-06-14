;; #350 regression — ADD #imm lowering for out-of-range immediates.
;;
;; A static store with offset=70000 (> 0xFFF) forces the indexed-address path
;; `ADD ip, base, #70000`. Before the fix, `encode_thumb32_add_imm` returned
;; `Err("ADD immediate too large for single instruction")`, so this whole
;; function failed to compile (empty object). The encoder now lowers it to
;; `MOVW ip,#0x1170; MOVT ip,#0x0001; ADD.W ip, base, ip` (ip = base + 70000).
;;
;; Differential: scripts/repro/add_imm_large_differential.py stores a sentinel
;; at the large offset and reads it back; the result must match wasmtime.
(module
  (memory (export "mem") 2)
  (func (export "store_load_large") (param i32) (result i32)
    ;; mem[70000] = param ; return mem[70000]
    i32.const 0
    local.get 0
    i32.store offset=70000
    i32.const 0
    i32.load offset=70000))
