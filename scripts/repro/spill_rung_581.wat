;; #581 — DIRECT-selector spill-rung minimal repro: a const fold deleting a
;; spill store.
;;
;; Shape: seven simultaneously-live i32 binop results (R2..R8) + p0 pushed +
;; p1 reserved to its late last-read pin all 9 allocatable registers, so the
;; base pass hard-fails with the exhaustion Err and the backend retries on the
;; spill rung (VCR-RA-001 3b-lite). On the retry, materializing `i32.const 77`
;; spills the deepest live value (v1) to a frame slot — the spill STR is tagged
;; with the const's source_line. The following `i32.sub` then folds the const
;; to `SUB rd, rn, #77` (#253) and drops the materialization BY SOURCE_LINE,
;; which pre-fix also deleted the spill store: v1's stack entry stayed
;; `Spilled` and its final reload read a never-written slot — silent wrong
;; value on the shipped `--relocatable`/direct path.
;;
;; hp(1,2): wasmtime 0x4f, pre-fix synth returned frame garbage.
;;
;; Differential oracle:
;;   python scripts/repro/spill_rung_581_differential.py
(module
  (func (export "hp") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add        ;; v1 = p0+p1  (the spill victim)
    local.get 0
    local.get 1
    i32.sub        ;; v2
    local.get 0
    local.get 1
    i32.xor        ;; v3
    local.get 0
    local.get 1
    i32.or         ;; v4
    local.get 0
    local.get 1
    i32.and        ;; v5
    local.get 0
    local.get 1
    i32.mul        ;; v6
    local.get 0
    local.get 1
    i32.add        ;; v7
    local.get 0
    i32.const 77
    i32.sub        ;; v8 = p0-77 — the fold whose spill store must survive
    i32.sub        ;; v7 - v8
    i32.xor        ;; v6 ^ …
    i32.add        ;; v5 + …
    i32.sub        ;; v4 - …
    i32.xor        ;; v3 ^ …
    i32.add        ;; v2 + …
    i32.sub        ;; v1 - …   <- pre-fix: reloads the never-stored slot
    local.get 1
    i32.add))      ;; + p1 (keeps R1 reserved through the const materialization)
