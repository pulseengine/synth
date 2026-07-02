;; VCR-RA-001 (#242) — OPTIMIZED-PATH register-exhaustion spill repro.
;;
;; Ten distinct i32 values derived from the two params (so constant folding
;; cannot collapse them) are simultaneously live before a non-commutative
;; sub/xor/add fold consumes them. The optimized path's R4-R8 scratch pool
;; exhausts at the 6th live binop result:
;;
;;   * flag OFF (default): `alloc_i32_scratch` flags exhaustion and the whole
;;     function DECLINES to the direct selector (#496 — observable as
;;     `[recovery-stats] rung=spill` under SYNTH_RECOVERY_STATS=1).
;;   * SYNTH_SPILL_ON_EXHAUST=1: the allocation-time spill pre-step evicts the
;;     live vreg with the FARTHEST next use (Belady) to a frame slot, reloads
;;     it at its next use, and the function stays on the optimized path (no
;;     recovery rung fires).
;;
;; No register-amount shifts: WASM masks the amount mod 32, ARM LSL/LSR do
;; not, and this fixture must isolate ALLOCATION behaviour, not the (separate,
;; pre-existing) shift-mask semantics gap.
;;
;; Differential oracle:
;;   SYNTH_SPILL_ON_EXHAUST=1 synth compile scripts/repro/spill_on_exhaust_242.wat \
;;         -o /tmp/soe.elf --target cortex-m4
;;   python scripts/repro/spill_on_exhaust_242_differential.py /tmp/soe.elf
(module
  (func (export "hp") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add        ;; v1 = p0+p1
    local.get 0
    local.get 1
    i32.sub        ;; v2 = p0-p1
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
    i32.const 12345
    i32.add        ;; v7
    local.get 1
    i32.const 23130
    i32.xor        ;; v8
    local.get 0
    i32.const 77
    i32.sub        ;; v9
    local.get 1
    i32.const 999
    i32.add        ;; v10
    i32.sub        ;; v9 - v10
    i32.xor        ;; v8 ^ …
    i32.add        ;; v7 + …
    i32.sub        ;; v6 - …
    i32.xor        ;; v5 ^ …
    i32.add        ;; v4 + …
    i32.sub        ;; v3 - …
    i32.xor        ;; v2 ^ …
    i32.add))      ;; v1 + …
