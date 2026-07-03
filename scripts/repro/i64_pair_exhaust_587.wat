;; #587 (VCR-RA, #242) — OPTIMIZED-PATH i64 register-PAIR exhaustion repro.
;;
;; The i64 sibling of spill_on_exhaust_242.wat. Five i64 values are
;; simultaneously live before the first fold: the optimized path's
;; `alloc_i64_pair` has exactly FOUR even-aligned candidate pairs
;; ((R4,R5) (R6,R7) (R8,R9) (R10,R11) — and its map never frees dead vregs),
;; so the fifth constant exhausts the pair pool:
;;
;;   * flag OFF (default): `alloc_i64_pair` flags exhaustion and the whole
;;     function DECLINES to the direct selector (#496 — a `[recovery-stats]`
;;     rung line under SYNTH_RECOVERY_STATS=1), which compiles it via the
;;     #171/#325 pair-spill machinery.
;;   * SYNTH_SPILL_ON_EXHAUST=1: the pair-aware Belady pre-step evicts the
;;     coherent PAIR (or two singles) whose displaced values have the farthest
;;     soonest-next-use into an 8-byte-aligned slot pair, reloads it into a
;;     legal even pair at its next use, and the function stays on the
;;     optimized path (no recovery rung fires).
;;
;; The fold mixes non-commutative ops (sub/xor) so an operand-order, reload,
;; or half-swap bug changes the result; the two i32 params enter late via
;; extend_i32_u so the reload path (not just eviction) is exercised. No i64
;; shifts (out of the modeled scope — their encoders clobber the amount pair
;; in place) and no i64 params (#503/#518 territory).
;;
;; Differential oracle:
;;   SYNTH_SPILL_ON_EXHAUST=1 synth compile scripts/repro/i64_pair_exhaust_587.wat \
;;         -o /tmp/pe587.elf --target cortex-m4
;;   python scripts/repro/i64_pair_exhaust_587_differential.py /tmp/pe587.elf
(module
  (func (export "hp64") (param i32 i32) (result i64)
    i64.const 0x1111111122222222   ;; A
    i64.const 0x3333333344444444   ;; B
    i64.const 0x5555555566666666   ;; C
    i64.const 0x7777777788888888   ;; D
    i64.const 0x0123456789abcdef   ;; E — 5th live pair: exhaustion HERE
    i64.add        ;; D+E
    i64.sub        ;; C-(D+E)
    i64.xor        ;; B^...
    i64.add        ;; A+...  (A was evicted first: farthest next use)
    local.get 0
    i64.extend_i32_u
    i64.sub
    local.get 1
    i64.extend_i32_u
    i64.xor))
