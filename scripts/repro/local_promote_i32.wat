;; VCR-RA local-promotion validation fixture (#390, epic #242).
;;
;; The structural gap to native parity is that the instruction selector lowers
;; every wasm local to a FRAME SLOT (`compute_local_layout` → ldr/str [sp,#off]).
;; The promotion lever keeps i32 locals in callee-saved registers (r4–r8) instead.
;; The frozen fixtures (control_step 2 slots, flight_seam 4) have register headroom
;; — promotion never overflows the pool and temps never collide with a promoted
;; reg there, so a differential on them proves NOTHING (the #193 non-vacuity trap).
;;
;; This fixture is built to EXPOSE the three promotion failure modes:
;;
;;  1. OVERFLOW-TO-FRAME — 8 declared non-param i32 locals (idx 2..9), all live
;;     simultaneously at the final fold. Only r4..r8 (5 regs) are promotion
;;     targets, so ≥3 locals MUST fall back to the frame. Exercises the
;;     promote-some / spill-rest split.
;;
;;  2. RESERVATION-UNDER-PRESSURE (#193 class) — the closing fold reads every
;;     local interleaved with arithmetic, so operand-stack temps are demanded
;;     WHILE the promoted locals are live. A temp allocator that hands out a
;;     promoted register clobbers a live local → wrong result. Non-commutative
;;     ops (sub/xor) make any operand-order or clobber bug observable.
;;
;;  3. PROMOTED-LOCAL-READ-BEFORE-WRITE GUARD — all 7 locals are written before
;;     any read (straight-line, so each defining set dominates every read), so
;;     promotion is sound. The differential harness pre-dirties r4..r8 AND the
;;     frame window with non-zero sentinels: a promotion that reads a local before
;;     its write (a wrong write-before-read analysis) leaks a sentinel into the
;;     result and diverges. (True zero-init of a NEVER-written local is a separate
;;     pre-existing miscompile — see read_before_write_local_zeroinit.wat — that
;;     promotion v1 declines by construction, not tested here.)
;;
;; Differential oracle (wasmtime ground truth vs unicorn on synth's ARM):
;;   synth compile scripts/repro/local_promote_i32.wat -o /tmp/lp.elf \
;;         --target cortex-m4 --relocatable
;;   /tmp/armv/bin/python scripts/repro/local_promote_i32_differential.py /tmp/lp.elf
;; Run flag-off (frame path) and flag-on (SYNTH_LOCAL_PROMOTE=1) — both must match.
(module
  (func (export "local_promote") (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32) ;; locals 2..8 (seven i32 locals)

    ;; Seed locals 2..8 from param-mixing expressions (every write dominates every
    ;; read — straight-line, so promotion v1's write-before-read guard accepts all).
    (local.set 2 (i32.add (local.get 0) (i32.const 1)))
    (local.set 3 (i32.sub (local.get 1) (local.get 0)))
    (local.set 4 (i32.xor (local.get 0) (local.get 1)))
    (local.set 5 (i32.mul (local.get 2) (i32.const 3)))
    (local.set 6 (i32.add (local.get 3) (local.get 4)))
    (local.set 7 (i32.sub (local.get 5) (local.get 6)))
    (local.set 8 (i32.add (local.get 0) (local.get 7)))

    ;; Closing fold: every local read interleaved with arithmetic so operand-stack
    ;; temps are live concurrently with the promoted locals (#193 pressure). 7 live
    ;; locals overflow the 5-reg r4..r8 pool → 2 spill to frame. Non-commutative
    ;; ops make any clobber / operand-order bug observable.
    (i32.add
      (i32.xor
        (i32.sub
          (i32.add
            (i32.mul (local.get 2) (local.get 3))
            (i32.sub (local.get 4) (local.get 5)))
          (i32.add
            (i32.xor (local.get 6) (local.get 7))
            (i32.sub (local.get 8) (local.get 2))))
        (i32.const 0x5a5a5a5a))
      (i32.mul (local.get 0) (local.get 1)))))
