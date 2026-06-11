;; #326 — register exhaustion on an arg-move CYCLE under callee-saved pressure.
;;
;; gale's dissolved `z_impl_k_mutex_unlock` stopped compiling on v0.11.36:
;; the #311 call-result pair tagging legitimately keeps i64 register PAIRS
;; live across the surrounding code, so at a later call whose argument
;; marshalling contains a genuine register cycle (two sources that must SWAP
;; into r0/r1), `emit_arg_moves` demanded a free callee-saved scratch from
;; R4-R8 — all pinned — and the `Err` propagated:
;;
;;   register exhaustion: no free callee-saved register to hold a call
;;   result while reloading a preserved param
;;
;; This module reproduces that exact shape without gale's firmware:
;;   * three i64 values stay live ON the operand stack across the calls,
;;     occupying the pairs (r3,r4), (r5,r6), (r7,r8) — every callee-saved
;;     register R4-R8 is pinned, exactly the #311 pressure class;
;;   * `$main`'s param is reloaded into r1, then `$get32`'s result lands in
;;     r0 ON TOP of it — so `$swap2(param, result)` needs arg0: r1->r0 and
;;     arg1: r0->r1, a genuine 2-cycle with no free callee-saved scratch.
;;
;; v0.11.36..v0.11.39 fail compile-time with the message above (the 3b-lite
;; retry covers a different exhaustion site). Fixed by routing the marshal
;; through the parallel-move resolver (synth_synthesis::parallel_move), which
;; breaks the cycle via ONE stack slot when no scratch register exists:
;;   str r0, [sp, #slot] ; mov r0, r1 ; ldr r1, [sp, #slot]
;;
;; Differential: scripts/repro/mutex_pressure_differential.py
;;   (wasmtime ground truth vs unicorn on the synth ELF, internal BLs
;;    resolved like u64_unpack_differential.py).
;;
;; Compile (fails on v0.11.36..39, compiles after the #326 fix):
;;   synth compile scripts/repro/mutex_pressure.wat -o /tmp/mp.elf \
;;         --target cortex-m4 --all-exports --relocatable
(module
  ;; i32-returning kernel-primitive stand-in: its result arrives in r0 on
  ;; top of the already-live marshal source — one half of the cycle.
  (func $get32 (result i32)
    i32.const 37)

  ;; Argument-order-sensitive callee: swap2(a, b) = 2*a - b, so a marshal
  ;; that swaps (or clobbers) its arguments is numerically visible.
  (func $swap2 (param i32 i32) (result i32)
    local.get 0
    i32.const 2
    i32.mul
    local.get 1
    i32.sub)

  (func $main (export "main") (param i32) (result i64)
    ;; Walk the temp allocator past r1/r2 so the i64 pairs land on
    ;; (r3,r4), (r5,r6), (r7,r8) — pinning all of R4-R8.
    i32.const 1
    drop
    i32.const 2
    drop
    ;; Three i64 values that stay live across both calls (#311 pressure).
    i64.const 0x1111111100000007  ;; pair (r3,r4)
    i64.const 0x2222222200000005  ;; pair (r5,r6)
    i64.const 0x4444444400000003  ;; pair (r7,r8)
    ;; Advance the allocator off r0 so the preserved param reloads into r1.
    i32.const 3
    drop
    local.get 0                   ;; a -> r1 (arg0 of $swap2)
    call $get32                   ;; result -> r0 (arg1 of $swap2)
    ;; Marshal cycle: arg0 r1->r0, arg1 r0->r1 — with R4-R8 all pinned.
    call $swap2
    ;; Fold everything so the i64 values were genuinely live across the calls.
    i64.extend_i32_u
    i64.add
    i64.add
    i64.add))
