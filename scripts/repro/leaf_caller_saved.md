# VCR-RA-002 scoping spike — leaf-function prologue shrink

**Issue:** #428 (the named dominant cycle residual) · **Epic:** #242 (VCR-*) ·
north-star #390
**Status:** SCOPING SPIKE (no codegen change — frozen-safe). The byte-changing
allocator change is the separate next gated step.

## The lever

On-target measurement: the dissolved hot path is now bounded by the
**6-register leaf prologue** — `push {r4-r8,lr}` / `pop {…,pc}`, ~12 cyc of pure
save/restore on a small leaf, the largest remaining cycle residual after
cmp→select + local-promotion + immediate-shift folding. A leaf never calls, so
caller-saved r0-r3 are free of clobber; if the whole leaf body stays off
callee-saved registers, `shrink_callee_saved_saves` drops the push entirely.

## What this spike establishes (and corrects)

The naive hypothesis — "make local **promotion** prefer caller-saved homes" — was
implemented and **empirically falsified** here. Two findings:

### 1. The pool change is necessary-but-insufficient (it's a JOINT allocation problem)
Promoting locals into caller-saved r1/r2/r3 was verified to work in isolation
(disasm: locals moved r4,r5,r6 → r1,r2,r3). But the prologue did **not** shrink:
the operand-stack **temps** still occupy r4-r7, so they keep the push alive. With
one param, the free caller-saved set is exactly {r1,r2,r3}; if locals claim all
three, temps are *forced* onto callee-saved — net-neutral or worse. Dropping the
push requires locals **and** temps to prefer caller-saved, spilling to callee-saved
only under combined pressure — then shrink fires. This is a joint
locals+temps coloring change, not a promotion-pool tweak.

### 2. It must live in the reallocator, not the selector (the measured path re-colors)
The non-relocatable path (what the host-link / native-pointer consumer compiles)
runs `select_with_stack` **then** `reallocate_function` + `shrink_callee_saved_saves`
(arm_backend.rs). The reallocator **re-colors** every straight-line segment over
`POOL=[r0..r8]`, so any caller-saved home the selector picks is **overwritten** —
a `compute_local_promotion` pool change is a no-op on this path (verified:
`SYNTH_NO_LOCAL_PROMOTE` on/off changes the bytes — structural — but a
selector-level reg *choice* does not survive realloc). The `--relocatable` path
skips the reallocator, so a selector change shows there but is insufficient (#1).

⇒ **VCR-RA-002 belongs in `reallocate_function` (liveness.rs):** for a leaf
segment, bias the colourer's `POOL` order toward caller-saved (r0-r3) so the body
touches no callee-saved reg unless pressure forces it; `shrink_callee_saved_saves`
then removes the now-dead `push {r4-r8}`. This is a #193/#220-class allocator
change — land flag-off, unicorn-differential the caller-saved homes (the
reservation correctness the leaf-only guarantee buys), then on-target gate.

## Fixture

`leaf_caller_saved.wat` — 1 param + 3 promotable i32 locals, low temp pressure; the
non-vacuity case (with 1 param, all 3 free caller-saved regs are consumed by
locals, exposing the temps-forced-to-callee-saved interaction). Neutral values.

## Adjacent finding (filed separately)

While measuring, the optimized/non-relocatable path was found to emit this
**exported** leaf clobbering callee-saved r4-r8 with `bx lr` and **no** push
(independent of promotion and of realloc/shrink; the `--relocatable` build is
correct). Potential AAPCS violation, differential-blind — **#470**. If exported
leaves must preserve callee-saved under synth's model, that bug outranks this perf
lever and changes its baseline.

## Next gated step (separate PR)
1. Flag-off leaf-aware caller-saved bias in `reallocate_function` (`SYNTH_LEAF_CALLER_SAVED`,
   default off ⇒ bit-identical).
2. Unicorn differential on `leaf_caller_saved.wat`: flag-off == flag-on == wasmtime,
   with r4-r8 pre-dirtied (the reservation/clobber gate).
3. On-target cycle gate, then default-on flip + re-freeze.
