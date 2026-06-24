# The register-exhaustion recovery ladder — the patch surface VCR-RA must subsume

**Epic:** #242 (VCR-* — replace the patch-accreting selector+allocator with a
verified one) · **Status:** ANALYSIS / roadmap artifact, no codegen change.

The north star (#242) is to replace synth's single-pass hand-written register
allocator with one that is correct by construction. The clearest measure of *what
that allocator must do* is the **failure-recovery ladder** the current allocator
has accreted: each rung is a retry that catches a register-exhaustion the previous
attempt couldn't, added reactively as a real function hit the wall. This file maps
that ladder so the verified replacement has an explicit list of failure modes to
**subsume** (not re-implement as retries).

All rungs live in `crates/synth-backend/src/arm_backend.rs` — the `select_direct`
recovery ladder over `select_direct_attempt(spill, param_backing, promote)`. Each
rung is reached **only** when the previous attempt returned a recoverable
`register exhaustion` Err, so a function that compiles on the base attempt is
untouched by every later rung (this is why each rung was bit-identical-by-
construction when it landed, and why the frozen byte gate stays green).

## The ladder (in order)

| # | Rung | Added by | Catches | Mechanism |
|---|------|----------|---------|-----------|
| 0 | base attempt | — | (nothing — the common case) | `select_with_stack`, promotion on |
| 1 | optimized→direct decline | #120 | constructs the IR can't lower (scalar f32/f64, …) | optimized path returns `Err`, fall back to the direct selector |
| 2 | spill-on-exhaustion | #242 (3b-lite) | i32 `all allocatable registers are live on the stack` | reserve a spill area, spill the deepest stack value when the pool is full |
| 3 | param frame-backing | #204 / #242 | i64 `no consecutive pair of free registers` | frame-back params (#204) so they stop pinning R0-R3; spill kept on |
| 4 | promotion-off fallback | #474 / #475 | *any* `register exhaustion` that promotion **caused** | re-run the whole ladder with local promotion off (the v0.12.0 frame-slot lowering) |

Rung 4 is the newest and the most telling for #242: local promotion (v0.14.0) is
an *optimization* that pins r4-r8 for locals, **halving** the operand-stack temp
pool — so on a dense function it can turn a working compile into a hard exhaustion.
The fix is a retry that drops the optimization. A verified allocator would never
need it: it would either color the function with the locals in registers, or spill
them — never fail. Rung 4 existing at all is a direct symptom of the single-pass
allocator the north star replaces.

## Which fixtures exercise which rung

Only rung 4 is **confirmed load-bearing** here (the `promotion_exhaustion_fallback`
fixture fails to compile without its rung and compiles with it — verified in the
#475 regression test). The rest are by *design intent* (the fixture/name + the
issue that introduced the rung); attributing a rung precisely needs the per-rung
counter noted below — this table is the hypothesis that counter would confirm.

| fixture | rung (status) |
|---|---|
| `control_step`, `flight_seam*`, most repros | 0 base (compile cleanly) |
| `high_pressure_i32` | 2 spill — *by design, unconfirmed* |
| `high_pressure_i64` | 3 param frame-backing — *by design, unconfirmed* |
| `promotion_exhaustion_fallback` (#475) | 4 promotion-off — **confirmed** |

## North-star implication

A correct-by-construction allocator with integrated spilling collapses rungs 2-4
into "allocation succeeds": no `register exhaustion` Err to retry, so no ladder.
Rung 1 (decline on unlowerable IR) is a *coverage* gap, not an allocation failure,
and stays until the selector DSL (`VCR-SEL-001`) covers those constructs. So the
VCR-RA acceptance bar includes: **every function in this corpus that today needs
rungs 2-4 must allocate on the first pass under the verified allocator**, with the
ladder retained only as a defense-in-depth assertion that should never fire.
`SYNTH_REALLOC_STATS` already reports per-function counters for the *range-realloc*
pass (segments / reallocated / declined / needs-spill) on the optimized path;
the analogous next measurement is a per-rung counter on **this** `select_direct`
ladder (how often each rung fires across a real dissolved corpus = the size of the
surface VCR-RA must absorb). That instrumentation is env-gated logging only
(byte-identical output), so it stays frozen-safe.
