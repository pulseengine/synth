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

## Which fixtures exercise which rung — MEASURED

`SYNTH_RECOVERY_STATS=1` makes `select_direct` log the rung that produced each
function's code (`[recovery-stats] rung=… result=…`). Logging only — emitted bytes
are unchanged (frozen gate green). Measured across the whole `scripts/repro/*.wat`
corpus (`--target cortex-m4 --relocatable --all-exports`):

| fixture (function) | rung (measured) |
|---|---|
| most of the ~49-fixture corpus | **base** — compile on the first attempt |
| `high_pressure_i32` | **spill** (rung 2) |
| `control_step.wasm` (the 0x00210A55 frozen fixture) | **spill** (rung 2) |
| `msgq_put_359.wasm` (1 of its 5 functions) | **spill** (rung 2) |
| `high_pressure_i64` | **param-backing** (rung 3) |
| `promotion_exhaustion_fallback` (#475) | **promotion-off** then spill (rung 4 → 2) |

So across the corpus the recovery ladder fires for **~5 functions** — that is the
entire local failure surface. The notable one is `control_step`: the canonical
frozen fixture is itself produced via the **spill** rung, i.e. it sits right at the
register-pressure edge (a base-attempt allocator would have *failed* it — the spill
rung is load-bearing for a shipped fixture, not just stress tests). `local_promote_*`,
`mutex_pressure`, the `flight_seam*` / `native_pointer_*` families, etc. all compile
on the base attempt. The classification is asserted by the CI test
`recovery_stats_rung_classification_242`.

## North-star implication

A correct-by-construction allocator with integrated spilling collapses rungs 2-4
into "allocation succeeds": no `register exhaustion` Err to retry, so no ladder.
Rung 1 (decline on unlowerable IR) is a *coverage* gap, not an allocation failure,
and stays until the selector DSL (`VCR-SEL-001`) covers those constructs. So the
VCR-RA acceptance bar includes: **every function in this corpus that today needs
rungs 2-4 must allocate on the first pass under the verified allocator**, with the
ladder retained only as a defense-in-depth assertion that should never fire. The
per-rung counter that quantifies this surface is now wired (`SYNTH_RECOVERY_STATS`,
above) — env-gated logging only (byte-identical, frozen-safe). On the local corpus
the surface is ~5 functions (incl. the shipped `control_step` fixture); the same
counter run over a real dissolved workload measures the production surface VCR-RA
must absorb. (`SYNTH_REALLOC_STATS` is the analogous counter for the separate
range-realloc pass on the optimized path.)

## Does the shadow allocator subsume the ladder? — MEASURED

`SYNTH_SHADOW_ALLOC=1` runs the graph-colouring allocator (`allocate_function`, the
VCR-RA prototype) on the selected stream and logs whether it colours within the
R0-R8 pool, the **true value-pressure** (one node per value, not per reused physical
register), and remat opportunities — measure-only, byte-identical. Running it on the
ladder-firing functions answers the acceptance question directly:

| function | recovery rung | shadow allocator | verdict |
|---|---|---|---|
| `control_step.wasm` | spill | would spill R3, but **peak value-pressure 8 ≤ 9** | **spurious spill — VCR-RA subsumes it** |
| `high_pressure_i32` | spill | would spill R1, **peak 10 > 9** | genuine — VCR-RA spills too |
| `promotion_exhaustion_fallback` | promotion-off→spill | would spill R5, **peak 10 > 9** | genuine — VCR-RA spills too |
| `high_pressure_i64` | param-backing | declined (i64 unmodeled) | Track-A model gap |
| `msgq_put_359.wasm` | spill | declined (calls/i64) | Track-A model gap |

So the single-pass allocator's spill is **not always real pressure**: `control_step`
— a *shipped* fixture — spills only as a physical-register artifact (peak 8 fits the
9-wide pool once values are allocated virtually), exactly the case a verified
allocator removes. The genuine floor in this corpus is the **peak-10** functions
(`high_pressure_i32`, `promotion_exhaustion_fallback`): there VCR-RA must spill too,
so its acceptance bar there is "spill no *worse* than the ladder," not "no spill."
The i64/call functions are the shadow model's current scope gap (it declines them) —
a `VCR-RA` modelling TODO, not an allocation result. The spurious-vs-genuine split is
asserted by `shadow_alloc_spurious_vs_genuine_spill_242`.
