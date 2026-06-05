# VCR-RA-001 — Allocator wiring design

Status: **design** (no code yet). Tracks `VCR-RA-001` in
`artifacts/verified-codegen-roadmap.yaml`, epic #242.

## Why this document

The register-allocator **analysis + decision layer** is merged and lives in
`crates/synth-synthesis/src/liveness.rs`, all of it pure and unwired:

| Primitive | What it computes |
|-----------|------------------|
| `reg_effect` | per-instruction def/use |
| `cfg_liveness` (#268) | per-block live-in/live-out (backward dataflow fixpoint) |
| `interference_graph` (#269) | "cannot share a physical register" graph |
| `color_graph` (#270) | Chaitin/Briggs k-colouring with optimistic spill |
| `color_graph_precolored` (#271) | colouring with reserved/ABI-pinned registers |

Those five landed **side-by-side and bit-identical-by-construction** precisely
*because* nothing called them. The wiring is the opposite: it makes the
allocator drive codegen, so it **changes emitted bytes**. That crosses the line
from "unwired ⇒ safe" into "needs the full differential oracle gate." This note
plans that crossing before any of it is written, so the consequential step is
sequenced, gated, and reversible — not improvised.

## What the wiring replaces

The single-pass allocator hard-fails on register exhaustion instead of spilling.
The failure sites in `instruction_selector.rs` (the symptoms VCR-RA-001 exists to
cure):

- `~362` "all allocatable registers are live on the stack"
- `~388` / `~4699` "i64 spill-slot pool exhausted"
- `~609` "no consecutive pair of free registers for i64"
- `~4765` "no free callee-saved register to hold a call result"

These hard-fails are what force the reciprocal-mult cost-gate (#209/v0.11.20) and
the 2-temp UMULL path. The acceptance criterion for VCR-RA-001 is that, once the
allocator spills under pressure, **one** of those greedy fixes becomes
revert-able with the full differential staying bit-identical and cycles
equal-or-better.

## Hard invariant (frozen behaviour)

Every sub-step below keeps the differential fixtures **bit-identical**:
`control_step 0x00210A55`, flat+inlined `flight_algo 0x07FDF307`, `divseam`
sign vectors. A sub-step that cannot stay bit-identical does not merge. The
wiring is therefore introduced **behind a flag, defaulting off**, and only flips
on once a sub-step is differentially proven a no-op or a measured improvement.

## Sequenced sub-steps (each its own oracle-gated PR)

1. **Allocation verifier (oracle, still unwired).**
   `verify_allocation(graph, assignment) -> Result<(), Conflict>`: every pair of
   interfering registers has distinct colours, every reserved register is
   respected. This is the *self-check* the wired allocator runs on its own output
   before emitting — build it first so later steps are gated by it. Pure, unwired,
   bit-identical by construction. *(This is the one remaining genuinely-bounded,
   safe piece; it can land like #268–#271.)*

2. **Spill-cost ranking.** When `color_graph` returns `Spilled`, choose which
   node to actually spill by cost (≈ uses / degree — Chaitin's metric) rather
   than the current degree-only heuristic. Pure, unwired.

3. **Virtual-register selector output (the big structural change).** Teach
   `select_with_stack` to emit *virtual* registers for temps instead of eagerly
   assigning physical R0–R8. This is the largest diff and the riskiest; it must
   be **flag-gated and default-off**, with the existing physical path untouched
   when the flag is off (so all fixtures stay bit-identical by default).

4. **Spill-code insertion.** For each spilled value, materialise a stack slot and
   insert store-after-def / reload-before-use. Reuses the existing i64 spill-slot
   frame machinery. Gated by step 1's verifier.

5. **Wire-in + flip.** Map colours → physical registers honouring the reserved
   set via `color_graph_precolored` (R9 globals / R10 mem-size / R11 mem-base /
   R12 IP-scratch pinned out of the pool; R0–R3 ABI arg pins). Run on a function,
   `verify_allocation`, then emit. Flip the flag on **per-function** only where
   the differential proves bit-identical-or-better; leave the old path for the
   rest. Remove a hard-fail site only once its functions all route through the
   allocator green.

## Oracle gate (every step from 3 on)

- `cargo test --workspace --exclude synth-verify` green.
- The three differential fixtures **bit-identical** (`scripts/repro/*_differential.py`
  on `/tmp/armv`, or `cmp -s` of the compiled `.o` vs `main` for a behaviour-frozen
  step).
- `i64_lowering` + `encoder_no_panic` fuzz smoke green.
- For any step that flips the flag on: a **measured** size/cycle delta, not just
  "still passes" — per the audit rule that a change with no measured delta and a
  green oracle does not merge.

## Non-goals (for VCR-RA-001)

Coalescing, live-range splitting, and rematerialisation are regalloc2-class
refinements deferred until the basic spill-capable allocator is wired and proven.
The first win is simply: **stop hard-failing**, so the cost-gates become
revert-able.
