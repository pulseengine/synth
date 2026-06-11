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

## Step 3 design decision (settled 2026-06-09, before any code)

Step 3 splits into two pieces with different power and different risk. They are
sequenced — 3a first, because it is bounded and delivers the measured wins; 3b
second, because only it can meet the acceptance criterion.

### 3a. Post-pass range re-allocation (bounded; lands first)

Re-allocate the **greedy physical stream** after selection: split it into value
ranges (`straight_line_value_ranges` — already landed), build interference over
*ranges* instead of physical registers, colour with the costed Chaitin pass
(step 2), and rewrite each range to its assigned register.

- **What it wins (already measured):** removes the spurious spills (flat_flight
  peak value-pressure = 9 = pool → 17 spills eliminable) and restores constant
  residency, which is what lets `apply_const_cse` fire >0 times.
- **What it cannot win:** the hard-fail sites. The selector fails *during
  emission*, before any post-pass runs — so 3a does not remove the exhaustion
  hard-fail and does not unlock the cost-gate reverts.
- **Machinery needed (no-regret — 3b consumes the same pieces):**
  `rename_def` (the def-side sibling of `rename_use`), `range_interference`
  (ranges → adjacency over vreg ids; ranges interfere iff
  `a.def < b.last_use && b.def < a.last_use`, plus co-defined ranges — the
  dies-at-birth boundary case is deliberately non-interfering so a consumer can
  reuse its operand's register, the in-place-select pattern), a Chaitin core
  generic over node id (the step-2 colourer refactored from `Reg` to any
  `Ord + Copy`), and `apply_range_coloring` (replay ranges, rename uses from the
  open-range map then defs from the at-this-index map).
- **Scope guard:** leaf, straight-line, fully-modeled segments only — the same
  scope every analysis in `liveness.rs` already declines outside of. Flag-gated
  default-off; bounds: bit-identical fixtures when off, measured spill/movw
  delta when on.

### 3b. Selector-side virtual temps (the hard-fail remover; lands second)

Teach `select_with_stack` to emit **virtual temp ids past the physical pool**
instead of hard-failing in `alloc_temp_safe`: when all of R0–R8 are pinned by
live stack values, hand out a virtual id (representation: keep `next_temp: u8`
but let indices ≥ 9 denote virtuals — no `Reg` enum change; the virtual ids
exist only between selection and allocation, and 3a's allocator+rewrite maps
them onto physical registers, spilling per step 4 where k-colouring fails).
Encoding is unreachable for virtual ids by construction: the allocate+rewrite
pass runs before the encoder and either assigns physical registers or spills.

- This — and only this — removes the exhaustion hard-fail, which is the
  VCR-RA-001 acceptance criterion ("a previously load-bearing greedy fix
  becomes revertable").
- Risk containment: virtual ids are emitted **only on the would-have-failed
  path** at first (the existing 9-register fast path stays byte-identical for
  every function that never exhausts), so all frozen fixtures are untouched by
  construction until the flag flips wider.

#### 3b-lite (landed first, 2026-06-11): spill-on-exhaustion retry — no virtual ids

The first 3b increment removes the *i32* exhaustion hard-fail without any
virtual-id plumbing, by reusing the #171 `StackVal::Spilled` machinery at the
exact moment the old code returned `Err`:

- `alloc_temp_or_spill` wraps `alloc_temp_safe`; on exhaustion **and only when
  `SpillState::spill_on_exhaustion` is set**, it spills the deepest
  register-resident stack value (`spill_deepest_reg`, LIFO ⇒ least likely
  consumed next) to an i64-spill-area slot and retries. The value reloads on
  pop/peek through the existing `Spilled` path.
- The mode is set by the **backend retry**: `compile_wasm_to_arm` runs the
  unmodified first pass; only if it fails with the specific exhaustion `Err`
  does it re-select with a fresh selector and the flag on (which also forces
  `compute_local_layout` to reserve the spill area, since the prologue is
  emitted before any spill can be predicted). Bit-identity for everything that
  compiles today is therefore **structural**, not measured-after-the-fact.
- Honest bound (the hard-fail shrinks, doesn't vanish): `I64_SPILL_SLOTS = 8`
  can still exhaust (now surfacing the slot-pool `Err`), and the i64
  consecutive-pair (`~609`) and call-result callee-saved (`~4765`) sites keep
  their hard-fails for this increment.
- Oracle: `scripts/repro/high_pressure_i32.wat` (hard-fails on pre-3b main,
  compiles + unicorn-vs-wasmtime differential PASS with the retry) + the three
  frozen fixtures sha256-identical against a main-built compiler.

Full 3b (virtual ids ≥ 9 mapped by the 3a allocator) remains the path to
allocator-*chosen* spills; 3b-lite only guarantees forward progress.

### Why not pure selector-side vregs from the start

Rewriting the selector to emit vregs for *every* temp invalidates the byte-level
behavior of every function at once — the opposite of the per-function,
differential-gated migration this plan requires. 3a + exhaustion-only-3b keeps
the frozen world the default at every merge.
