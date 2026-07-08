# VCR-VER-001 — the program gate, attempted and measured

**Epic:** #242 · **Artifact:** `artifacts/verified-codegen-roadmap.yaml` `VCR-VER-001`
· **Status:** GATE DEMONSTRATED (status → `implemented`); the #496 flip stays HELD
· **Derived:** 2026-07-08 at `f8c6826`, frozen anchors 10/10 green at baseline.

The gate is the North-Star program's falsification test: *a previously
load-bearing greedy fix becomes revertable — patch-accretion reverses.*
Pass-criteria (roadmap): at least one previously load-bearing greedy-fix removed
with the full differential bit-identical and cycles equal-or-better; no new
cost-gate introduced.

## Candidate survey

| # | Greedy fix | What it protected | Verdict |
|---|-----------|-------------------|---------|
| 1 | v0.11.20 reciprocal-mult **cost-gate** (UDIV fallback when UMULL scratch could not be allocated) | v0.11.19 hard-fail: gale's `control_step` 4× const `div_u` exhausted the R0-R8 pool → compile error | **REVERSED — deleted outright (PR #322)**; meets the pass-criteria literally (below) |
| 2 | #496 **decline-on-exhaustion** (optimized path hard-declines to the direct selector when its R4-R8 scratch / i64-pair pool exhausts) | #496 silent miscompile: the pre-fix R12/IP last-resort borrow collided with the encoder's indexed-load scratch (#212 class) — `control_step` execution-faulted, `flight_seam_flat` computed wrong values | **REVERTABLE, flag-off** via `SYNTH_SPILL_ON_EXHAUST` (#580); correctness criteria all hold; **cycles criterion FAILS on i32 shapes** → flip stays held (missing capability named below) |
| 3 | `// #NNN` guards in `optimizer_bridge.rs` (#377/#382/#483/#543 …) | Encoding-range, bounds-guard and volatile-window soundness — not allocation greediness | Not candidates: these are correctness features with their own oracles, not pressure heuristics the allocator subsumes |

## Demonstration 1 — the cost-gate deletion (PR #322) meets the pass-criteria

The v0.11.20 UDIV fallback was load-bearing when added (without it v0.11.19
failed to compile `control_step`). Two things made it removable, both verified
in #322 and re-verified today:

1. **The case it guarded is covered by Track-A machinery**: the #320
   spill-on-exhaustion retry recovers UMULL-scratch exhaustion
   (`alloc_temp_or_spill` in `instruction_selector.rs`); the original red case
   is pinned green by `test_209_multi_const_div_does_not_exhaust`.
2. **Full differential bit-identical**: the fallback was dead on the entire
   frozen suite — deletion was byte-identical (±0 B), hence cycles trivially
   equal. No new cost-gate has been introduced since (the reciprocal-multiply
   path at `instruction_selector.rs:~7412` has no profitability guard).

That is the roadmap's pass-criteria, satisfied exactly: removed (not
flag-gated), differential bit-identical, cycles equal, no new cost-gate.

## Demonstration 2 — the #496 decline is revertable; the flip is held on measured cycles

Reversal flag: `SYNTH_SPILL_ON_EXHAUST` (#580; default **off** = the greedy fix
stays). Flag-on, exhaustion routes through the allocation-time Belady spill
(pair-aware since #587) instead of declining — strictly more capable: fewer
functions leave the optimized path, and the exhaustion class that #496 turned
from silent-miscompile into loud-decline becomes "spill and continue".

All numbers derived on `f8c6826`, default path (`--target cortex-m4
--all-exports`, no `--relocatable`), synth debug build.

### (a) The original red case stays green with the reversal active

* `r12_spill_496_differential.py` with `SYNTH_SPILL_ON_EXHAUST=1`: **PASS** —
  the two original silicon victims execute bit-for-bit like wasmtime,
  including the frozen result anchors `control_step(3000,50,40,0) =
  0x00210A55` and `flight_algo = 0x07FDF307` (13 + 1 vectors).
* `spill_on_exhaust_242_differential.py` on the flag-on bytes: **PASS** (8/8).
* `i64_pair_exhaust_587_differential.py` on the flag-on bytes: **PASS** (8/8).
* `i64_spill_pool_587_differential.py`, `spill_rung_581_differential.py`
  flag-on: **PASS**.
* `signed_div_const` + `high_pressure_i32` flag-on bytes execution-verified
  vs wasmtime under unicorn (6 and 8 vectors): **OK**.

### (b) Differential suite + per-function bytes/declines

Frozen pinned goldens (`frozen_codegen_bytes.rs`, `--relocatable`): the flag
acts on the optimized path only — **10/10 green in both flag states**.
Default-path anchor fixtures are byte-identical flag-on (locked by the new
`vcr_ver_001_gate_242.rs`). Per-function measurement over the pressure corpus:

| fixture (default path) | declines off→on | .text B off→on | weighted cycle proxy* off→on |
|---|---|---|---|
| `control_step.wasm` | 1 → 1 (rung=spill, non-exhaustion Err) | 474 = 474 | identical bytes |
| `flight_seam.wasm` | 3 → 3 (rung=base) | 886 = 886 | identical bytes |
| `flight_seam_flat.wasm` | 3 → 3 (rung=base) | 1026 = 1026 | identical bytes |
| `spill_on_exhaust_242.wat` | 1 → **0** | 264 → 296 | 368 → 480 (**+30.4 %**) |
| `i64_pair_exhaust_587.wat` | 1 → **0** | 348 = 348 | 584 → 552 (**−5.5 %**) |
| `i64_spill_pool_587.wat` | 1 → **0** | 912 → 930 | 2208 → 2176 (**−1.4 %**) |
| `spill_rung_581.wat` | 1 → **0** | 228 → 254 | 272 → 360 (**+32.4 %**) |
| `high_pressure_i32.wat` | 1 → **0** | 274 → 272 | 400 → 432 (**+8.0 %**) |
| `signed_div_const.wasm` | 1 → **0** | 194 → 236 (fn 34 → 76) | 90 → 198 (**+120 %**) |
| `high_pressure_i64.wat` | 1 → 1 (rung=param-backing, out of scope) | 350 = 350 | identical bytes |

\* dynamic instructions + data-memory accesses under unicorn (first-order M4:
LDR/STR ≈ 2 cyc), summed over the differential vectors; every run
execution-matched wasmtime.

Total declines across the corpus: **14 → 8**. Everything pinned is
bit-identical; every changed function is execution-proven.

### (c) Frozen anchors + refreeze ritual

Flag OFF (the default this state ships in): frozen byte gate **10/10**, no code
change — trivially bit-identical. Flag ON changes bytes **only** on unpinned
pressure fixtures; per the refreeze ritual the result differentials were re-run
on the new bytes (all PASS, above) and the goldens were **not** re-pinned — the
flip is a separate later PR.

### The verdict on criterion "cycles equal-or-better" — and the missing capability

The reversal is **correctness-complete but performance-regressive on i32
shapes**: +8 % to +120 % on the weighted proxy, improving only the i64-pair
shapes. The #496 decline therefore remains load-bearing *for cycles, not for
correctness*. The named missing capability (`VCR-RA` follow-on):

> **Post-exhaustion code quality on the optimized path.** The allocation-time
> Belady spill emits more stack traffic than the direct selector's
> operand-stack spill on i32-dense shapes (`spill_on_exhaust_242`: 16 → 22
> memory accesses per call), and an optimized-path function that only compiles
> *because* of the spill lever can be worse than the direct lowering of the
> same function (`signed_div_const`: 34 → 76 B, 90 → 198 weighted — the
> optimized path's const-div lowering under pressure loses to the direct
> selector's strength-reduced form). Until spill placement/coalescing (or
> running the frame-slot-DCE/stack-fwd family over allocation-time slots)
> closes that gap — measured on gale's G474RE per the #580 hold — the flip
> would trade declines for cycles.

## Reproduce

```sh
cargo test -p synth-cli --test frozen_codegen_bytes --test vcr_ver_001_gate_242 \
    --test spill_on_exhaust_242 --test i64_pair_exhaust_587
# execution evidence (needs wasmtime + unicorn + pyelftools):
SYNTH=target/debug/synth SYNTH_SPILL_ON_EXHAUST=1 \
    python scripts/repro/r12_spill_496_differential.py
SYNTH_SPILL_ON_EXHAUST=1 target/debug/synth compile \
    scripts/repro/spill_on_exhaust_242.wat -o /tmp/soe.elf --target cortex-m4
python scripts/repro/spill_on_exhaust_242_differential.py /tmp/soe.elf
```

## Post-exhaustion code quality — the named capability, built (follow-up PR)

The missing capability named above ("post-exhaustion code quality on the
optimized path") is now partially closed. Root cause of the unreached slots,
found by construction analysis + disassembly of the flag-on streams:

1. **`eliminate_dead_frame_stores` structurally cannot fire** on allocation-
   time slots: `next_spill_offset` is fresh-monotonic (every eviction gets a
   new slot), and the pass proves deadness ONLY via a later same-slot
   overwrite (#515's overwrite-only discipline). No overwrite can exist.
2. **`forward_stack_reloads` structurally cannot fire**: the Belady eviction
   store's source register is redefined immediately after the store (that is
   WHY the value was evicted), so the forwarding shape never survives.
3. **`spill_rechoice_segment` declined every rename**: the bridge draws
   scratch from R4-R8 only, so R2/R3 are never touched again after a
   segment — and `rename_kill_def`'s segment-local deadness proof rejects a
   register with no later in-segment def as "possibly live-out". The one
   fact that resolves it (nothing past `bx lr` can read R2/R3) is function-
   level, invisible to the segment pass. A second blocker hid behind the
   first: guard (a)'s exact `SegmentTrace` equality rejects any rename onto a
   fresh register (its exit entry differs), and guard (b) rejected
   count-neutral `ldr`→`mov` folds.
4. **`signed_div_const` was a different bug**: the optimized path emitted the
   div-by-zero + INT_MIN/−1 trap guards even for a constant divisor (the
   direct selector elides them since v0.11.17), plus a dead spill store the
   unread-store sweep could not reach past the guards' resolved branches.

Extensions, ALL scoped to functions the #580 machinery actually shaped
(`OptimizerBridge::spill_on_exhaust_fired`, so a flag-on compile leaves every
untouched function byte-identical — locked by `vcr_ver_001_gate_242` and the
frozen suite run in BOTH flag states):

- `scratch_dead_at` (function-level R2/R3 exit-deadness, conservative at any
  branch/call/unmodeled op) feeding `rename_kill_def`; trace equality taken
  modulo provably-dead-at-exit exit entries; per-pair pool-pressure commit;
  count-neutral folds accepted when bytes strictly shrink.
- Constant REMATERIALIZATION in `spill_forward_segment`: a reload of a slot
  provably holding a single-instruction constant (`mov`/`movw`; `movt`'s RMW
  kills the shape — the #582-class discipline) becomes the retargeted
  materialization; the store then dies in the unread sweep.
- Bounded fixpoint (≤4 rounds) of the cleanup triple, post-exhaustion only.
- Terminal-segment RELAXED live-out pinning in range-realloc (only R0/R1
  observable past `bx lr` pre-prologue; VCR-RA-003 validator run with the
  same exemptions) — restricted to reload-free segments so R2/R3 stay free
  for the rechoice pass; late `elide_dead_frame` re-run once cleanup empties
  the frame.
- Constant-divisor trap-guard elision in the bridge's DivS/DivU/RemS/RemU
  (single-def `Const` scan, total-or-disabled def enumeration; c=0 keeps
  everything, DivS c=−1 keeps the overflow guard).

### Cycle proxy, re-measured (`scripts/repro/postex_cycle_proxy.py`)

Weighted proxy = dynamic instructions + data-memory accesses under unicorn,
summed over the differential vectors, every run execution-matched against
wasmtime in both flag states.

| fixture (default path) | off | on (PR #659) | on (now) | target ≤ +5% |
|---|---|---|---|---|
| `spill_on_exhaust_242.wat` | 368 | +30.4 % | 432 (**+17.4 %**) | missed |
| `spill_rung_581.wat` | 204 | +32.4 % | 222 (**+8.8 %**) | missed |
| `high_pressure_i32.wat` | 300 | +8.0 % | 228 (**−24.0 %**) | ✓ (now faster than the decline) |
| `signed_div_const.wasm` | 75 | +120 % | 50 (**−33.3 %**) | ✓ (now faster than the decline) |
| `i64_pair_exhaust_587.wat` | 584 | −5.5 % | 488 (**−16.4 %**) | ✓ |
| `i64_spill_pool_587.wat` | 1656 | −1.4 % | 1608 (**−2.9 %**) | ✓ |

(PR #659 percentages were derived on slightly different vector sets for two
fixtures; each column is internally consistent — off and on always share
vectors.)

### The residual, named

`spill_on_exhaust_242` (+17.4 %) and `spill_rung_581` (+8.8 %) still miss the
≤ +5 % bar. The residual cause is the allocation itself, not the cleanup:
`alloc_i32_scratch` draws destinations from a FIXED R4-R8 pool (5 registers)
while the direct selector allocates over all nine of R0-R8 — so the bridge
evicts 5 values where Belady over 9 registers needs 1. The post-hoc renamer
recovers only what fits through the two forever-free caller-saved registers
(R2/R3, serially reusable across disjoint live windows); the surviving pairs'
windows overlap every candidate. Widening the RELOAD pool with R2/R3 at
allocation time was tried and reverted (it starves the renamer of exactly
those registers: rung +8.8 % → +14.7 %). Closing the last gap needs dest
allocation over the full pool — the hand-written single-pass allocator itself,
i.e. the Track-A VCR-RA/VCR-SEL replacement, exactly the North-Star claim.
The `SYNTH_SPILL_ON_EXHAUST` default-on flip stays HELD (#580) on that gap +
gale G474RE cycles.

Reproduce:

```sh
cargo test -p synth-cli --test frozen_codegen_bytes --test vcr_ver_001_gate_242   # off
SYNTH_SPILL_ON_EXHAUST=1 cargo test -p synth-cli \
    --test frozen_codegen_bytes --test vcr_ver_001_gate_242                        # on
SYNTH=target/debug/synth python scripts/repro/postex_cycle_proxy.py
SYNTH=target/debug/synth SYNTH_SPILL_ON_EXHAUST=1 \
    python scripts/repro/r12_spill_496_differential.py
```
