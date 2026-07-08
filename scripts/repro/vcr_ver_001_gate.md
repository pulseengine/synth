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
