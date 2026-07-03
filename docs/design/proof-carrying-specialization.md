# VCR-PERF-002 — Proof-carrying specialization design (#494)

Status: **design** (no code yet). Tracks `VCR-PERF-002` in
`artifacts/verified-codegen-roadmap.yaml`, epic #242, GitHub #494 part (a).
Cross-repo contract: loom#240 / loom#231 (`wsc.facts`), gale PR
pulseengine/gale#121 (`gust_floor_bench`, the measured floor).

## Why this document

gale measured the payoff before we built anything: under qemu `-icount`
(deterministic, re-run-identical), three lowerings of `gust_mix` over the same
proven-range inputs:

| lowering | fn-only ticks/call | ratio vs native |
|---|---|---|
| native (LLVM, full clamp) | 0.50 | 1.00× |
| dissolved today (synth ≥0.15.1) | 0.825 | 1.65× (in-range) |
| **proof-carrying floor** (`add #476` only) | **0.225** | **0.45×** |

`gust_mix` is algebraically `clamp(ch+476, 1000, 2000)`. A composition that
proves `ch ∈ [524,1524]` makes **both clamp branches dead**; the function
collapses to `add r0, #476; bx lr`. LLVM never emits that — it never had the
bound. The bound exists only in the verified pipeline: meld fuses a closed
world, loom's validator + gale's Verus/Rocq/Kani primitives prove the ranges.
The design question is purely how the fact travels and how synth is allowed to
act on it *soundly*. Target: **≤0.70× of native**, kill-criterion per #494.

## The contract (what loom forwards)

Per loom#231: a custom section **`wsc.facts`** (sibling of
`wsc.transformation.attestation`), carrying invariants loom's Z3 translation
validator already discharges, keyed by `(function index, value id)`. Fact
kinds, in silicon-payoff order:

1. **value-range** — `v ∈ [lo, hi]` (drives the clamp elision above)
2. **shift-bound** — shift amount `< 32`/`< 64` (bare `lsl/lsr`, no mask)
3. **divisor-nonzero** — drop the `div/rem` trap guard
4. **in-bounds access** — drop a bounds check
5. **select-totality** — branchless `IT` (pairs with VCR-SEL-004)
6. **memory disjointness** — keep values in registers across stores

**Fail-safe skew rule (loom#231 Q4):** synth ignores unknown fact kinds, and a
missing or unparseable section entirely. Facts are optional accelerators. The
facts-absent compile is **byte-identical to today's baseline by construction**
— which is also why every frozen fixture (none carries the section) stays
bit-identical trivially at every phase.

**Trust split (loom#231 Q3):** loom is the *prover* — fact validity is
loom's obligation, discharged by its validator and attested through the
existing `wsc` attestation channel. synth is a *conditional optimizer* — it
never re-derives the fact; it proves the conditional correctness of its **own
transformation given the fact** (next section). A forged fact is a contract
violation upstream, not a synth soundness hole: synth's certificate says
"correct **under P**", exactly the side-condition gale's bench encodes.

## How synth consumes facts: the per-elision proof obligation

Every specialization fires only after a machine-checked, per-site obligation,
discharged **before emission** by the ordeal-backed translation validator
(#553 / PR #595 — certificate-checked pure-Rust QF_BV behind the `BvSolver`
trait, so this runs on every dev machine and in CI with no C++ toolchain):

```
premise   P            (the wsc.facts invariant, asserted as a hypothesis)
obligation UNSAT( P ∧ (general_lowering(x) ≠ specialized_lowering(x)) )
```

- **UNSAT (certificate-checked)** → the elision is admitted; the certificate is
  logged per function (the evidence trail, not trust in a heuristic).
- **Sat / Unknown / conflict-budget exceeded** → **decline loudly**, emit the
  general lowering. There is no silent wrong-code path; the conservative
  fallback is today's codegen.

This is deliberately the same shape as the existing translation-validation
flow — the premise is the only new ingredient. `SYNTH_ORDEAL_MAX_CONFLICTS`
bounds adversarial queries to a clean conservative decline.

## Oracle strategy (every elision gated twice)

1. **Certificate** — the per-elision ordeal obligation above.
2. **Differential** — the specialized build must be result-identical to BOTH
   wasmtime and the unspecialized synth build **over the proven bound, and only
   over the bound** (exit-coded, exactly like `gust_floor_bench`'s soundness
   gate `mix_proven ≡ mix_native ≡ gust_mix` on `[524,1524]`). Out-of-bound
   divergence is *expected and correct* — the bound is the contract.
3. **Frozen anchors** — no facts section on any frozen fixture ⇒ the lever
   cannot fire ⇒ bit-identical trivially; additionally flag-gated
   (`SYNTH_FACT_SPEC`, default off) until gale confirms on silicon.

## Phasing (each phase its own oracle-gated PR)

1. **Fact ingestion** — parse `wsc.facts`, thread premises into
   `CompileConfig` / the selector. **Zero codegen change**; byte-identical,
   frozen-safe. Schema versioned, unknown-kind-tolerant. Co-designed with
   loom's emitter (loom#231 open questions 1/2 resolve here: keying + binary
   encoding).
2. **Single-elision prototype** — value-range ⇒ dead conditional-branch
   elision (the `gust_mix` clamp shape), behind `SYNTH_FACT_SPEC`, with the
   per-elision obligation + a red/green in-bounds differential oracle.
3. **Measurement vs the 0.45× floor** — gale re-measures `gust_mix` on
   `gust_floor_bench` (qemu `-icount`) and STM32F100 silicon (DWT CYCCNT).
   Kill-criterion (#494, unchanged): shipped dissolved lane **<1.0× then
   ≤0.70×** vs native LLVM, bit-identical under the proven bound. The measured
   floor gives 0.25× of headroom; if the productized elision can't land inside
   it, the premise-to-selector plumbing is at fault and the phase re-plans
   before any widening of fact kinds.

## Non-goals (this requirement)

- Part (b) of #494 (exhaustive/optimal allocation on small whole-known
  functions) — that is VCR-RA territory and independently unblocked.
- loom's algebraic mid-end (`256*x>>8 → x`, loom#240 ask 1) — a loom change;
  it shrinks the input but is not fact-passing.
- Fact kinds beyond value-range in the prototype — ordered by silicon payoff
  only after Phase 3 reports.
