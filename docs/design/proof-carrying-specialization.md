# VCR-PERF-002 — Proof-carrying specialization design (#494)

Status: **Phases 1–2 + 2b implemented** (fact ingestion, the single-elision
prototype, and the divisor-nonzero trap-guard elision behind
`SYNTH_FACT_SPEC` — see "Phasing"; Phase 3, the gale measurement vs the
0.45× floor, remains). Tracks `VCR-PERF-002` in
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
validator already discharges, keyed by `(function index, value id)`. The
concrete binary encoding (schema v1 — version byte first, LEB128 fields,
length-prefixed unknown-kind-skippable records; resolves loom#231 open
questions 1/2) is specified in the sibling document
[`wsc-facts-encoding.md`](wsc-facts-encoding.md). Fact kinds, in
silicon-payoff order:

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
   encoding). **IMPLEMENTED** — encoding: `wsc-facts-encoding.md` (schema v1);
   parser: `crates/synth-core/src/wsc_facts.rs` (total, fail-safe), wired
   into `decode_wasm_module` and threaded to `CompileConfig::wsc_facts` /
   `current_func_facts`; neutrality gate:
   `crates/synth-cli/tests/wsc_facts_ingestion_494.rs` (facts-present compile
   byte-identical to facts-stripped, malformed/wrong-version ignored
   end-to-end).
2. **Single-elision prototype** — value-range ⇒ dead conditional-branch
   elision (the `gust_mix` clamp shape), behind `SYNTH_FACT_SPEC`, with the
   per-elision obligation + a red/green in-bounds differential oracle.
   **IMPLEMENTED** — pass: `crates/synth-verify/src/fact_spec.rs`
   (backend-agnostic `WasmOp`-stream rewrite; the discharged obligation is
   `UNSAT(P ∧ cond ≠ 0)`, which implies the general/specialized equivalence
   above for a no-`else` `if` — see the module docs for the
   over-approximation discipline and why `div/rem` stay untracked). Driver
   gate: `maybe_fact_spec` in `synth-cli/src/main.rs` (both compile paths;
   requires the `verify` feature — without it the flag declines loudly).
   Oracles: `crates/synth-cli/tests/fact_spec_clamp_494.rs` (flag/fact
   matrix, certificate trail, wrong-bound Sat decline) +
   `scripts/repro/fact_spec_clamp_494_differential.py` (in-bounds execution
   sweep, specialized ≡ wasmtime ≡ unspecialized on [524,1524]), both CI-run
   by the `fact-spec-oracle` job. Fixture:
   `scripts/repro/fact_spec_clamp_494.wat`.

   **Phase 2b — divisor-nonzero trap-guard elision (fact kind 3).
   IMPLEMENTED.** The pass's symbolic walk now TRACKS `div`/`rem` (i32 and
   i64) instead of stopping at them — the ops are never *deleted* (they can
   trap; a div result carries no erasable producer slice), but each site
   discharges up to TWO **independent** guard obligations and emits per-site
   elision marks the direct selector consumes
   (`CompileConfig::fact_div_zero_elide` / `fact_div_ovf_elide`):

   | guard | applies to | obligation |
   |---|---|---|
   | divide-by-zero (`CMP/BNE/UDF #0`; i64: fused `ORRS R12/BNE/UDF #0`) | `div_u`, `div_s`, `rem_u`, `rem_s` | `UNSAT(P ∧ divisor == 0)` |
   | `INT_MIN / -1` overflow (`…UDF #1`; i64: the #633 22-byte sequence) | `div_s` ONLY (`rem_s(INT_MIN,-1) == 0` never traps) | `UNSAT(P ∧ dividend == INT_MIN ∧ divisor == -1)` |

   **The two-guard distinction (the #633/#634 synergy):** a divisor-nonzero
   fact (kind 3) discharges the first obligation but NOT the second —
   `divisor ≠ 0` does not exclude `divisor == -1`, so the overflow guard is
   RETAINED (loud decline) unless the premises independently prove it (a
   value-range fact `divisor ∈ [1, N]` proves both). Both fact kinds work:
   kind 3 directly, or any value-range excluding 0. Sat / Unknown /
   no-premise ⇒ loud decline, the guard is emitted.

   Consumption is direct-selector-only: the optimized path's IR passes
   renumber instructions, so op-index-keyed marks route the function to
   `select_with_stack` (the #507/#509 honest-degradation pattern; never
   fires without flag + facts + a discharged obligation). The i64 guards
   live inside the `ArmOp::I64Div*/I64Rem*` encoder expansions, which
   gained per-guard elision flags — estimator sizes track them
   (estimator↔encoder agreement oracle extended with the elided variants).
   Oracles: fact_spec unit gates (two-guard matrix, i64 width discipline,
   mark remapping through a clamp elision) +
   `crates/synth-cli/tests/fact_spec_div_494.rs` (byte evidence: guard UDFs
   present without facts, absent with facts+flag, i64 overflow guard
   retained under kind 3; Sat-decline byte-identity; the debug-only
   `SYNTH_FACT_SPEC_FORCE_ADMIT` red lever) +
   `scripts/repro/fact_spec_div_494_differential.py` (in-bounds sweep over
   the proven divisor bound incl. the retained-guard trap
   `qs64(INT64_MIN, -1)`; `--expect-decline`; `--force-admit` red
   divergence demo), all CI-run by the `fact-spec-oracle` job. Fixture:
   `scripts/repro/fact_spec_div_494.wat`.
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
- Fact kinds beyond value-range and divisor-nonzero in the prototype —
  ordered by silicon payoff only after Phase 3 reports.
