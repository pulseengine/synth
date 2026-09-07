# Acceptance ladder — v0.63

**Measured 2026-09-06** on synth at `e3a09ac2` (all v0.63 capability work merged),
over the **243-module reachable corpus** (131 core + 112 components, unique by
sha256, manifest at `corpora/wasm-243/MANIFEST.sha256`).

Produced by `scripts/repro/partial_census_1017.py --ladder`. Rungs are reported
**separately and never summed into one rate** — see "Why a ladder" below.

## The ladder

| backend | default | +embedder-ack | +allow-skipped | +no-optimize | NEVER |
|---------|---------|---------------|----------------|--------------|-------|
| **arm** | 27 (11.1 %) | **+72 → 99 (40.7 %)** | +3 | +0 | 141 |
| **riscv** | 50 (20.6 %) | +0 | +11 | +0 | 182 |
| **aarch64** | 49 (20.2 %) | +0 | +1 | +0 | 193 |

- **default** — `--all-exports --relocatable`, no other flags. What a consumer
  gets with no knowledge of the embedder contract.
- **+embedder-ack** — `--embedder-data-init --embedder-global-init`. The
  consumer ACKNOWLEDGES an embedder obligation. These modules compile today.
- **+allow-skipped** — `--allow-skipped-exports`. **Categorically different: a
  PARTIAL object is a third state, not a pass.** Counted, labelled, and never
  folded into accepts.
- **+no-optimize** — **STRUCTURALLY INERT under this base invocation, and not
  a measured negative.** Every rung runs `--relocatable`, and
  `arm_backend.rs:990` selects the direct path on
  `no_optimize || relocatable || …`, so the flag changes nothing on ARM here;
  riscv and aarch64 never read it at all. "+0" is the only value this rung can
  report. **Nothing about the two `#197` selector paths follows from it** —
  the optimized ARM selector is never reached by this ladder. Measuring that
  needs a run WITHOUT `--relocatable`, which is a different ABI and a
  different measurement. Kept and labelled rather than deleted, because a rung
  that cannot move is the checker-that-cannot-fail class this release spent
  its scope finding, here in a measurement harness.

## Why a ladder, and not one number

v0.62 published `arm 11 %, riscv 16 %, aarch64 19 %` measured with ONE fixed
invocation. On arm that under-reports by a factor of **3.7**: 27 modules become
99 the moment the embedder obligation is acknowledged.

`--embedder-data-init` / `--embedder-global-init` are **not a feature switch**.
They are the `#952`/`#1041`/`#1052` honest-refusal pattern: synth refuses to
emit an object whose data or globals the embedder must initialise unless the
caller states that it will. Counting those refusals as "cannot compile" says
synth cannot do work it demonstrably can.

**This does NOT mean the flags should be default** — see `RQ-63-ACKDEFAULT`.
The refusal is correct; only the reporting was wrong.

## What moved this release, and what did not

Against v0.62's census on the same corpus:

| backend | v0.62 | v0.63 | delta | cause |
|---|---|---|---|---|
| arm | 27 | 27 | **+0** | `RQ-63-ARMI64OFF` cleared its 46-module blocker and gained **zero** reach — all 46 landed on the next rung |
| riscv | 40 | 50 | **+10** | `RQ-63-RVGLOBAL` |
| aarch64 | 46 | 49 | **+3** | `RQ-63-A64STACK` |

**A BLOCKER COUNT IS NOT A REACH ESTIMATE.** The census records only the FIRST
decline per function, so clearing a top blocker does not add its count — it
reveals the next layer. All three v0.63 lanes reported this independently, and
the full corpus confirms it: `RQ-63-A64STACK` cleared 77 modules and gained 3;
`RQ-63-ARMI64OFF` cleared 46 and gained 0. Any plan built on primary-blocker
counts systematically overestimates every fix.

The clearest instance: **aarch64's `MemoryCopy` went 45 → 106 modules without
anyone touching `MemoryCopy`.** Those modules were always blocked by it, hidden
behind an earlier decline.

## NEVER buckets — the real capability gaps

Attributed from the MOST PERMISSIVE invocation, so a blocker surviving every
flag is a genuine gap and not a missing acknowledgement.

### arm (141)
| n | blocker |
|---|---------|
| 71 | register exhaustion — no free callee-saved register to hold a call result while reloading a preserved param |
| 41 | `#929` AAPCS: an i64 call argument needs an even-aligned register PAIR |
| 7 | start section — no backend invokes it |
| 5 | `rule_i32_rotl` side condition |
| 4 | `call_indirect` type/table mismatch |
| 4 | `encode_operand2` non-rotated immediate |
| 3 | `GI-FPU-002` scalar f32 without an FPU |

#### arm (141), re-attributed under RQ-64-HISTOGRAM (#1159, v0.64)

The table above is the v0.63 measurement as its instrument printed it. That
instrument did not mask HEX payloads, so `encode_operand2`'s non-rotated
immediates fragmented one row per value (`0x624` 4, `0x5dc` 1) and — the
under-ranking one level down — inside four more modules each fragment lost
`_modal()`'s plurality vote to a cause that happened to carry no varying
payload (`yolo_inference_{release,debug}`: 84 functions across ~20 immediates,
largest fragment 6, vs 58 for `GI-FPU-002`). Same binary, same corpus, rungs
identical (27 / 72 / 3 / 141), only the bucketing fixed:

| n | blocker |
|---|---------|
| 70 | register exhaustion — no free callee-saved register to hold a call result while reloading a preserved param |
| 40 | `#929` AAPCS: an i64 call argument needs an even-aligned register PAIR |
| **9** | **`encode_operand2` non-rotated immediate** — was 4 + 1 in two rows, plus four modules attributed elsewhere; rank 5 → 3 |
| 7 | start section — no backend invokes it |
| 5 | `rule_i32_rotl` side condition |
| 4 | `call_indirect` type/table mismatch |
| 2 | WASM decode failure |
| 1 | `GI-FPU-002` scalar f32 without an FPU — was 3 |
| 1 · 1 · 1 | `call_indirect` type-id sidecar · `LdrSym` Thumb-2-only · no exports |

The riscv and aarch64 tables below are unchanged: their records carry no hex
payload, so the fix is a no-op there by construction. The instrument now
asserts on every run that its printed rows sum to the modules they rank, and
its `--self-test` (the two shapes above, a negative control) is CI-wired.

### riscv (182)
| n | blocker |
|---|---------|
| 62 | immediate too large for memory offset |
| 51 | multi-memory `#406` — no per-memory base lowering |
| 30 | `call_indirect` unsupported in the RV32 skeleton |
| 18 | `Call` unsupported in the RV32 skeleton |
| 7 | start section |
| 6 | non-contiguous global index space |

### aarch64 (193)
| n | blocker |
|---|---------|
| 106 | `MemoryCopy` |
| 51 | multi-memory `#406` |
| 22 | active data segments not materialised |
| 7 | start section |
| 2 | `MemoryFill` |

## One cross-backend observation worth recording

riscv's top blocker — *"immediate too large for memory offset"* (62 modules) —
is the **same class** as the A32 defect `#1167` this release fixed. The two
backends handled it oppositely: **RV32 declines loudly; A32 silently masked the
offset and emitted a wrong address at exit 0.** Identical gap, and only one of
them was a miscompile. The loud one cost acceptance; the silent one cost
correctness.

## Reproducing

```sh
python3 scripts/repro/partial_census_1017.py \
  --synth ./target/debug/synth --backend <arm|riscv|aarch64> \
  --ladder --json ladder.json <corpus-root>
```

The corpus is not carried by CI (243 modules, 426 MB); the manifest pins it by
sha256 so a re-run is checkable.
