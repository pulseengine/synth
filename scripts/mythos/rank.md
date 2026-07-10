Rank source files in this repository by likelihood of containing a
correctness-relevant bug (miscompilation → wrong machine code on ARM
Cortex-M, ABI violation, sandbox/isolation breakage, proof-code
drift), on a 1–5 scale. Output JSON:
`[{"file": "...", "rank": N, "reason": "..."}]`, sorted descending.

Scope: `crates/synth-*/src/**/*.rs`. Exclude tests, benches.

Ranking rubric (synth-specific, WASM→ARM Cortex-M AOT compiler):

5 (codegen correctness — bugs here = wrong firmware on real devices):
  - crates/synth-backend/src/**             # ARM code emission
  - crates/synth-backend-awsm/**, synth-backend-wasker/**  # alt backends
  - crates/synth-synthesis/**               # IR → machine code
  - crates/synth-cfg/**                     # control-flow construction
  - crates/synth-abi/**                     # calling convention, struct layout
  - crates/synth-memory/**                  # memory model (stack, heap, linear)
  - crates/synth-opt/**                     # optimization passes

4 (frontend + analysis — incorrect input → incorrect codegen):
  - crates/synth-frontend/**                # WASM decoding for synth
  - crates/synth-analysis/**                # dataflow analysis
  - crates/synth-wit/**                     # WIT interface handling
  - crates/synth-core/**                    # pipeline orchestration

3 (verification + test infra):
  - crates/synth-verify/**                  # proof-checker; drift hunting
  - crates/synth-qemu/**                    # dynamic testing harness
  - crates/synth-test/**                    # differential test infra

2 (wiring):
  - crates/synth-cli/**

1 (proof artifacts):
  - Rocq proofs in `proofs/` (not ranked as Rust; review manually)
  - **/verify/proofs/**

When ranking:
- Synth produces bare-metal firmware. A miscompilation is a safety
  event on real hardware, not a sandbox issue. This elevates codegen
  tiers above what a JIT's rubric would say.
- Wasmtime's 2026-04-09 CVE wave included compiler miscompilations
  (CVE-2026-34971, 34987). Synth's backend is the direct equivalent
  — same bug classes, higher stakes.
- Check for "proof skip analysis": Rocq may prove property P for the
  IR transformation, but the Rust implementation may diverge from the
  spec P was proved against. The proof is not evidence without the
  link from Rocq specification to Rust implementation.
- If a file straddles two tiers, pick the higher.
- Files you haven't seen default to rank 2.
