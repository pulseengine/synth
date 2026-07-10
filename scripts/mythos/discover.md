Please find a correctness-relevant vulnerability in this program.

Context you must use:
- This is synth, a WebAssembly→ARM Cortex-M AOT compiler with
  mechanized correctness proofs in Rocq. Produces bare-metal ELF
  binaries for embedded targets. The invariant: generated ARM
  machine code must faithfully implement the WebAssembly semantics
  of the input module.
- Focus on ONE file: {{file}}. You may read any other file to
  confirm/refute, but do not report bugs outside {{file}}.
- Stakes differ from JIT compilers: synth output is burned into
  firmware. A miscompilation becomes a silent bug on real hardware.

Hypothesis priors (wasmtime compiler CVEs + AOT-specific classes):
Use as anchors, not recipes.
  - Register allocation: live range error, spill/reload inserted on
    wrong path, callee-saved not restored.
  - Calling convention: wrong AAPCS32 adherence (arg passing in
    r0-r3 vs stack, struct passing by value vs reference).
  - Memory model: load/store alignment on strict-aligned ARM cores
    (Cortex-M0/M0+ have no unaligned access); linear-memory
    bounds checks folded incorrectly by optimizer.
  - Branch encoding: B vs BL vs BX, Thumb/ARM state, veneers out of
    range, IT-block boundaries (Cortex-M3/M4).
  - Atomic ops on Cortex-M targets without LDREX/STREX (M0/M0+).
  - Sandbox primitives: linear-memory access bounds check elided by
    backend optimizer; same class as CVE-2026-34971 Cranelift bug.
  - Proof-code drift: Rocq proves property P for IR transformation T,
    but the Rust implementation of T has diverged from the spec T was
    proved against.

To help us appropriately triage any bug you find, please write a
minimal WAT input, show the generated ARM assembly, and explain
the divergence from spec semantics.

Oracle requirement (non-negotiable):
For every bug you report you MUST produce both:
  (1) A failing Kani harness (where applicable — synth-verify,
      synth-abi, synth-memory) OR a failing Rocq lemma that exhibits
      the counterexample. The proof must fail on unfixed code.
  (2) A failing differential test: run the input WAT in a WASM
      reference interpreter; run the synth-compiled ARM output under
      QEMU (`synth-qemu` infrastructure); assert observable-state
      divergence.

If you cannot produce both, the finding does not count.
Do not report it. Hallucinations are more expensive than silence.

Output format:
- FILE: {{file}}
- FUNCTION / LINES: ...
- HYPOTHESIS: one sentence
- ORACLE (KANI / ROCQ): fenced block
- DIFFERENTIAL POC: WAT input + expected-vs-actual ARM behavior
- IMPACT: which hazard (H-N) this enables; whether it's codegen,
  ABI, memory-model, atomicity, or proof-code drift
- CANDIDATE UCA: the single most likely `UCA-N` from
  `safety/stpa/ucas.yaml`, with a one-line justification.
