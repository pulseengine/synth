# Validation Infrastructure — Status

> **Historical note (rewritten 2026-09, #1080).** An earlier version of this
> document described an OCaml-extraction validation pipeline (`extracted/`,
> `validation/`, dune builds, a Sail ARM emulator differential) as "complete
> and ready for use" underneath a header saying the opposite. Neither claim
> survived: the pipeline was never wired into any build, and the checked-in
> extraction snapshots it described drifted for months (the committed
> `WasmInstructions.ml` predated the model's `BrIf` constructor by nine
> months) while disagreeing with each other across four directories. All of
> those snapshots and the dune tree were **deleted** in #1080. This page now
> describes only what exists and runs.

## Where extraction actually lives

Coq-to-OCaml extraction is a build step, not a checked-in artifact:

- **Source**: `coq/Synth/Extraction/CompilerExtract.v` — the extraction
  configuration for the verified `compile_wasm_to_arm` function and the WASM
  and ARM semantics.
- **Build target**: `rocq_library(name = "extraction")` in `coq/BUILD.bazel`,
  a dependency of `rocq_proof_test(name = "rocq_proofs")`.
- **Gate**: `bazel test //coq:verify_proofs` re-runs extraction on every CI
  run, inside the Bazel sandbox. The extracted OCaml is a derived artifact of
  that build; no copy is committed, so there is no copy to go stale.

If a reviewable extraction snapshot is ever needed (e.g., as assessor
evidence), the honest mechanism is the one used for the project's other
generated artifacts (`VcrSelRulesGenerated.v` #667, `proof-inventory.json`
#1057): regenerate in CI and byte-compare, so drift is a red gate rather than
a discovery. Nothing currently consumes such a snapshot, so none is kept.

## What validates the compiler today

The validation strategy this document once proposed (execute extracted OCaml
semantics against a Sail emulator) was never implemented. What shipped
instead, and runs in CI:

- **Mechanized proofs** — the Rocq suite under `coq/Synth/` (see
  `coq/STATUS.md` for the coverage matrix), built by
  `bazel test //coq:verify_proofs`. The 80 selector-DSL rule theorems are
  stated about a model **generated from the shipped selector table** (#667),
  not a hand-written mirror.
- **Per-compilation translation validation** — `synth-verify` (SMT, ordeal
  QF_BV by default; Z3 as a feature-gated differential oracle), and the
  unconditional static-data addressing validator
  (`synth_core::static_data_addr`, VCR-VER-003).
- **Differential oracles, CI-gated** — cmp-select, RV32 shift-fold /
  const-addr-fold, callee-saved, spill-frame, and symtab-based frozen-fixture
  differentials; unicorn full-boot and WCET soundness cross-checks
  (`wcet_*_soundness.py`).
- **Emulation tests** — Renode Cortex-M4 tests under `tests/` (Bazel).

## History

The remaining challenges recorded here previously — Sail 0.20 keyword
incompatibilities with the ARM model, C emulator/runtime signature mismatches,
and the 40 GB build footprint of the Sail Coq snapshots — were real findings
of the 2025-11 exploration and are preserved in
`docs/build-systems/BAZEL_INTEGRATION_RESEARCH.md`. The Sail direction later
landed in a different, smaller form: `coq/Synth/ARM/SailArmBridge.v`
(VCR-ISA-001 spike, 92 Qed). The 2025-11 dune-based validation run is reported
in `docs/validation/COMPREHENSIVE_VALIDATION_REPORT.md`, which is likewise
historical — the executables it describes were removed in #1080.
