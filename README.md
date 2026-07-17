<div align="center">

# Synth

<sup>WebAssembly-to-native AOT compiler (ARM Cortex-M/R &middot; RISC-V &middot; AArch64) with mechanized correctness proofs</sup>

&nbsp;

[![CI](https://github.com/pulseengine/synth/actions/workflows/ci.yml/badge.svg)](https://github.com/pulseengine/synth/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/pulseengine/synth/graph/badge.svg)](https://codecov.io/gh/pulseengine/synth)
![Rust](https://img.shields.io/badge/Rust-CE422B?style=flat-square&logo=rust&logoColor=white&labelColor=1a1b27)
![WebAssembly](https://img.shields.io/badge/WebAssembly-654FF0?style=flat-square&logo=webassembly&logoColor=white&labelColor=1a1b27)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square&labelColor=1a1b27)

[![Rocq Qed](https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fpulseengine%2Fsynth%2Fmain%2Fartifacts%2Fstatus.json&query=%24.rocq_qed&label=Rocq%20Qed&color=blueviolet&style=flat-square&labelColor=1a1b27)](coq/STATUS.md)
[![Rocq Admitted](https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fpulseengine%2Fsynth%2Fmain%2Fartifacts%2Fstatus.json&query=%24.rocq_admitted&label=Admitted&color=orange&style=flat-square&labelColor=1a1b27)](coq/STATUS.md)
[![Verified selector rules](https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fpulseengine%2Fsynth%2Fmain%2Fartifacts%2Fstatus.json&query=%24.sel_dsl_rules&label=verified%20selector%20rules&color=blue&style=flat-square&labelColor=1a1b27)](artifacts/status.json)

<sub>Badge numbers are machine-derived into [`artifacts/status.json`](artifacts/status.json) and CI-staleness-gated — never hand-typed.</sub>

&nbsp;

<h6>
  <a href="https://github.com/pulseengine/meld">Meld</a>
  &middot;
  <a href="https://github.com/pulseengine/loom">Loom</a>
  &middot;
  <a href="https://github.com/pulseengine/synth">Synth</a>
  &middot;
  <a href="https://github.com/pulseengine/kiln">Kiln</a>
  &middot;
  <a href="https://github.com/pulseengine/sigil">Sigil</a>
</h6>

</div>

&nbsp;

Synth is an ahead-of-time compiler from WebAssembly to ARM Cortex-M machine code, with additional backends for ARM Cortex-R5 (A32, `--target cortex-r5`), RISC-V RV32IMAC (qemu_riscv32 / ESP32-C3), and AArch64 (host-native, `-b aarch64`). It produces bare-metal ELF binaries targeting embedded microcontrollers. The compiler handles i32, i64 (via register pairs), scalar f32/f64 via VFP on FPU targets (f32 complete v0.41, f64 complete v0.43 — #369 closed; open residuals tracked in #782), control flow, and memory operations; any construct without a lowering declines loudly rather than miscompiling (the #369/#554 gate class). Mechanized correctness proofs in [Rocq](https://rocq-prover.org/) cover the i32 and i64 instruction selection with result-correspondence (T1) proofs; float/SIMD selection has existence-only (T2) proofs.

**This is pre-release software.** Generated code is validated by unit tests, Renode/QEMU emulation, execution differentials against wasmtime, and — for specific fixtures — cycle- and correctness-gated runs on real Cortex-M silicon (NUCLEO-G474RE, STM32F100, via the gale test loop). Broad hardware validation is still missing. Use at your own risk.

Part of [PulseEngine](https://github.com/pulseengine) -- a WebAssembly toolchain for safety-critical embedded systems:

| Project | Role |
|---------|------|
| [**Synth**](https://github.com/pulseengine/synth) | WASM-to-ARM AOT compiler with Rocq proofs |
| [**Loom**](https://github.com/pulseengine/loom) | WASM optimizer with Z3 verification |
| [**Meld**](https://github.com/pulseengine/meld) | WASM Component Model static fuser |
| [**Kiln**](https://github.com/pulseengine/kiln) | WASM runtime for safety-critical systems |
| [**Sigil**](https://github.com/pulseengine/sigil) | Supply chain attestation and signing |

## Customer narrative

Synth's pitch is that **functional safety is a certification problem, not a
processor problem**: the right unit of evidence is verifiable code
generation from a small, well-defined source language (WASM) to a small,
well-defined target ISA (Thumb-2 / RV32), not a verified silicon core.
Synth contributes the codegen half of that workflow: a compiler whose
lowering steps come with mechanized proofs and an explicit
[Spectre / speculative-execution policy](docs/spectre-policy.md) per
lowering rule.

## Installation

### From source (Cargo)

Requires Rust 1.88+ (edition 2024).

```bash
git clone https://github.com/pulseengine/synth.git
cd synth
cargo build --release -p synth-cli
```

The binary is at `target/release/synth`. Add it to your PATH or invoke directly.

### With Bazel

Bazel 8.x builds Rust, Rocq proofs, and Renode emulation tests hermetically via Nix.

```bash
bazel build //crates:synth
```

## Quick Start

```bash
# Compile a WAT file to a Cortex-M ELF binary
synth compile examples/wat/simple_add.wat --cortex-m -o firmware.elf

# Disassemble the result
synth disasm firmware.elf
```

Translation validation (`synth verify`, `--verify`) is feature-gated in the CLI. Since v0.27.0 the default verification engine is [ordeal](https://github.com/pulseengine/ordeal), a pure-Rust QF_BV solver — `synth-verify` itself no longer needs a C++ toolchain. The CLI `verify` feature currently also enables the feature-gated Z3 differential oracle (statically linked):

```bash
cargo build --release -p synth-cli --features verify
synth verify examples/wat/simple_add.wat firmware.elf
```

## Features

| Category | Status | Notes |
|----------|--------|-------|
| i32 arithmetic, bitwise, comparison, shift/rotate | **Tested** | Full Rocq T1 proofs, Renode execution tests |
| i64 (register pairs): arithmetic, shifts, rotates, div/rem, compare | **Tested** | full pair lowering — right shifts fixed v0.28.0 (#599), rot/div/rem v0.30.1 (#610), A32 completeness v0.30.2 (#615); differential vs wasmtime |
| Scalar f32/f64 via VFP on FPU targets | **Implemented** | Complete f32 (v0.41) + f64 (v0.43, #369 closed) incl. AAPCS-VFP marshalling; execution differentials vs wasmtime; non-FPU targets loud-reject; residuals: `trunc_sat` not decoded (loud skip) + a pressure-dependent f32 class (#782) |
| WASM SIMD via ARM Helium MVE | Experimental | Cortex-M55 only; encoding untested on hardware |
| Control flow (block, loop, if/else, br, br_table) | **Tested** | Renode execution tests, complex test suite |
| Function calls (direct, indirect) | Implemented | `call_indirect` traps per WASM §4.4.8 (OOB index, type mismatch, null slot); self-contained `--cortex-m` dispatch via a PC-relative flash funcref table since v0.47 (#275), execution-differential-gated vs wasmtime |
| Memory (load/store, sub-word, size/grow) | Implemented | memory.grow returns -1 on embedded (fixed memory) |
| Globals, select | Implemented | R9-based globals; unit tests only |
| ELF output with vector table | Implemented | Thumb bit set on symbols; not linked on real hardware |
| Linker scripts (STM32, nRF52840, generic) | Implemented | Generated, not tested with real boards |
| Cross-compilation (`--link` flag) | Implemented | Requires `arm-none-eabi-gcc` in PATH; not CI-tested |
| Rocq mechanized proofs | CI-derived (badges above) | i32 + i64 T1 correctness proofs; the selector-DSL rule theorems are stated directly about the GENERATED model (VCR-ISA-001 #667 — `rule_X := Gen.rule_X`, single source `VcrSelRulesGenerated.v`); all four i32 div/rem trap guards discharged against the branch-taking executor (#73); counts re-derived into `artifacts/status.json` on every commit |
| SMT translation validation | ordeal (pure-Rust QF_BV) default | v0.27.0 (#553); Z3 demoted to feature-gated differential oracle — 141/141 agreement |
| WebAssembly spec test suite | CI-tracked compile rate | Compilation only — not executed on emulator |

### What doesn't work yet

- **Narrow hardware coverage** — silicon validation is fixture-scoped (gale's NUCLEO-G474RE / STM32F100 cycle and correctness gates); there is no broad board matrix
- **No multi-memory** — fused components from meld need single-memory mode
- **No WASI on embedded** — kiln-builtins crate doesn't exist yet
- **No component model execution** — components compile but can't run without kiln-builtins; `cabi_realloc` binds natively (synthesized in-module arena allocator) on self-contained dissolves since v0.47, with #418 still open for the real dissolved fixture
- **Spill-on-exhaustion is opt-in** — Belady spilling is default-on (v0.24.0, VCR-RA-001), but replacing the register-exhaustion decline with allocation-time spilling (`SYNTH_SPILL_ON_EXHAUST`, #580) is held for silicon numbers
- **No tail call optimization** — return_call compiles but doesn't optimize the call frame
- **SIMD/Helium is untested** — MVE instruction encoding implemented but never run on M55 silicon or emulator

## Usage

### Compile WASM/WAT to ARM ELF

```bash
# Compile a WAT file to an ARM ELF binary
synth compile examples/wat/simple_add.wat -o add.elf

# Compile with a built-in demo (add, mul, calc, calc-ext)
synth compile --demo add -o demo.elf

# Compile a complete Cortex-M binary (vector table, startup code)
synth compile examples/wat/simple_add.wat --cortex-m -o firmware.elf

# Compile all exported functions
synth compile input.wat --all-exports -o multi.elf

# Compile and formally verify the translation
synth compile input.wat --verify -o verified.elf
```

### Disassemble

```bash
synth disasm add.elf
```

### Translation validation

```bash
# Standalone verification: check that an ELF faithfully preserves WASM semantics
synth verify input.wat output.elf
```

### List backends

```bash
synth backends
```

## Compilation Pipeline

```mermaid
graph LR
    A["WAT / WASM"] --> B["Parse &<br/>Decode"]
    B --> C["Instruction<br/>Selection"]
    C --> D["Peephole<br/>Optimizer"]
    D --> E["ARM<br/>Encoder"]
    E --> F["ELF<br/>Builder"]
    F --> G["ARM ELF<br/>Binary"]

    style A fill:#654FF0,color:#fff
    style G fill:#CE422B,color:#fff
```

**Pipeline stages:**

1. **Parse** -- decode WASM binary or WAT text via `wasmparser`/`wat` crates
2. **Instruction selection** -- pattern-match WASM ops to ARM instruction sequences (i32, i64, f32, f64, SIMD)
3. **Peephole optimization** -- redundant-op elimination, NOP removal, instruction fusion, constant propagation (0-25% code reduction)
4. **ARM encoding** -- emit 32-bit ARM / Thumb-2 machine code
5. **ELF builder** -- produce ELF32 with `.text`, `.isr_vector`, `.data`, `.bss`, symbol table; optional vector table and reset handler for Cortex-M

## Formal Verification

### Verification status

Per the [PulseEngine Verification Guide](https://pulseengine.eu/guides/VERIFICATION-GUIDE.md), projects target multi-track verification. Current status:

| Track | Status | Coverage |
|-------|--------|----------|
| **Rocq** | Partial | i32 + i64 T1 result-correspondence; float/SIMD T2; selector-DSL rule theorems stated directly about the GENERATED model (VCR-ISA-001 #667); all four i32 div/rem trap guards discharged (#73). Counts: `artifacts/status.json` (CI-re-derived; badges above) |
| **Kani** | Starting | Bounded model checking harnesses for the ARM encoder (count: `artifacts/status.json`) |
| **Verus** | Starting | Spec functions in `synth-synthesis/src/contracts.rs`; Bazel integration via `rules_verus` (count: `artifacts/status.json`) |
| **Lean** | Not started | — |

See `artifacts/verification-gaps.yaml` for the detailed gap analysis (VG-001 through VG-008).

### Rocq proof suite

Mechanized proofs in Rocq 9 show that `compile_wasm_to_arm` preserves WASM semantics for each operation. The proof suite lives in `coq/Synth/` and covers ARM instruction semantics, WASM stack-machine semantics, and per-operation correctness theorems.

```
Qed/Admitted counts: artifacts/status.json — machine-derived and CI-gated
(claims.yaml + scripts/claim_check.py); surfaced by the badges at the top.
  T1 result-correspondence (ARM output = WASM result): all i32 ops and all
     i64 ops — i64 T1 parity since v0.11.0, 0 i64 admits (coq/STATUS.md)
  T2 existence-only: f32/f64 and remaining categories
  T3 admitted: 1 CorrectnessSimple.v, 2 ArmRefinement.v
     (0 division admits — all four i32 div/rem trap guards discharged against
     exec_program_br, #73 closed at i32; #166 discharged the 2 Compilation.v
     example admits via vm_compute; the CorrectnessSimple.v i32_const_correct
     residual is a documented modeling-gap T3 — the MOVW+MOVT reconstruction
     arithmetic is proven, the gap is the un-normalized-Z WASM-constant
     representation; the 2 ArmRefinement.v admits are opaque-sail_exec_instr-
     axiom placeholders superseded by SailArmBridge.v)
  incl. the selector-DSL rule theorems (Synth/VcrSelRules.v — every manifest
     rule has a 1:1 Qed correctness theorem, count-same CI-gated against
     coq/vcr_sel_rules.manifest) — stated directly about the GENERATED model
     (VCR-ISA-001 #667: rule_X := Gen.rule_X, single source
     Synth/VcrSelRulesGenerated.v emitted from the shipped sel_dsl::RULES, so
     a selector-table change breaks the matching Qed), the VCR-SEL-001
     pilot lemmas (Synth/VcrSelPilot.v, #386), and the Sail/ASL bridge
     lemmas (ARM/SailArmBridge.v, VCR-ISA-001)
```

i32 and i64 operations have full T1 (result-correspondence) proofs; i64 parity landed in v0.11.0. The four i32 div/rem trap-guard proofs are discharged against the branch-taking executor `exec_program_br` (#73). The f32, f64, and SIMD instruction selection has T2 existence proofs but not T1 result-correspondence.

Build the proofs:

```bash
# Hermetic build via Bazel + Nix
bazel test //coq:verify_proofs

# Or locally with Rocq 9
cd coq && make proofs
```

See [coq/STATUS.md](coq/STATUS.md) for the per-file coverage matrix.

### SMT translation validation (ordeal, with Z3 as differential oracle)

The `synth-verify` crate encodes WASM and ARM semantics as QF_BV formulas and checks per-rule equivalence. Since v0.27.0 (#553/#595) the default engine is [ordeal](https://github.com/pulseengine/ordeal), a pure-Rust QF_BV solver (139/139 validator tests, ~2 s; no C++ toolchain required); Z3 is demoted to a feature-gated (`z3-solver`) differential oracle — 141/141 cases, zero disagreements with ordeal. The `--verify` CLI flag invokes validation after compilation; `synth verify` provides standalone validation.

## Roadmap — North Star

**Replace synth's patch-accreting code generator with foundationally-verified, allocator-robust infrastructure — so correctness comes from construction, not from an ever-growing pile of locally-correct patches.**

The recurring greedy fixes (the reciprocal-multiply cost-gate, the register-exhaustion hard-fail, the "selector missed an op" class behind #223/#226/#232) are all symptoms of one root cause: two single-pass, hand-written components — the **instruction selector** and the **register allocator**. The fix is filed as a phased, parallelizable rivet program (**VCR-\***, [epic #242](https://github.com/pulseengine/synth/issues/242), `artifacts/verified-codegen-roadmap.yaml`), built incrementally alongside the per-issue cadence — never a big-bang rewrite, **behavior frozen and oracle-gated at every step**.

The one-sentence version: moving synth's correctness from *"we patched every bug we found"* to *"the structure makes the bug unrepresentable."*

**Historical motivation** (gale, #209, on NUCLEO-G474RE, mid-2026): the fully-composed `flat_flight` ran **315 cyc vs 99 native (3.18×)** with **61 % redundant constant materializations** and **17 stack spills**. Those numbers set the allocator track's agenda; the v0.19–v0.30 arc has since retired them.

### Shipped (v0.19.0 → v0.30.2, 2026-07)

- **`VCR-RA-001` — allocator with liveness-based Belady spilling: `verified`, default-on since v0.24.0** (`SYNTH_SPILL_REALLOC`). `flat_flight` reaches its Belady optimum — 412→388 B, hot-segment frame traffic 3 ld + 3 st → **0** — with every re-pinned fixture execution-proven vs wasmtime first.
- **const-CSE default-on** (v0.29.0, #604) — the redundant-materialization datum retired; gale-confirmed on its kernel (`gust_mix` 90→86 B loom-inlined, direct-compile `func_1` 70→66 B).
- **The lever ladder, all default-on and evidence-gated** with CI-pinned `=0`/escape-hatch opt-outs: cmp→select fusion (ARM v0.13.0, RV32 v0.28.0), i32 local promotion (v0.14.0, with the v0.15.1 never-cause-a-compile-failure fallback), immediate-shift folding (ARM v0.15.0, RV32 v0.30.0), base-CSE into R11 (v0.27.0), dead-frame-elim + uxth-fold (v0.30.0).
- **i64 completeness arc**: direct-path i64 stack params + pair spill-pool growth (#503, v0.29.0), pair right-shifts (#599, v0.28.0), rotl/rotr/div/rem silent-zero fix (#610, v0.30.1), and the A32 (`cortex-r5`) i64 family — previously silently encoding to NOP — rebuilt with a **221-variant no-wildcard tripwire** so no silent-NOP arm can regrow (#615, v0.30.2).
- **Verification substrate**: [ordeal](https://github.com/pulseengine/ordeal) (pure-Rust QF_BV) is the default translation-validation engine since v0.27.0; Z3 demoted to a feature-gated differential oracle (141/141 agreement). Track C's differential oracles are CI-gated jobs (cmp-select, RV32 shift-fold/const-addr-fold, callee-saved, spill-frame, control_step/flight_seam symtab-based fixtures, …).

### In flight / next

| Track | Item | What it does | Status |
|-------|------|--------------|--------|
| **A — codegen core** | `VCR-SEL-001` | Rocq-discharged verified selector DSL — *"ISLE with a proof-assistant backend"*; a missing lowering rule becomes an enumerable coverage gap, not a silent miscompile | increments 1–4 shipped default-on (`SYNTH_SEL_DSL`, opt-out `SYNTH_NO_SEL_DSL=1`): every manifest rule has a 1:1 Qed correctness theorem in `coq/Synth/Synth/VcrSelRules.v` (count-same CI-gated against `coq/vcr_sel_rules.manifest`; current counts: `artifacts/status.json`), plus pilot lemmas in `coq/Synth/Synth/VcrSelPilot.v`; the DSL is now the SHIPPED lowering path for its covered ops (byte-invisible flip — every rule was mirror-pinned byte-identical to the hand-written arm it replaces, frozen anchors unmoved) |
| | `VCR-PERF-002` | Proof-carrying specialization (#494): loom's `wsc.facts` invariants become premises for per-elision proof obligations, certificate-checked by the ordeal-backed validator — toward gale's measured **0.45× (below-native) floor** | design traced (v0.30.0); phase 1 (facts ingestion) landed ([PR #624](https://github.com/pulseengine/synth/pull/624), v0.31.0) |
| | `SYNTH_SPILL_ON_EXHAUST` | Replace the register-exhaustion decline with allocation-time Belady spilling (#580) — the last piece of the exhaustion hard-fail | built, flag-off; default-on held for silicon cycle numbers |
| **B — authoritative semantics** | `VCR-ISA-001` | Re-base ARM/RISC-V semantics on Sail-generated Rocq (the official ISA spec); generate the selector model, don't mirror it (#667) | approved — Sail/ASL bridge spike landed (`coq/Synth/ARM/SailArmBridge.v`); #667 "generate, don't mirror" landed: the shipped `sel_dsl::RULES` table emits the covered ops' Rocq lowerings (`coq/Synth/Synth/VcrSelRulesGenerated.v`), and `VcrSelRules.v` DEFINES `rule_X := Gen.rule_X` — the generated file is the single model source, the per-rule correctness Qed are stated directly about it, and a selector-table change breaks the matching proof (no hand-written copy left to drift) |
| | `VCR-WASM-001` | Anchor WASM source semantics on WasmCert-Coq | phases 1+2 landed: the i32 integer fragment (arithmetic/bitwise/shifts/eqz/comparisons) transcribed from the pinned coq9.0-wasm-2.2.0 sources with line-level provenance (`coq/Synth/WASM/WasmCertReference.v`) and proven refined by `exec_wasm_instr` (`WasmCertBridge.v`; lemma count: `artifacts/status.json`); the real external dep is nix-feasible, bazel-deferred on three named blockers (roadmap entry) |
| **Gate** | `VCR-VER-001` | Success = a previously load-bearing greedy-fix becomes *revertable*, with the full differential bit-identical and cycles equal-or-better | **demonstrated** (implemented; [evidence](scripts/repro/vcr_ver_001_gate.md)): the v0.11.20 reciprocal-mult cost-gate deleted outright (PR #322, bit-identical); the #496 exhaustion decline revertable behind `SYNTH_SPILL_ON_EXHAUST` — red case green, anchors byte-identical, declines 14→8; flip held on a measured i32-shape cycle regression |

Honest open items: the RV32 local-promotion flip is held on a failed no-grow gate (#601); float residuals — `trunc_sat` (0xFC prefix) is not decoded (functions using it loud-skip) and a pressure-dependent f32 class is open (#782); SIMD/Helium is untested on hardware.

**What it buys us:** synth stops being a real-ish compiler held together by oracle-gated patches and becomes a genuinely best-in-class *verified* compiler — and the verified selector DSL is the part that is potentially novel/publishable, not just catching up to Cranelift.

## Crate Map

| Crate | Purpose |
|-------|---------|
| `synth-cli` | CLI entry point (`synth compile`, `synth verify`, `synth disasm`) |
| `synth-core` | Shared types, error handling, `Backend` trait, WASM decoder |
| `synth-frontend` | WASM Component Model parser and validator |
| `synth-backend` | ARM Thumb-2 (Cortex-M) + A32 (Cortex-R5) encoder, ELF builder, vector table, linker scripts, MPU |
| `synth-backend-riscv` | RISC-V RV32IMAC backend (selector, encoder, relocatable ELF) — qemu_riscv32 / ESP32-C3 |
| `synth-backend-aarch64` | AArch64 (A64) host-native backend — integer subset, `-b aarch64` |
| `synth-backend-awsm` | aWsm backend integration (WASM-to-native via aWsm) |
| `synth-backend-wasker` | Wasker backend integration (WASM-to-Rust transpiler) |
| `synth-synthesis` | WASM-to-ARM instruction selection, peephole optimizer, pattern matcher |
| `synth-cfg` | Control flow graph construction and analysis |
| `synth-opt` | IR-level optimization passes (CSE, constant folding, DCE) |
| `synth-verify` | SMT translation validation — ordeal (pure-Rust QF_BV) default, Z3 feature-gated differential oracle |
| `synth-analysis` | SSA, control flow analysis, call graph |
| `synth-abi` | WebAssembly Component Model ABI (lift/lower) |
| `synth-memory` | Portable memory abstraction (Zephyr, Linux, bare-metal) |
| `synth-qemu` | QEMU integration for testing |
| `synth-test` | WAST-to-Robot Framework test generator for Renode |
| `synth-wit` | WIT (WebAssembly Interface Types) parser |

## Testing

```bash
# Run all Rust tests
cargo test --workspace

# Lint
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --check

# Bazel: Rocq proofs + Renode ARM Cortex-M4 emulation tests
bazel test //coq:verify_proofs
bazel test //tests/...
```

## Documentation

- [Architecture](ARCHITECTURE.md) -- compilation pipeline, components, binary emission
- [Synth & Loom](docs/architecture/SYNTH_LOOM_RELATIONSHIP.md) -- two-tier architecture
- [Feature Matrix](docs/status/FEATURE_MATRIX.md) -- what works, what doesn't (generated; numbers from `artifacts/status.json`)
- [Status (machine-derived)](artifacts/status.json) -- CI-re-derived counts: proofs, verified rules, backend coverage
- [Requirements](docs/requirements/REQUIREMENTS.md) -- functional and non-functional requirements
- [Research](docs/research/) -- literature review, formal methods, Sail/ARM analysis
- [Roadmap](artifacts/verified-codegen-roadmap.yaml) -- the VCR-* program (single source of truth for roadmap status; see also the [North Star section](#roadmap--north-star) and [Changelog](CHANGELOG.md))
- [Contributing](CONTRIBUTING.md) -- how to contribute

## License

Apache-2.0 -- see [LICENSE](LICENSE).

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; WebAssembly toolchain for safety-critical systems</sub>

</div>
