<div align="center">

# Synth

<sup>WebAssembly-to-ARM Cortex-M AOT compiler with mechanized correctness proofs</sup>

&nbsp;

[![CI](https://github.com/pulseengine/synth/actions/workflows/ci.yml/badge.svg)](https://github.com/pulseengine/synth/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/pulseengine/synth/graph/badge.svg)](https://codecov.io/gh/pulseengine/synth)
![Rust](https://img.shields.io/badge/Rust-CE422B?style=flat-square&logo=rust&logoColor=white&labelColor=1a1b27)
![WebAssembly](https://img.shields.io/badge/WebAssembly-654FF0?style=flat-square&logo=webassembly&logoColor=white&labelColor=1a1b27)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square&labelColor=1a1b27)

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

Synth is an ahead-of-time compiler from WebAssembly to ARM Cortex-M machine code. It produces bare-metal ELF binaries targeting embedded microcontrollers. The compiler handles i32, i64 (via register pairs), f32/f64 (via VFP), control flow, and memory operations. Mechanized correctness proofs in [Rocq](https://rocq-prover.org/) cover the i32 instruction selection; i64/float/SIMD proofs are not yet done.

**This is pre-release software.** It has not been tested on real hardware. The generated ARM code passes unit tests and compiles 227/257 WebAssembly spec test files, but execution on Cortex-M silicon is unverified. Use at your own risk.

Part of [PulseEngine](https://github.com/pulseengine) -- a WebAssembly toolchain for safety-critical embedded systems:

| Project | Role |
|---------|------|
| [**Synth**](https://github.com/pulseengine/synth) | WASM-to-ARM AOT compiler with Rocq proofs |
| [**Loom**](https://github.com/pulseengine/loom) | WASM optimizer with Z3 verification |
| [**Meld**](https://github.com/pulseengine/meld) | WASM Component Model static fuser |
| [**Kiln**](https://github.com/pulseengine/kiln) | WASM runtime for safety-critical systems |
| [**Sigil**](https://github.com/pulseengine/sigil) | Supply chain attestation and signing |

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

To use Z3 translation validation, rebuild with the `verify` feature (requires Z3 on your system):

```bash
cargo build --release -p synth-cli --features verify
synth verify examples/wat/simple_add.wat firmware.elf
```

## Features

| Category | Status | Notes |
|----------|--------|-------|
| i32 arithmetic, bitwise, comparison, shift/rotate | **Tested** | Full Rocq T1 proofs, Renode execution tests |
| i64 arithmetic (register pairs) | **Tested** | ADDS/ADC, SUBS/SBC, UMULL; unit tests only |
| f32/f64 via VFP | Implemented | Requires FPU-equipped target (M4F, M7); Rocq proofs admitted |
| WASM SIMD via ARM Helium MVE | Experimental | Cortex-M55 only; encoding untested on hardware |
| Control flow (block, loop, if/else, br, br_table) | **Tested** | Renode execution tests, complex test suite |
| Function calls (direct, indirect) | Implemented | Unit tests; inter-function calls not Renode-tested |
| Memory (load/store, sub-word, size/grow) | Implemented | memory.grow returns -1 on embedded (fixed memory) |
| Globals, select | Implemented | R9-based globals; unit tests only |
| ELF output with vector table | Implemented | Thumb bit set on symbols; not linked on real hardware |
| Linker scripts (STM32, nRF52840, generic) | Implemented | Generated, not tested with real boards |
| Cross-compilation (`--link` flag) | Implemented | Requires `arm-none-eabi-gcc` in PATH; not CI-tested |
| Rocq mechanized proofs | 188 Qed / 52 Admitted | Only i32 has result-correspondence (T1); all 52 admits are float/VFP |
| Z3 translation validation | 53 tests passing | Covers i32 arithmetic and comparison rules |
| WebAssembly spec test suite | 227/257 compile | Compilation only — not executed on emulator |

### What doesn't work yet

- **No real hardware testing** — all testing is unit tests and Renode emulation
- **No multi-memory** — fused components from meld need single-memory mode
- **No WASI on embedded** — kiln-builtins crate doesn't exist yet
- **No component model execution** — components compile but can't run without kiln-builtins + cabi_realloc
- **Register allocator is naive** — wrapping allocation with reserved register exclusion, no graph coloring
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
| **Rocq** | Partial | 188 Qed / 52 Admitted — only i32 has T1 result-correspondence proofs |
| **Kani** | Starting | 20 bounded model checking harnesses for ARM encoder |
| **Verus** | Not started | No requires/ensures specs on Rust functions |
| **Lean** | Not started | — |

See `artifacts/verification-gaps.yaml` for the detailed gap analysis (VG-001 through VG-008).

### Rocq proof suite

Mechanized proofs in Rocq 9 show that `compile_wasm_to_arm` preserves WASM semantics for each operation. The proof suite lives in `coq/Synth/` and covers ARM instruction semantics, WASM stack-machine semantics, and per-operation correctness theorems.

```
188 Qed  /  52 Admitted
  T1: 39 result-correspondence (ARM output = WASM result)  — i32 only
  T2: 95 existence-only (ARM execution succeeds, no result claim)
  T3: 52 admitted (VFP/float semantics — not yet proven)
```

Only i32 operations have full T1 (result-correspondence) proofs. The i64, f32, f64, and SIMD instruction selection has NO mechanized proofs — correctness relies on unit tests and the Z3 translation validation. The 52 admitted theorems all require VFP floating-point semantics that are not yet modeled in Rocq.

Build the proofs:

```bash
# Hermetic build via Bazel + Nix
bazel test //coq:verify_proofs

# Or locally with Rocq 9
cd coq && make proofs
```

See [coq/STATUS.md](coq/STATUS.md) for the per-file coverage matrix.

### Z3 SMT translation validation

The `synth-verify` crate encodes WASM and ARM semantics as Z3 formulas and checks per-rule equivalence. The `--verify` CLI flag invokes this after compilation; `synth verify` provides standalone validation. 53 Z3 verification tests pass in CI.

## Crate Map

| Crate | Purpose |
|-------|---------|
| `synth-cli` | CLI entry point (`synth compile`, `synth verify`, `synth disasm`) |
| `synth-core` | Shared types, error handling, `Backend` trait |
| `synth-backend` | ARM encoder, ELF builder, vector table, linker scripts, MPU |
| `synth-synthesis` | WASM-to-ARM instruction selection, peephole optimizer |
| `synth-verify` | Z3 SMT translation validation |
| `synth-analysis` | SSA, control flow analysis |
| `synth-abi` | WebAssembly Component Model ABI (lift/lower) |
| `synth-memory` | Portable memory abstraction (Zephyr, Linux, bare-metal) |
| `synth-test` | WAST-to-Robot Framework test generator for Renode |

## Testing

```bash
# Run all Rust tests (851 tests across workspace)
cargo test --workspace

# Lint
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --check

# Bazel: Rocq proofs + Renode ARM Cortex-M4 emulation tests
bazel test //coq:verify_proofs
bazel test //tests/...
```

## Documentation

- [Architecture](ARCHITECTURE.md) -- compilation pipeline, ARM instruction mapping, benchmarks
- [Architecture Vision](docs/architecture/ARCHITECTURE_VISION.md) -- full system design and roadmap
- [Synth & Loom](docs/architecture/SYNTH_LOOM_RELATIONSHIP.md) -- two-tier architecture
- [Feature Matrix](docs/status/FEATURE_MATRIX.md) -- what works, what doesn't
- [Requirements](docs/requirements/REQUIREMENTS.md) -- functional and non-functional requirements
- [Research](docs/research/) -- literature review, formal methods, Sail/ARM analysis
- [Roadmap](ROADMAP.md) -- development phases
- [Changelog](CHANGELOG.md) -- version history
- [Contributing](CONTRIBUTING.md) -- how to contribute

## License

Apache-2.0 -- see [LICENSE](LICENSE).

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; WebAssembly toolchain for safety-critical systems</sub>

</div>
