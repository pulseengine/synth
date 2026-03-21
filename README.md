<div align="center">

# Synth

<sup>WebAssembly-to-ARM Cortex-M AOT compiler with mechanized correctness proofs</sup>

&nbsp;

[![CI](https://github.com/pulseengine/synth/actions/workflows/ci.yml/badge.svg)](https://github.com/pulseengine/synth/actions/workflows/ci.yml)
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

Synth compiles WebAssembly to native ARM Cortex-M machine code, producing bare-metal ELF binaries for embedded targets. It supports 197+ WASM opcodes (i32, i64, f32, f64, SIMD/Helium), full control flow, memory operations, and globals. Pattern-based instruction selection, AAPCS calling conventions, and ELF generation -- with mechanized correctness proofs in [Rocq](https://rocq-prover.org/) (formerly Coq) and SMT-based translation validation via Z3.

Part of [PulseEngine](https://github.com/pulseengine) -- a WebAssembly toolchain for safety-critical systems with mechanized verification:

| Project | Role |
|---------|------|
| [**Synth**](https://github.com/pulseengine/synth) | WASM-to-ARM compiler with Rocq proofs |
| [**Loom**](https://github.com/pulseengine/loom) | WASM optimizer with Z3 verification |
| [**Meld**](https://github.com/pulseengine/meld) / [**Kiln**](https://github.com/pulseengine/kiln) | Platform runtime and build orchestration |
| [**Sigil**](https://github.com/pulseengine/sigil) | Attestation and signing |

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

# Formally verify the translation
synth verify examples/wat/simple_add.wat firmware.elf
```

## Features

| Category | Status |
|----------|--------|
| i32 arithmetic, bitwise, comparison, shift/rotate | Supported |
| i64 arithmetic (register pairs) | Supported |
| f32/f64 via VFP | Supported |
| WASM SIMD via ARM Helium MVE | Supported (Cortex-M55) |
| Control flow (block, loop, if/else, br, br_if, br_table) | Supported |
| Function calls (direct, indirect) | Supported |
| Memory (load/store, sub-word, size/grow) | Supported |
| Globals, select, unreachable, nop | Supported |
| ELF output with vector table | Supported |
| Linker scripts (STM32, nRF52840, generic) | Supported |
| Cross-compilation via arm-none-eabi-gcc | Supported |
| Rocq mechanized proofs | 188 Qed / 52 Admitted |
| Z3 translation validation | 53 tests passing |
| WebAssembly spec test suite | 227/257 files compile |

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

Synth employs two complementary verification strategies.

### Rocq proof suite

Mechanized proofs in Rocq 9 show that `compile_wasm_to_arm` preserves WASM semantics for each operation. The proof suite lives in `coq/Synth/` and covers ARM instruction semantics, WASM stack-machine semantics, and per-operation correctness theorems.

```
188 Qed  /  52 Admitted
  T1: 39 result-correspondence (ARM output = WASM result)
  T2: 95 existence-only (ARM execution succeeds)
  T3: 52 admitted (VFP/float semantics)
```

All i32 operations (arithmetic, division, comparison, bit-manip, shift/rotate) have full T1 proofs.

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
