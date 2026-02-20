<div align="center">

# Synth

<sup>WebAssembly synthesis for embedded systems</sup>

&nbsp;

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

Meld fuses. Loom weaves. Synth transpiles. Kiln fires. Sigil seals.

Synth transpiles WebAssembly to native ARM for embedded Cortex-M targets. Not just translation — program synthesis: exploring equivalent implementations for provably optimal native code. Pattern-based instruction selection, AAPCS calling conventions, and ELF generation. Translation validation ensures the transpiled output faithfully preserves WebAssembly semantics.

Designed for safety-critical systems with formal verification and certification pathways for automotive (ISO 26262), medical (IEC 62304), and industrial environments.

## Quick Start

```bash
# Clone and build
git clone https://github.com/pulseengine/synth.git
cd synth
cargo build --release -p synth-cli

# Transpile WAT/WASM to ARM ELF
synth compile examples/wat/simple_add.wat -o add.elf

# Disassemble to verify output
synth disasm add.elf

# Or use Bazel
bazel build //crates:synth
```

## Current Status

**Phase 1 Build System complete, Phase 2 Calculator Demo in progress.**

### Working

- WASM/WAT file parsing and decoding
- Pattern-based instruction selection (WASM to ARM)
- ARM binary encoding
- ELF file generation
- CLI: `synth compile` and `synth disasm`
- Bazel build system

### In Progress

- Register allocation (regalloc2 integration)
- QEMU testing infrastructure
- Full function prologue/epilogue generation
- Zephyr RTOS integration

See [ROADMAP.md](ROADMAP.md) for detailed progress.

## Synthesis Pipeline

```
Frontend: Parse & Validate (WebAssembly Components + WIT)
    ↓
Analysis: Whole-Program (dependencies, memory layout, call graph)
    ↓
Optimization: E-Graph Synthesis (equality saturation, ISLE rewrites)
    ↓
Synthesis: Target-Specific Lowering (ISLE instruction selection, MPU/PMP)
    ↓
Verification: Formal Validation (SMT translation validation, memory safety)
    ↓
Backend: Binary Emission (ELF generation, debug info)
```

### Key Technologies

- **E-Graphs (egg)** — Equality saturation for optimization
- **ISLE** — Declarative instruction selection and lowering
- **regalloc2** — Fast register allocation
- **Z3** — SMT solver for translation validation
- **wasm-tools** — Component Model parsing and validation

## Synth and Loom

Synth is part of a two-tier architecture with [Loom](https://github.com/pulseengine/loom):

| Project | Purpose | Safety Level |
|---------|---------|--------------|
| **Loom** | WASM optimizer with Z3 verification | ASIL B |
| **Synth** | Native code synthesizer with Rocq proofs | ASIL D |

See [docs/architecture/SYNTH_LOOM_RELATIONSHIP.md](docs/architecture/SYNTH_LOOM_RELATIONSHIP.md) for details.

## Formal Verification

> [!NOTE]
> **Cross-cutting verification** &mdash; Rocq mechanized proofs, Kani bounded model checking, Z3 SMT verification, and Verus Rust verification are used across the PulseEngine toolchain. Sigil attestation chains bind it all together.

## Documentation

- [Architecture](docs/architecture/ARCHITECTURE.md) — System design and crate structure
- [Requirements](docs/requirements/REQUIREMENTS.md) — Functional and non-functional requirements
- [PoC Plan](docs/poc/POC_PLAN.md) — Proof-of-concept implementation plan
- [Project Status](docs/status/PROJECT_STATUS.md) — Current implementation state
- [Research](docs/research/) — Literature review, formal methods, Sail/ARM analysis
- [Changelog](CHANGELOG.md) — Version history

## License

Apache-2.0

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; formally verified WebAssembly toolchain for safety-critical systems</sub>

</div>
