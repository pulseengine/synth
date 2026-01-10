# Synth and Loom: Two-Tier Architecture

## Overview

Synth and Loom are companion projects with a clear division of responsibilities:

| Project | Repository | License | Purpose |
|---------|------------|---------|---------|
| **Loom** | [pulseengine/loom](https://github.com/pulseengine/loom) | Apache-2.0 | WebAssembly optimizer with Z3 verification |
| **Synth** | pulseengine/Synth (this repo) | Proprietary | WebAssembly synthesizer for embedded systems |

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                    LOOM (Open Source)                        │
│              github.com/pulseengine/loom                     │
├─────────────────────────────────────────────────────────────┤
│  Purpose: WebAssembly → Optimized WebAssembly                │
│  Verification: Z3 SMT translation validation                 │
│  Safety Level: ASIL B (automotive)                           │
│                                                              │
│  Components:                                                 │
│  ├── loom-shared    - ISLE rules, IR definitions (reusable) │
│  ├── loom-core      - Optimization pipeline                 │
│  ├── loom-cli       - Command-line tool                     │
│  └── loom-verify    - Z3 SMT verification                   │
│                                                              │
│  Optimizations:                                              │
│  • Constant folding, strength reduction                      │
│  • Function inlining, dead code elimination                  │
│  • Local CSE, block merging                                  │
│  • 80-95% binary size reduction                              │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ depends on (loom-shared crate)
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                   SYNTH (This Repository)                    │
│              github.com/pulseengine/Synth                    │
├─────────────────────────────────────────────────────────────┤
│  Purpose: WebAssembly → Native ARM/RISC-V for embedded       │
│  Verification: Coq mechanized proofs + Sail ARM semantics    │
│  Safety Level: ASIL D (automotive), IEC 62304 (medical)      │
│                                                              │
│  Components:                                                 │
│  ├── synth-frontend   - WASM Component Model parsing        │
│  ├── synth-synthesis  - Instruction selection (uses Loom)   │
│  ├── synth-backend    - ARM/RISC-V code generation          │
│  ├── synth-verify     - Z3 + Coq verification               │
│  └── coq/             - Mechanized correctness proofs       │
│                                                              │
│  Additional Capabilities:                                    │
│  • Native code generation (not just WASM optimization)       │
│  • MPU/PMP memory protection integration                     │
│  • Embedded target support (Cortex-M, RISC-V)               │
│  • Safety certification evidence generation                  │
└─────────────────────────────────────────────────────────────┘
```

## Why Two Projects?

### Different Verification Levels

| Aspect | Loom | Synth |
|--------|------|-------|
| **Verification Method** | Z3 SMT (runtime) | Coq proofs (compile-time) |
| **Proof Scope** | Per-optimization pass | Full compiler correctness |
| **ISA Semantics** | Manual encoding | Sail ARM (authoritative) |
| **Target Safety Level** | ASIL B | ASIL D |
| **Certification Path** | Testing + SMT | Formal verification |

### Loom Strengths (Reused by Synth)

1. **Proven Optimization Patterns** - Battle-tested ISLE rules
2. **Fast Verification** - Z3 SMT checks in milliseconds
3. **Comprehensive Test Suite** - WebAssembly edge cases covered
4. **Cost Models** - ARM instruction cost heuristics

### Synth Additions

1. **Mechanized Proofs** - Coq proofs of compiler correctness
2. **Authoritative Semantics** - Sail ARM specification integration
3. **Native Code Generation** - Direct ARM/RISC-V output
4. **Embedded Integration** - MPU, linker scripts, ELF generation
5. **Safety Certification** - ISO 26262, IEC 62304 evidence

## Data Flow

```
                    ┌─────────────┐
                    │  .wasm/.wat │
                    │   (input)   │
                    └──────┬──────┘
                           │
                           ▼
              ┌────────────────────────┐
              │   LOOM (optional)       │
              │   WASM → Optimized WASM │
              │   Z3 verification       │
              └───────────┬────────────┘
                          │
                          ▼
              ┌────────────────────────┐
              │   SYNTH                 │
              │   WASM → Native Code    │
              │   Coq-verified rules    │
              └───────────┬────────────┘
                          │
                          ▼
                    ┌─────────────┐
                    │   .elf      │
                    │  (output)   │
                    └─────────────┘
```

## Integration Points

### 1. loom-shared Crate

Synth can depend on `loom-shared` for:
- ISLE term definitions
- WebAssembly IR types
- Optimization rule patterns

```toml
# Synth's Cargo.toml (future)
[dependencies]
loom-shared = { git = "https://github.com/pulseengine/loom" }
```

### 2. Optimization Pipeline

Loom's 12-phase optimization pipeline can preprocess WASM before Synth's native code generation:

1. Loom optimizes WASM (size reduction, simplification)
2. Synth synthesizes optimized WASM to native code
3. Both verify their transformations independently

### 3. Test Suite Sharing

Loom's test cases validate WASM semantics; Synth extends these to verify native code generation.

## Current Status

| Integration | Status |
|-------------|--------|
| Loom as optional preprocessor | Planned |
| loom-shared dependency | Planned |
| Shared test suite | Planned |
| Independent operation | **Working** |

Currently, Synth operates independently with its own optimization passes. Loom integration is a future enhancement.

## Summary

- **Loom** = Open-source WASM optimizer (ASIL B, Z3 verified)
- **Synth** = Embedded WASM synthesizer (ASIL D, Coq verified)
- **Relationship** = Synth can use Loom's optimizations, but adds native codegen and stronger verification
- **Key Difference** = Verification depth (Z3 runtime vs Coq compile-time proofs)
