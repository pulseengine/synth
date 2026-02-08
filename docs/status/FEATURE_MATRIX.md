# Feature Matrix: Current State

**Last Updated:** February 2026

This document provides an honest assessment of what works, what doesn't, and what's planned.

---

## Legend

| Symbol | Meaning |
|--------|---------|
| ✅ | Working - tested and functional |
| ⚠️ | Partial - implemented but incomplete or untested end-to-end |
| ❌ | Not implemented |
| 🔬 | Research/experimental |

---

## Core Compiler Pipeline

| Component | Status | Notes |
|-----------|--------|-------|
| WASM/WAT parsing | ✅ | wasmparser + wat crate integration |
| WIT parsing | ✅ | Custom parser implemented |
| Instruction selection | ✅ | 151/151 WASM Core 1.0 ops → ARM |
| Optimizer bridge | ✅ | Wires instruction selection into pipeline |
| Peephole optimizer | ✅ | Strength reduction, constant folding |
| Register allocation | ✅ | Graph coloring, AAPCS-compliant |
| ARM code generation | ✅ | Thumb-2 encoding, conditional execution |
| ELF emission | ✅ | Valid ARM ELF with sections, symbols |
| Cortex-M support | ✅ | Vector table, startup code, AAPCS ABI |
| **End-to-end CLI** | ✅ | **`synth compile input.wat -o output.elf` works** |
| Multi-backend arch | ✅ | Backend trait, registry, 4 backends registered |
| Z3 formal verification | ✅ | SMT-based translation validation |

### What Works End-to-End

> `synth compile input.wat -o output.elf` takes a WAT file and produces a valid ARM ELF binary.
>
> `synth compile --demo add --verify` compiles and formally verifies the translation using Z3.
>
> 496 tests pass across 18 crates with 0 failures.

---

## CLI Commands

| Command | Status | Notes |
|---------|--------|-------|
| `synth compile input.wat -o output.elf` | ✅ | Single-function WASM → ARM ELF |
| `synth compile --all-exports -o output.elf` | ✅ | Multi-function compilation |
| `synth compile --cortex-m -o output.elf` | ✅ | Complete Cortex-M binary (vector table, startup) |
| `synth compile --demo add` | ✅ | Built-in demos: add, calc, calc-ext |
| `synth compile --verify` | ✅ | Compile + Z3 formal verification |
| `synth compile --backend arm\|w2c2` | ⚠️ | ARM functional, others return stubs |
| `synth verify input.wat output.elf` | ✅ | Standalone translation validation |
| `synth disasm output.elf` | ✅ | Disassemble generated ELF |
| `synth parse input.wasm` | ✅ | Parse and analyze WASM components |
| `synth backends` | ✅ | List backends with capabilities |
| `synth synthesize` | ⚠️ | Scaffold only, pipeline not wired |
| `synth target-info` | ⚠️ | Basic target information |

---

## WebAssembly Operations

| Category | Operations | Unit Tests | Synthesis Rules | Verified (Z3) |
|----------|------------|------------|-----------------|----------------|
| i32 arithmetic | 52 | ✅ 100% | ✅ 100% | ✅ core ops |
| i64 arithmetic | 40 | ✅ 100% | ✅ 100% | ⚠️ partial |
| f32 operations | 29 | ✅ 100% | ✅ 100% | ❌ |
| f64 operations | 30 | ✅ 100% | ✅ 100% | ❌ |
| **Total** | **151** | **✅ 100%** | **✅ 100%** | **⚠️ i32 core** |

### Coverage Details

- ✅ All 151 WASM Core 1.0 operations have synthesis rules with unit tests
- ✅ Core i32 operations verified via Z3 SMT solver (add, sub, mul, and, or, xor)
- ✅ 53 comprehensive Z3 verification tests pass
- ⚠️ Not all operations tested through full compile → ELF → execute path
- ⚠️ Control flow (if/else, loop, br) has rules but not tested end-to-end

---

## Multi-Backend Architecture

| Backend | Status | `compile_function()` | `compile_module()` |
|---------|--------|---------------------|--------------------|
| ARM (built-in) | ✅ | ✅ Works | ✅ Works |
| w2c2 | ⚠️ | ❌ Stub | ❌ Stub |
| aWsm | ⚠️ | ❌ Stub | ❌ Stub |
| wasker | ⚠️ | ❌ Stub | ❌ Stub |

### Backend Trait

All backends implement `Backend` trait with: `name()`, `version()`, `is_available()`, `capabilities()`, `compile_function()`, `compile_module()`. BackendRegistry provides centralized discovery.

---

## Verification

| Feature | Status | Notes |
|---------|--------|-------|
| Z3 SMT translation validation | ✅ | Per-rule equivalence proofs |
| `--verify` CLI flag | ✅ | Invokes Z3 after compilation |
| `synth verify` command | ✅ | Standalone WASM ↔ ELF validation |
| WASM semantics encoding | ✅ | 30+ operations modeled |
| ARM semantics encoding | ✅ | 20+ instructions modeled |
| Counterexample generation | ✅ | Reports failing inputs |
| Parameterized verification | ✅ | Range-based testing |
| Coq proofs | 🔬 | Research artifacts, not integrated |
| Sail ARM semantics | 🔬 | Evaluated, not implemented |

---

## Target Support

| Target | Status | Notes |
|--------|--------|-------|
| ARM Cortex-M4 (Thumb-2) | ✅ | Primary target, code generation works |
| ARM Cortex-M (generic) | ✅ | Vector table, startup, AAPCS ABI |
| ARM Cortex-M4F (FPU) | ⚠️ | FPU rules exist, not tested end-to-end |
| ARM Cortex-M7 | ❌ | Not implemented |
| RISC-V | ❌ | Not implemented |

---

## Embedded Features

| Feature | Status | Notes |
|---------|--------|-------|
| Vector table generation | ✅ | Tested in Cortex-M binaries |
| Reset handler / startup code | ✅ | Stack setup, function dispatch |
| AAPCS calling convention | ✅ | Params in r0-r3, return in r0 |
| ELF with proper sections | ✅ | .text, .symtab, .strtab, .shstrtab |
| Linker script generation | ⚠️ | Implemented, not tested with linker |
| MPU configuration | ⚠️ | Implemented, not tested on hardware |
| Bounds-checked memory | ⚠️ | `--bounds-check` flag, synthesis rules exist |
| XIP (execute in place) | ❌ | Not implemented |

---

## Build System

| System | Status | Notes |
|--------|--------|-------|
| Cargo | ✅ | 496 tests pass, 18 crates |
| Bazel | ⚠️ | BUILD files for 17/18 crates, synth-memory missing |
| CI/CD | ❌ | No GitHub Actions yet |

---

## Testing

| Type | Status | Coverage |
|------|--------|----------|
| Unit tests | ✅ | 496 tests, 100% pass |
| Z3 verification tests | ✅ | 53 comprehensive tests |
| WAST test files | ⚠️ | 22 files exist, runner not wired |
| Spec test suite | ⚠️ | 267 files exist, adapter not built |
| Integration tests | ⚠️ | Binary validation tests exist |
| QEMU/Renode tests | ❌ | Config files exist, not wired |
| Hardware tests | ❌ | Never tested on real device |

---

## Workspace Structure

18 crates:

| Crate | Purpose |
|-------|---------|
| synth-core | WasmOp, Backend trait, TargetSpec |
| synth-frontend | WASM/WIT parsing |
| synth-synthesis | Instruction selection, rules, optimizer bridge |
| synth-backend | ARM encoding, ELF emission, Cortex-M |
| synth-regalloc | Graph coloring register allocation |
| synth-opt | Optimization passes |
| synth-verify | Z3 SMT translation validation |
| synth-cli | CLI (compile, verify, disasm, backends) |
| synth-test | Test infrastructure |
| synth-memory | Memory architecture (new) |
| synth-wit | WIT type system |
| synth-component | Component model |
| synth-types | Type definitions |
| synth-ir | Intermediate representation |
| synth-safety | Safety annotations |
| synth-loom | Loom integration |
| synth-codegen-traits | Code generation traits |
| synth-macro | Procedural macros |

---

## Documentation

| Category | Count | Notes |
|----------|-------|-------|
| Architecture docs | 10+ | Crate structure, Loom relationship |
| Design docs | 5+ | Memory architecture, WAST test design |
| Research docs | 7+ | Cranelift, Sail ARM, verification ecosystem |
| Analysis docs | 5+ | Build system, QEMU vs Renode, LLVM strategy |
| Status docs | 3 | Feature matrix, progress, project status |
| Validation docs | 2 | Formal verification, validation report |
| **Total** | **91+** | Well-organized under docs/ |

---

## Summary

### What Works

1. **End-to-end compilation:** `synth compile input.wat -o output.elf` produces valid ARM ELF
2. **Multi-function compilation:** `--all-exports` compiles all exported functions
3. **Cortex-M binaries:** `--cortex-m` generates complete embedded binaries
4. **Formal verification:** `--verify` proves translation correctness via Z3
5. **Multi-backend architecture:** Backend trait with registry, ARM backend functional
6. **CLI:** 8 commands (compile, verify, disasm, backends, parse, synthesize, target-info)
7. **496 tests pass** across 18 crates

### What Doesn't Work Yet

1. **End-to-end execution:** No WASM → ELF → execute → verify-result cycle
2. **External backends:** w2c2/aWsm/wasker stubs not implemented
3. **CI/CD:** No automated testing pipeline
4. **Hardware/emulator testing:** No QEMU or Renode integration
5. **Control flow end-to-end:** if/else/loop rules exist but untested through compile

### Next Steps

See [ROADMAP.md](/ROADMAP.md) for the plan.
