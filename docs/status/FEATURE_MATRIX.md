# Feature Matrix: Current State

**Last Updated:** March 2026

This document provides an honest assessment of what works, what doesn't, and what's planned.

---

## Legend

| Symbol | Meaning |
|--------|---------|
| Y | Working - tested and functional |
| P | Partial - implemented but incomplete or untested end-to-end |
| N | Not implemented |
| R | Research/experimental |

---

## Core Compiler Pipeline

| Component | Status | Notes |
|-----------|--------|-------|
| WASM/WAT parsing | Y | wasmparser + wat crate integration |
| WIT parsing | Y | Custom parser implemented |
| Instruction selection | P | i32/i64 integer ops compile to ARM; f32 with FPU; f64 rejected |
| Optimizer bridge | Y | Wires instruction selection into pipeline |
| Peephole optimizer | Y | Strength reduction, constant folding |
| ARM code generation | Y | Thumb-2 encoding, conditional execution |
| ELF emission | Y | Valid ARM ELF with sections, symbols |
| Cortex-M support | Y | Vector table, startup code, AAPCS ABI |
| **End-to-end CLI** | Y | **`synth compile input.wat -o output.elf` works** |
| Z3 formal verification | Y | SMT-based translation validation |

### What Works End-to-End

> `synth compile input.wat -o output.elf` takes a WAT file with i32/i64/f32 functions and produces a valid ARM ELF binary.
>
> `synth compile --demo add --verify` compiles and formally verifies the translation using Z3.
>
> 895 tests pass across the workspace with 0 failures.

---

## CLI Commands

| Command | Status | Notes |
|---------|--------|-------|
| `synth compile input.wat -o output.elf` | Y | i32/i64/f32 WASM to ARM ELF |
| `synth compile --all-exports -o output.elf` | Y | Multi-function compilation |
| `synth compile --cortex-m -o output.elf` | Y | Complete Cortex-M binary (vector table, startup) |
| `synth compile --demo add` | Y | Built-in demos: add, calc, calc-ext |
| `synth compile --verify` | Y | Compile + Z3 formal verification |
| `synth verify input.wat output.elf` | Y | Standalone translation validation |
| `synth disasm output.elf` | Y | Disassemble generated ELF |
| `synth parse input.wasm` | Y | Parse and analyze WASM components |
| `synth backends` | Y | List backends with capabilities |

---

## WebAssembly Operation Coverage

### Rust Instruction Selector (what actually compiles)

| Category | Ops | Compiles | Notes |
|----------|-----|----------|-------|
| i32 arithmetic | 14 | 14 | ADD, SUB, MUL, DIV_S/U, REM_S/U, AND, OR, XOR, SHL, SHR_S/U, ROTL, ROTR |
| i32 comparison | 11 | 11 | EQZ, EQ, NE, LT_S/U, GT_S/U, LE_S/U, GE_S/U |
| i32 bit manipulation | 3 | 3 | CLZ, CTZ, POPCNT |
| i32 other | ~8 | ~8 | CONST, EXTEND8S/16S, LOAD, STORE, etc. |
| i64 operations | 34 | 34 | Register-pair support (ADDS/ADC, SUBS/SBC, etc.) |
| f32 operations | 23 | 23 | VFP support (requires FPU-enabled target) |
| f64 operations | 20 | 0 | **Rejected** - single-precision targets only |
| Control flow | varies | P | Basic blocks; if/else/loop/br partially |
| Memory | 8 | P | i32 load/store; f32 load/store with FPU; f64 rejected |
| **Total** | **~151** | **~93** | **i32, i64, f32 (with FPU); f64 rejected** |

### Rocq Proof Coverage (formal verification model)

The Rocq model in `Compilation.v` covers more ops than the Rust compiler.
Some ops compile to `[]` (empty program) in the model, which is honest but trivial.

| Category | T1 (Result) | T2 (Exists) | T3 (Admitted) | Notes |
|----------|-------------|-------------|---------------|-------|
| i32 arithmetic | 6 | 0 | 0 | ADD, SUB, MUL, AND, OR, XOR |
| i32 division | 4 | 0 | 0 | DIV_S/U, REM_S/U |
| i32 bit manipulation | 3 | 0 | 0 | CLZ, CTZ, POPCNT |
| i32 comparisons | 11 | 11 | 0 | T1 flag-correspondence proofs |
| i32 shifts | 5 | 5 | 0 | T1 register-based shift proofs |
| i64 operations | 4 | 25 | 0 | T1 for div/rem; T2 for rest |
| i64 comparisons | 0 | 19 | 0 | T2 existence proofs |
| f32 operations | 0 | 20 | 0 | VFP semantics modeled (Phase 5) |
| f64 operations | 0 | 20 | 0 | VFP semantics modeled (Phase 5) |
| Conversions | 0 | 21 | 0 | VFP conversion semantics (Phase 5) |
| Memory | 0 | 8 | 0 | LDR/STR + VLDR/VSTR |
| Control/other | 6 | 29 | 0 | Simple ops, nop, drop, locals, globals |
| ArmRefinement | 0 | 0 | 2 | Sail integration placeholders |
| **Total** | **39** | **143** | **2** | **237 Qed / 2 Admitted** |

Tier definitions:
- **T1: Result Correspondence** -- ARM output register = WASM result value (strongest)
- **T2: Existence-Only** -- ARM execution succeeds, no claim about result value
- **T3: Admitted** -- Not yet proven (requires unmodeled semantics)

See [coq/STATUS.md](/coq/STATUS.md) for the full breakdown.

---

## Verification

| Feature | Status | Notes |
|---------|--------|-------|
| Z3 SMT translation validation | Y | Per-rule equivalence proofs |
| `--verify` CLI flag | Y | Invokes Z3 after compilation |
| `synth verify` command | Y | Standalone WASM <-> ELF validation |
| WASM semantics encoding | Y | 30+ operations modeled |
| ARM semantics encoding | Y | 20+ instructions modeled |
| Counterexample generation | Y | Reports failing inputs |
| Rocq proof suite | P | 237 Qed, 2 Admitted; 39 result-correspondence proofs |
| Sail ARM semantics | R | Evaluated, not implemented |

---

## Target Support

| Target | Status | Notes |
|--------|--------|-------|
| ARM Cortex-M4 (Thumb-2) | Y | Primary target, code generation works |
| ARM Cortex-M (generic) | Y | Vector table, startup, AAPCS ABI |
| ARM Cortex-M4F (FPU) | Y | VFP single-precision (f32) support |
| RISC-V | N | Not implemented |

---

## Embedded Features

| Feature | Status | Notes |
|---------|--------|-------|
| Vector table generation | Y | Tested in Cortex-M binaries |
| Reset handler / startup code | Y | Stack setup, function dispatch |
| AAPCS calling convention | Y | Params in r0-r3, return in r0 |
| ELF with proper sections | Y | .text, .symtab, .strtab, .shstrtab |
| Relocatable ELF (ET_REL) | Y | For linking with Kiln runtime |
| Linker script generation | P | Implemented, not tested with linker |
| MPU configuration | P | Implemented, not tested on hardware |

---

## Testing

| Type | Status | Coverage |
|------|--------|----------|
| Unit tests | Y | 895 tests, 100% pass |
| Z3 verification tests | Y | 53 tests |
| WAST compilation tests | Y | 23 cargo tests + 22 WAST files |
| Renode emulation tests | P | 3 robot files via Bazel rules_renode |
| Spec test suite | P | 267 files exist, adapter not built |
| Hardware tests | N | Never tested on real device |

---

## Summary

### What Works

1. **End-to-end compilation:** `synth compile input.wat -o output.elf` for i32, i64, and f32 (with FPU) functions
2. **Multi-function compilation:** `--all-exports` compiles all exported functions
3. **Cortex-M binaries:** `--cortex-m` generates complete embedded binaries
4. **Formal verification:** 39 result-correspondence proofs in Rocq, 53 Z3 verification tests
5. **895 tests pass** across the workspace

### What Doesn't Work

1. **F64 operations:** All f64 ops rejected (single-precision targets only)
2. **F32 without FPU:** f32 ops require FPU-enabled target (e.g., Cortex-M4F)
3. **Hardware testing:** No tests on real devices
4. **End-to-end execution validation:** No WASM -> ELF -> execute -> verify-result cycle

### Honest Framing

Synth is an early-stage WASM-to-ARM compiler with genuine formal verification of its i32 and i64 compilation paths. The 39 result-correspondence proofs in Rocq cover all i32 arithmetic, bitwise, comparison, shift/rotate, and i64 division operations. VFP f32 support is implemented for FPU-enabled targets. This is a strong foundation for a research compiler, not a production tool.
