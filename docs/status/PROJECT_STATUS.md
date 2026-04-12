# Synth Project Status

Last updated: 2026-04-12

Synth is a WebAssembly-to-ARM Cortex-M compiler with mechanized correctness proofs.
**This is pre-release software. It has not been tested on physical hardware.**

## Crates (16)

| Crate | Purpose | Status |
|-------|---------|--------|
| synth-cli | CLI (`synth compile`, `synth verify`, `synth disasm`) | Implemented |
| synth-core | Shared types, error handling, WASM decoder | Implemented |
| synth-frontend | WASM Component Model parser and validator | Implemented |
| synth-backend | ARM Thumb-2 encoder, ELF builder, vector table, linker | Implemented |
| synth-backend-awsm | aWsm backend integration | Partial |
| synth-backend-wasker | Wasker backend integration | Partial |
| synth-synthesis | WASM to ARM instruction selection, pattern matcher | Implemented |
| synth-cfg | Control flow graph construction and analysis | Implemented |
| synth-opt | IR optimization passes (CSE, constant folding, DCE) | Implemented |
| synth-verify | Z3 SMT translation validation | Implemented |
| synth-analysis | SSA, control flow analysis, call graph | Implemented |
| synth-abi | WebAssembly Component Model ABI (lift/lower) | Implemented |
| synth-memory | Portable memory abstraction (Zephyr, Linux, bare-metal) | Partial |
| synth-qemu | QEMU integration for testing | Implemented |
| synth-test | WAST to Robot Framework test generator for Renode | Implemented |
| synth-wit | WIT parser | Implemented |

## Tests

895 tests passing, 0 failing (cargo test --workspace, 2026-04-12).

## Formal Verification

### Rocq (Coq) Proofs

237 Qed / 2 Admitted across all `.v` files in `coq/Synth/`.

| Tier | Meaning | Count |
|------|---------|-------|
| T1: Result correspondence | ARM output = WASM result value | 39 |
| T2: Existence-only | ARM execution succeeds (no result claim) | 143 |
| T3: Admitted | Not yet proven (Sail integration placeholders) | 2 |
| Infrastructure | Integer properties, state lemmas, flag lemmas | 55 |

See `coq/STATUS.md` for the per-file breakdown.

### Kani (Bounded Model Checking)

18 proof harnesses in `crates/synth-backend/tests/kani_arm_encoding.rs`.

### Z3 (SMT Translation Validation)

110 Z3-based tests in synth-verify (57 unit + 53 comprehensive).

### Verus (Deductive Verification)

8 spec functions in `crates/synth-synthesis/src/contracts.rs` covering register allocation,
instruction encoding, memory access, and division trap invariants.

## What Works

- **i32 operations**: All arithmetic, bitwise, comparison, shift/rotate, division.
  Fully implemented, tested, and proven (39 T1 result-correspondence proofs in Rocq).
- **i64 operations**: Register-pair architecture for 64-bit on ARM32.
  Implemented and tested. Rocq proofs at T2 level (execution succeeds) plus 4 T1 division proofs.
- **f32/f64 operations**: VFP single/double precision. Implemented and tested.
  Rocq proofs at T2 level using abstract VFP axioms (not Flocq IEEE 754).
- **Control flow**: block, loop, br, br_if, br_table, call, return.
- **Memory**: i32/i64/f32/f64 load/store with bounds checking.
- **ELF output**: Produces bare-metal ELF binaries for Cortex-M4.
- **Renode emulation tests**: WAST-derived Robot Framework tests run on emulated Cortex-M4.

## What Is Partial

- **i64 proofs**: T2 existence proofs only (except division). No T1 result correspondence for
  arithmetic, bitwise, comparison, or shift operations.
- **Float proofs**: T2 existence proofs using abstract axioms. Upgrading to T1 requires Flocq
  IEEE 754 integration.
- **Component Model**: WIT parser and ABI lift/lower implemented; end-to-end integration incomplete.
- **Alternative backends**: awsm and wasker backends are stubs/partial.

## What Is Missing

- No testing on physical ARM hardware (Renode emulation only).
- No WASI support.
- No SIMD (v128) operations.
- No reference types.
- No multi-memory.
- No bulk memory operations.
- No performance benchmarks.
