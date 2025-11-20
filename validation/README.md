# Synth Compiler Validation Framework

This directory contains the validation infrastructure for testing our formally verified WASM-to-ARM compiler against the official ARM Sail ISA specifications.

## Overview

**Goal**: Validate that our proven compiler generates ARM code that executes identically to the official ARM architecture specification.

**Method**: Executable testing - compare execution results between:
1. Our extracted Coq compiler (OCaml) executing WASM programs
2. Sail ARM emulator (C) executing the generated ARM code

## Architecture

```
┌──────────────┐
│ WASM Program │
└──────┬───────┘
       │
       │ [Our Verified Compiler - OCaml]
       ▼
┌──────────────┐
│  ARM Code    │
└──────┬───────┘
       │
       ├─────────────────────────────┐
       │                             │
       ▼                             ▼
┌─────────────────┐          ┌─────────────────┐
│ Sail ARM        │          │ Our ARM         │
│ Emulator (C)    │          │ Semantics (OCaml)│
│ [Official Ref]  │          │ [Verified]      │
└────────┬────────┘          └────────┬────────┘
         │                            │
         ▼                            ▼
    ┌─────────┐                  ┌─────────┐
    │ State₁  │                  │ State₂  │
    └────┬────┘                  └────┬────┘
         │                            │
         └──────────┬─────────────────┘
                    ▼
              ┌───────────┐
              │  Compare  │
              │ Registers │
              │ Memory    │
              │ Flags     │
              └───────────┘
```

## Directory Structure

```
validation/
├── README.md              # This file
├── test_driver/           # Test execution framework
│   ├── driver.ml          # Main test driver
│   ├── comparator.ml      # Result comparison
│   └── dune               # Build configuration
├── test_cases/            # Test suite
│   ├── wasm/              # WASM test programs
│   │   ├── arithmetic.wasm
│   │   ├── control_flow.wasm
│   │   └── memory.wasm
│   ├── expected/          # Expected results
│   └── generator/         # Test case generator
├── sail_interface/        # Sail emulator wrapper
│   ├── sail_wrapper.c     # C wrapper for Sail
│   ├── sail_wrapper.ml    # OCaml FFI bindings
│   └── dune
└── results/               # Test results and reports
    ├── coverage.md        # Coverage analysis
    └── validation.md      # Validation report
```

## Components

### 1. Extracted Compiler (OCaml)
- Location: `../extracted/`
- Generated from: Coq proofs via extraction
- Contains: Compiler, WASM semantics, ARM semantics

### 2. Sail ARM Emulator (C)
- Location: `../external/sail-arm/arm-v8.5-a/aarch64`
- Built from: Official ARM Sail specifications
- Represents: Ground truth ARM architecture behavior

### 3. Test Driver (OCaml)
- Orchestrates test execution
- Loads WASM programs
- Compiles via our compiler
- Executes on both implementations
- Compares results

### 4. Test Suite
- **WASM Conformance**: Official WASM test suite
- **Instruction Coverage**: One test per ARM instruction we use
- **Edge Cases**: Boundary conditions, corner cases
- **Integration**: Full programs (Fibonacci, factorial, etc.)

## Test Categories

### Category 1: Instruction-Level Tests
Each ARM instruction we generate gets a dedicated test:
- Arithmetic: ADD, SUB, MUL, SDIV, UDIV
- Bitwise: AND, OR, XOR, NOT
- Memory: LDR, STR
- Control: B, BEQ, BNE, etc.

### Category 2: WASM Operation Tests
Each of 151 WASM operations:
- i32 operations (constants, arithmetic, comparisons)
- i64 operations
- f32/f64 operations (floating-point)
- Memory operations (load/store)
- Control flow (if, loop, call)

### Category 3: Integration Tests
Complete programs:
- Fibonacci (recursion + arithmetic)
- Factorial (recursion + control flow)
- Array sum (memory + loops)
- Bubble sort (complex control + memory)

### Category 4: Property-Based Tests
Random program generation testing:
- QuickCheck-style property testing
- Fuzz testing with random WASM programs
- Ensure consistency across all inputs

## Validation Metrics

### Coverage Metrics
- **Instruction Coverage**: % of ARM instructions tested
- **Operation Coverage**: % of WASM operations tested
- **Branch Coverage**: % of control flow paths tested
- **Boundary Coverage**: % of edge cases tested

### Correctness Metrics
- **Pass Rate**: % of tests with matching results
- **Discrepancy Rate**: % of tests with mismatches
- **Bug Discovery**: Issues found in either implementation

### Confidence Level
Target: 99.99% confidence via:
- 1000+ test cases
- 100% instruction coverage
- Property-based random testing
- Manual review of critical paths

## Running Validation

### Prerequisites
```bash
# OCaml toolchain
opam install dune ctypes

# Build extracted compiler
cd ../extracted && dune build

# Build Sail emulator (done separately)
cd ../external/sail-arm/arm-v8.5-a && make aarch64
```

### Execute Tests
```bash
# Run full validation suite
cd validation
dune exec ./test_driver/driver.exe -- --all

# Run specific category
dune exec ./test_driver/driver.exe -- --category arithmetic

# Run single test
dune exec ./test_driver/driver.exe -- --test fibonacci

# Generate report
dune exec ./test_driver/driver.exe -- --report results/validation.md
```

## Test Result Format

Each test produces:
```json
{
  "test_name": "i32_add_simple",
  "category": "arithmetic",
  "wasm_program": "...",
  "arm_code": ["ADD R0, R0, R1"],
  "sail_result": {
    "registers": {"R0": 42, "R1": 0, ...},
    "flags": {"N": false, "Z": false, "C": false, "V": false},
    "memory": {}
  },
  "synth_result": {
    "registers": {"R0": 42, "R1": 0, ...},
    "flags": {"N": false, "Z": false, "C": false, "V": false},
    "memory": {}
  },
  "status": "PASS",
  "execution_time_ms": 1.2
}
```

## ISO 26262 Certification Evidence

This validation provides tool qualification evidence per ISO 26262-8 §11.4.5:

**Evidence Package**:
1. **Test Plan**: This README
2. **Test Cases**: All programs in test_cases/
3. **Test Results**: results/validation.md
4. **Coverage Analysis**: results/coverage.md
5. **Traceability Matrix**: WASM ops → ARM instrs → tests
6. **Formal Proofs**: Coq development (../coq/)
7. **Official Reference**: Sail ARM specifications

**Claim**: "Validated against official ARM architecture specification with 99.99% confidence via comprehensive testing"

## Current Status

- [x] Extraction infrastructure created
- [x] Sail emulator building
- [ ] Test driver implementation
- [ ] Test suite creation
- [ ] Initial validation run
- [ ] Results analysis
- [ ] Bug fixes (if needed)
- [ ] Final validation report

## Timeline

- **Week 1**: Infrastructure setup (DONE)
- **Week 2**: Test driver + initial tests
- **Week 3**: Full test suite + validation run
- **Week 4**: Analysis + bug fixes + documentation

## References

- Sail ARM: https://github.com/rems-project/sail-arm
- WASM Spec: https://webassembly.github.io/spec/
- ISO 26262-8: Automotive safety standard
- CompCert Validation: Similar approach for C compiler
