# Synth Crate Structure

## Overview

Synth consists of **18 Rust crates** organized as a Cargo workspace. The crates form a clear compilation pipeline from WebAssembly input to ARM binary output, with a multi-backend architecture and formal verification.

**Last Updated:** 2026-02-09

## Crate Summary

| Crate | Purpose | Internal Deps |
|-------|---------|---------------|
| synth-core | Fundamental types, IR, Backend trait, BackendRegistry | - |
| synth-wit | WIT parsing and AST | - |
| synth-cfg | Control flow graph | - |
| synth-qemu | QEMU integration | - |
| synth-memory | Linear memory management | synth-core |
| synth-abi | Canonical ABI implementation | synth-wit |
| synth-frontend | WASM Component parsing | synth-core |
| synth-analysis | Whole-program analysis | synth-core |
| synth-opt | Optimization passes | synth-cfg |
| synth-regalloc | Register allocation | synth-cfg, synth-opt |
| synth-synthesis | Instruction selection + synthesis rules | synth-core, synth-cfg, synth-opt |
| synth-codegen | ARM code generation | synth-cfg, synth-opt, synth-regalloc |
| synth-backend | ARM backend, ELF builder, Cortex-M startup | synth-core, synth-synthesis |
| synth-backend-awsm | aWsm external backend (stub) | synth-core |
| synth-backend-wasker | wasker external backend (stub) | synth-core |
| synth-verify | Z3 SMT formal verification | synth-core, synth-synthesis, synth-cfg, synth-opt |
| synth-test | WAST test infrastructure (parser, Renode runner) | synth-core |
| synth-cli | Command-line interface | synth-core, synth-frontend, synth-backend, synth-synthesis |

**Total: ~45,000 lines of Rust**

## Dependency Graph

```
                        ┌─────────────┐
                        │  synth-cli  │ (entry point)
                        └──────┬──────┘
                               │
            ┌──────────────────┼──────────────────┐
            ▼                  ▼                   ▼
    ┌──────────────┐   ┌─────────────┐    ┌───────────────┐
    │synth-frontend│   │synth-backend│    │synth-synthesis│
    └──────┬───────┘   └──────┬──────┘    └───────┬───────┘
           │                  │                    │
           ▼                  ▼                    ▼
      ┌─────────┐    ┌──────────────┐      ┌───────────┐
      │synth-core◄───┤  ARM encoder │      │synth-cfg  │
      └────┬────┘    │  ELF builder │      └───────────┘
           │         │  Cortex-M    │             ▲
           │         └──────────────┘             │
           │                                ┌─────┴─────┐
           │                                │ synth-opt │
           │                                └───────────┘
           ▼
    ┌──────────────┐     ┌──────────────────┐
    │Backend trait │────▶│ BackendRegistry   │
    │BackendCaps   │     └────────┬─────────┘
    └──────────────┘              │
           ▲          ┌───────────┼───────────┐
           │          ▼           ▼           ▼
           │   synth-backend  backend-awsm  backend-wasker
           │   (ARM, active)  (stub)        (stub)
           │
    ┌──────┴───────┐
    │ synth-verify │  Z3 SMT verification
    └──────────────┘

    Test infrastructure:
    ┌──────────┐    ┌──────────────┐
    │synth-test│───▶│ WAST parser  │
    └──────────┘    │ Robot gen    │
                    │ Renode runner│
                    └──────────────┘

    Independent:
    ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌────────────┐
    │synth-wit │───▶│synth-abi │    │synth-qemu│    │synth-memory│
    └──────────┘    └──────────┘    └──────────┘    └────────────┘
```

## Compilation Pipeline

```
┌─────────────────────────────────────────────────────────────────────┐
│                        COMPILATION PIPELINE                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  .wasm/.wat ──▶ synth-frontend ──▶ Component (synth-core types)     │
│                                                                      │
│  Component ──▶ synth-analysis ──▶ call graphs, memory layout        │
│                                                                      │
│  Component ──▶ synth-opt ──▶ optimized IR                           │
│                     │                                                │
│                     ├── DeadCodeElimination                          │
│                     ├── ConstantFolding                              │
│                     ├── CommonSubexpressionElimination               │
│                     ├── StrengthReduction                            │
│                     └── LoopInvariantCodeMotion                      │
│                                                                      │
│  Optimized IR ──▶ synth-synthesis ──▶ ARM instruction patterns      │
│                     │                                                │
│                     ├── PatternMatcher                               │
│                     ├── InstructionSelector                          │
│                     └── PeepholeOptimizer                            │
│                                                                      │
│  ARM patterns ──▶ synth-regalloc ──▶ physical register allocation   │
│                     │                                                │
│                     └── Graph coloring (R0-R12)                      │
│                                                                      │
│  Allocated IR ──▶ synth-codegen ──▶ ARM Thumb-2 assembly            │
│                                                                      │
│  Assembly ──▶ synth-backend ──▶ ELF binary                          │
│                     │                                                │
│                     ├── ArmEncoder (machine code)                    │
│                     ├── ElfBuilder (binary format)                   │
│                     ├── VectorTable (interrupts)                     │
│                     ├── ResetHandler (startup)                       │
│                     ├── LinkerScript (memory layout)                 │
│                     └── MPUAllocator (memory protection)             │
│                                                                      │
│  (Optional) ──▶ synth-verify ──▶ Z3 SMT verification                │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## Crate Details

### Foundation Crates (No Dependencies)

#### synth-core
**Purpose:** Fundamental types used throughout the compiler
- Component model representations
- Intermediate Representation (IR) types
- Target architecture specifications
- Error types

#### synth-wit
**Purpose:** WebAssembly Interface Types (WIT) parsing
- Lexer and tokenizer
- Parser producing WIT AST
- Interface definitions for Component Model

#### synth-cfg
**Purpose:** Control Flow Graph construction and analysis
- `BasicBlock`, `Cfg`, `CfgBuilder`
- Loop detection
- Dominators, branch simplification, block merging

#### synth-qemu
**Purpose:** QEMU integration for testing
- ARM emulation helpers
- Test execution on QEMU

### Frontend & Analysis

#### synth-frontend
**Purpose:** Parse WASM Component Model binaries
- `ComponentParser` - binary parsing
- `ComponentValidator` - structural validation
- Converts raw WASM to `synth-core::Component`

#### synth-abi
**Purpose:** Canonical ABI implementation
- Value lifting/lowering
- Memory management
- String encoding (UTF-8, UTF-16, Latin-1)
- Type size/alignment calculations

#### synth-analysis
**Purpose:** Whole-program analysis
- Call graph construction
- Memory layout analysis
- SSA form (Static Single Assignment)

### Optimization & Synthesis

#### synth-opt
**Purpose:** Machine-independent optimization passes
- `OptimizationPass` trait
- `PassManager` with fixed-point iteration
- Passes: DCE, constant folding, CSE, strength reduction, LICM, copy propagation

#### synth-synthesis
**Purpose:** Target-specific instruction selection
- `InstructionSelector` - IR to ARM mapping
- `PatternMatcher` - pattern-based selection
- `RuleDatabase` - synthesis rules
- `PeepholeOptimizer` - local optimizations

### Code Generation

#### synth-regalloc
**Purpose:** Register allocation
- `PhysicalReg` enum (R0-R15)
- `LiveInterval` analysis
- `InterferenceGraph` construction
- Graph coloring algorithm

#### synth-codegen
**Purpose:** ARM Thumb-2 code generation
- `ArmInstruction` enum
- `CodeGenerator` - produces assembly strings
- Data processing, memory, control flow instructions

#### synth-backend
**Purpose:** Binary emission and embedded setup
- `ArmEncoder` - assembly to machine code
- `ElfBuilder` - ELF file generation
- `VectorTable` - interrupt vectors
- `ResetHandlerGenerator` - startup code
- `LinkerScriptGenerator` - memory layout
- `MPUAllocator` - memory protection

### Verification

#### synth-verify
**Purpose:** Formal verification with Z3 SMT solver
- Translation validation
- Semantic equivalence proofs
- Property-based testing

### Multi-Backend Support

#### synth-backend-awsm
**Purpose:** aWsm external backend (stub)
- Implements `Backend` trait from synth-core
- Would invoke external `awsm` compiler to produce ELF
- Currently returns "not implemented"

#### synth-backend-wasker
**Purpose:** wasker external backend (stub)
- Implements `Backend` trait from synth-core
- Would invoke external `wasker` to produce ELF
- Currently returns "not implemented"

### Memory Management

#### synth-memory
**Purpose:** Linear memory management for WASM
- Memory region allocation
- R11-based linear memory addressing for ARM
- Stack layout management (stack at top of SRAM, linear memory at base)

### Test Infrastructure

#### synth-test
**Purpose:** WAST test infrastructure
- `WastParser` - parse WAST files into test cases (assert_return, assert_trap)
- `RobotGenerator` - generate Robot Framework .robot files from parsed tests
- `NativeRunner` - direct Renode telnet control (bypassing Robot Framework)
- `TelnetController` - Renode telnet interface for machine control
- `synth-test generate` - CLI for WAST → Robot file generation
- `synth-test run` - CLI for direct test execution via Renode

### User Interface

#### synth-cli
**Purpose:** Command-line interface
- `synth compile` - compile WAT/WASM to ARM ELF
- `synth verify` - standalone Z3 translation validation
- `synth disasm` - disassemble generated ELF
- `synth backends` - list available backends
- `synth parse` - parse and analyze WASM

## Key Questions Answered

### Q: What's the difference between synth-synthesis and synth-opt?

| Aspect | synth-opt | synth-synthesis |
|--------|-----------|-----------------|
| **Purpose** | Machine-independent optimization | Machine-specific instruction selection |
| **Input** | Abstract IR | Optimized IR |
| **Output** | Optimized IR (same format) | ARM instruction patterns |
| **Approach** | Pass-based transformation | Pattern matching with rules |
| **Target-aware** | No | Yes (ARM-specific) |

**Summary:** `synth-opt` improves code quality generically; `synth-synthesis` converts to target-specific instructions.

### Q: What's the difference between synth-codegen and synth-backend?

| Aspect | synth-codegen | synth-backend |
|--------|---------------|---------------|
| **Purpose** | Assembly generation | Binary file creation |
| **Input** | IR + register allocation | Assembly code |
| **Output** | ARM assembly strings | ELF binaries, scripts |
| **Scope** | Per-function | Whole program + runtime |

**Summary:** `synth-codegen` produces assembly; `synth-backend` produces deployable binaries.

### Q: Is there overlap or duplication?

**No significant overlap.** Each crate has a distinct role in the pipeline:
1. synth-opt → synth-synthesis → synth-regalloc → synth-codegen → synth-backend

The separation is clean and follows standard compiler architecture.

## Refactoring Recommendations

### Current State: Well-Structured

The crate structure is already well-organized with clear responsibilities. No major refactoring is required.

### Minor Improvements (Optional)

1. **synth-codegen + synth-regalloc consolidation**
   - Both are tightly coupled in the code generation phase
   - Could be merged into a single `synth-arm-codegen` crate
   - **Recommendation:** Keep separate for now (clear responsibilities)

2. **synth-analysis integration**
   - Currently has stub implementations
   - Should be integrated into the main pipeline when needed
   - **Recommendation:** Defer until pipeline is wired

3. **synth-qemu integration**
   - Standalone testing utility
   - Consider moving to a `tests/` or `tools/` directory
   - **Recommendation:** Keep as-is for modularity

### Not Recommended

- **Do NOT merge synth-synthesis and synth-opt** - They serve fundamentally different purposes
- **Do NOT split synth-backend further** - It's already well-modularized internally

## Conclusion

The Synth workspace is organized into **18 crates** with clear separation:

- **Foundation:** synth-core (Backend trait, IR, types), synth-wit, synth-cfg
- **Frontend:** synth-frontend, synth-abi, synth-analysis
- **Middle-end:** synth-opt (passes), synth-synthesis (rules + instruction selection)
- **Back-end:** synth-regalloc, synth-codegen, synth-backend (ARM + ELF + Cortex-M)
- **External backends:** synth-backend-awsm, synth-backend-wasker (stubs)
- **Memory:** synth-memory
- **Verification:** synth-verify (Z3 SMT)
- **Testing:** synth-test (WAST parser, Robot generator, Renode runner)
- **Tooling:** synth-cli, synth-qemu

The pipeline is fully wired: `synth compile input.wat -o output.elf --cortex-m` works end-to-end.
