# Synth Crate Structure

## Overview

Synth consists of **14 Rust crates** organized as a Cargo workspace. The crates form a clear compilation pipeline from WebAssembly Component Model input to ARM binary output.

## Crate Summary

| Crate | Lines | Purpose | Internal Deps |
|-------|-------|---------|---------------|
| synth-core | 821 | Fundamental types, IR, errors | - |
| synth-wit | 1,786 | WIT parsing and AST | - |
| synth-cfg | 839 | Control flow graph | - |
| synth-qemu | 276 | QEMU integration | - |
| synth-abi | 1,848 | Canonical ABI implementation | synth-wit |
| synth-frontend | 317 | WASM Component parsing | synth-core |
| synth-analysis | 511 | Whole-program analysis | synth-core |
| synth-opt | 3,037 | Optimization passes | synth-cfg |
| synth-regalloc | 555 | Register allocation | synth-cfg, synth-opt |
| synth-synthesis | 3,320 | Instruction selection | synth-core, synth-cfg, synth-opt |
| synth-codegen | 673 | ARM code generation | synth-cfg, synth-opt, synth-regalloc |
| synth-backend | 4,361 | Binary emission, ELF, startup | synth-core, synth-synthesis |
| synth-verify | 5,438 | Formal verification (Z3) | synth-core, synth-synthesis, synth-cfg, synth-opt |
| synth-cli | 249 | Command-line interface | synth-core, synth-frontend |

**Total: ~24,031 lines of Rust**

## Dependency Graph

```
                    ┌─────────────┐
                    │  synth-cli  │ (entry point)
                    └──────┬──────┘
                           │
              ┌────────────┴────────────┐
              ▼                         ▼
      ┌──────────────┐          ┌─────────────┐
      │synth-frontend│          │ synth-core  │◄──────────────┐
      └──────────────┘          └─────────────┘               │
                                       ▲                      │
                                       │                      │
       ┌───────────────────────────────┼──────────────────────┤
       │                               │                      │
       ▼                               │                      │
┌─────────────┐    ┌─────────────┐     │              ┌───────┴──────┐
│synth-analysis│   │synth-backend│─────┘              │ synth-verify │
└─────────────┘    └──────┬──────┘                    └───────┬──────┘
                          │                                   │
                          ▼                                   │
                  ┌───────────────┐                           │
                  │synth-synthesis│◄──────────────────────────┘
                  └───────┬───────┘
                          │
         ┌────────────────┼────────────────┐
         ▼                ▼                ▼
   ┌──────────┐    ┌───────────┐    ┌───────────┐
   │synth-cfg │◄───│ synth-opt │    │synth-core │
   └──────────┘    └─────┬─────┘    └───────────┘
         ▲               │
         │               ▼
         │        ┌────────────┐
         └────────│synth-regalloc│
                  └────────────┘
                         │
                         ▼
                  ┌────────────┐
                  │synth-codegen│
                  └────────────┘

   Independent:
   ┌──────────┐    ┌──────────┐    ┌──────────┐
   │synth-wit │───▶│synth-abi │    │synth-qemu│
   └──────────┘    └──────────┘    └──────────┘
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

### User Interface

#### synth-cli
**Purpose:** Command-line interface
- `synth parse` - parse and validate WASM
- `synth synthesize` - compile to native
- `synth target-info` - show target capabilities

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

The Synth crate structure is **well-designed** with clear separation of concerns:

- **Foundation:** synth-core, synth-wit, synth-cfg
- **Frontend:** synth-frontend, synth-abi, synth-analysis
- **Middle-end:** synth-opt, synth-synthesis
- **Back-end:** synth-regalloc, synth-codegen, synth-backend
- **Verification:** synth-verify
- **Tooling:** synth-cli, synth-qemu

**Priority:** Focus on wiring the pipeline together (synth-cli → all stages → binary) rather than restructuring crates.
