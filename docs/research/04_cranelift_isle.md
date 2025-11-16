# Cranelift Code Generator and ISLE Research

**Status:** Complete
**Last Updated:** 2025-11-16
**Focus:** Cranelift architecture, ISLE DSL, instruction selection, formal verification

---

## Executive Summary

Cranelift is a fast, secure code generator using the ISLE (Instruction Selection/Lowering Expressions) DSL for declarative instruction lowering. Key findings for WebAssembly synthesis:

- **ISLE enables formal verification** of instruction lowering rules (VeriISLE)
- **Fast compilation:** ~20-35% faster than LLVM
- **Reasonable performance:** ~86% of LLVM-optimized code
- **Production-proven:** Used in Wasmtime, Firefox
- **Modular backends:** AArch64, RISC-V, x86-64, s390x
- **E-graph optimization:** Solves phase-ordering problems

---

## 1. Cranelift Architecture

### Overview

- **Written in:** Rust (~200,000 lines of code)
- **Purpose:** Fast, secure compiler backend
- **Primary use case:** JIT compilation (but supports AOT)
- **Repository:** https://github.com/bytecodealliance/wasmtime/tree/main/cranelift

### Compilation Pipeline

```
Source (WebAssembly/etc.)
    ↓
CLIF (Cranelift IR)
    ↓
Mid-End Optimizations (E-graphs)
    ↓
Instruction Lowering (ISLE)
    ↓
VCode (Virtual-register Code)
    ↓
Register Allocation (regalloc2)
    ↓
Final VCode
    ↓
Machine Code Generation
    ↓
Native Code
```

### Intermediate Representations

#### CLIF (Cranelift IR Format)

**Characteristics:**
- High-level, architecture-independent
- Static Single Assignment (SSA) form
- Typed operations
- Text format: `.clif` file extension

**Design Choices:**
- Uses **block parameters** instead of phi-nodes for SSA
- Explicit control flow with basic blocks
- Strongly typed with integer (i8-i128), float (f32, f64), SIMD vector types

**Example CLIF:**
```clif
function u0:0(i32) -> i32 {
block0(v0: i32):
    v1 = iconst.i32 42
    v2 = iadd v0, v1
    return v2
}
```

**Benefits for Synthesis:**
- Simple, analyzable structure
- Easy to pattern-match for optimization
- Suitable for formal verification
- Clear semantics for translation validation

#### VCode (Virtual-Registerized Code)

**Characteristics:**
- Lower-level, target-specific
- Not in SSA form (values can be redefined)
- Uses virtual registers before allocation
- Strongly-typed instruction enums per backend

**Example Structure (AArch64):**
```rust
pub enum Inst {
    AluRRR {
        alu_op: ALUOp,
        size: OperandSize,
        rd: WritableReg,
        rn: Reg,
        rm: Reg,
    },
    // ... more instructions
}
```

**Benefits:**
- Type-safe instruction representation
- Efficient linear instruction arrays (not linked lists)
- Clear register constraints for allocation
- Straightforward emission to machine code

---

## 2. ISLE Domain-Specific Language

### What is ISLE?

ISLE (Instruction Selection and Lowering Expressions) is a **statically-typed, term-rewriting DSL** for expressing instruction lowering patterns declaratively.

**Key Innovation:** Designed from the ground up for formal verification (2021-2022)

**Repository:** https://github.com/bytecodealliance/wasmtime/tree/main/cranelift/isle

### Language Reference

**Official Documentation:**
https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/isle/docs/language-reference.md

### Core Language Concepts

#### Type System

**Two Primitive Categories:**
1. **Primitives:** Integers and symbolic constants from Rust
2. **Enums:** Correspond to Rust enum types with named variant fields

**Strong Typing:**
- A term can only rewrite to another term of identical type
- Type inference propagates unidirectionally through patterns
- Prevents many classes of bugs at compile time

#### Term-Rewriting Foundation

**Based on:**
- Nested tree structures of constructors and primitives
- S-expression syntax borrowed from Lisp
- Rules applied until terminating state (no further rules apply)
- **No full backtracking:** Once LHS matches, RHS is evaluated infallibly

### Syntax and Structure

#### Rule Format

```isle
(rule [PRIORITY] pattern expression)
```

#### Basic Examples

**Integer Addition on x86:**
```isle
;; Add two registers
(rule (lower (iadd x y))
  (value_reg (add (put_in_reg x) (RegMemImm.Reg (put_in_reg y)))))
```

**Load Sinking:**
```isle
;; Declare an external extractor
(decl inst_result (HighLevelInst) Value)
(extern extractor inst_result inst_result)

;; Rule to sink loads into adds
(rule (lower (HighLevelInst.Add a (inst_result (HighLevelInst.Load addr))))
  (LowLevelInst.Add (AddrMode.RegMem (put_in_reg a) (put_in_reg addr) 0)))
```

**Optimization Rewrite:**
```isle
;; Strength reduction: multiply by power-of-two → shift
(rule (simplify (imul x (power_of_two log2y)))
      (ishl x log2y))
```

### Pattern Matching Features

#### Left-Hand Sides (Patterns)

**Supported Constructs:**
- **Wildcards:** `_` matches any subterm
- **Variables:** `x` captures subterm value
- **Constants:** Decimal/hex/binary/octal integers; symbolic constants `$Symbol`
- **Constructors:** `(A pat1 pat2)` deconstructs nested structures
- **Conjunctions:** `(and PAT1 PAT2)` matches multiple patterns simultaneously
- **Bindings:** `x @ PAT` binds variable and matches sub-pattern

#### Right-Hand Sides (Expressions)

**Supported Constructs:**
- Constants and variable references
- Term constructors building new structures
- `let` bindings with lexical scoping
- Calls to external Rust functions

### Advanced Features

#### if-let Clauses

```isle
(rule LHS_PATTERN
  (if-let PAT2 EXPR2)
  (if-let PAT3 EXPR3)
  RHS)
```

**Purpose:** Conditional matching without pattern explosion

#### Pure Constructors

```isle
(extern constructor pure u32_fallible_add u32_fallible_add)
```

**Marked with `pure` keyword:**
- Return `Option<T>` for fallible operations
- Side-effect-free
- Enables match failure without state corruption

### Rule Prioritization

**Priority System:**
- Default priority: 0
- Range: -∞ to +∞
- Higher priority rules match first
- Automatic specificity heuristics applied before explicit priorities

**Use Case:**
Disambiguate overlapping patterns by giving more specific patterns higher priority.

### Compilation to Rust

**ISLE Compiler generates:**
- Efficient Rust code in a single pass over input
- Decision tree (trie structure) merging all rules
- Shared work across overlapping patterns
- Overlap detection and unreachable-rule identification
- Respects user-configured priorities

**Benefits:**
- No runtime overhead for pattern matching
- Compile-time verification of rule exhaustiveness
- Type-safe integration with Rust backend code

---

## 3. Instruction Selection Process

### Tree-Based Pattern Matching

**Process:**

1. Backend receives CLIF instructions in **postorder traversal**
2. For each instruction, ISLE-generated lowering function invoked
3. Operand "trees" examined by tracing value definitions upward in SSA form
4. Pattern matching continues until reaching block parameters or constants
5. Matched patterns generate corresponding VCode instructions

**Many-to-One Mappings:**
- **1-to-1:** One CLIF instruction → one VCode instruction
- **1-to-many:** Complex CLIF operations → multiple VCode instructions
- **Many-to-1:** Multiple CLIF operations → single optimized machine instruction

### Example: ARM64 Shift-Add Fusion

```isle
;; Combine shift and add into single instruction
(rule (lower (iadd x (ishl y (iconst k))))
      (madd x y (shift_amount k)))
```

**Result:**
Instead of:
```
LSL w1, w1, #3    ; shift
ADD w0, w0, w1    ; add
```

Single instruction:
```
ADD w0, w0, w1, LSL #3
```

### Decision Tree Generation

**Compilation Strategy:**
- ISLE compiler constructs a **trie (decision tree)** from all rules
- Nodes represent pattern matching decisions
- Edges represent partial matches
- Leaves contain right-hand-side expressions to evaluate
- Sharing maximized across overlapping patterns

**No Backtracking:**
- Once a pattern matches, its RHS is evaluated deterministically
- Failure only occurs if pattern doesn't match initially
- Guarantees predictable performance (no exponential blowup)

---

## 4. Backend Architecture

### Supported Targets (2024-2025)

1. **x86-64:** Full support with SIMD
2. **AArch64 / ARM64:** Full support with SIMD
3. **RISC-V 64:** RV64GC variant
4. **IBM s390x:** Full support with SIMD

### AArch64 Backend Implementation

**Location:** `/wasmtime/cranelift/codegen/src/isa/aarch64/`

#### ISLE Files

**inst.isle:**
- Instruction type definitions
- Emission helpers
- Instruction encoding

**lower.isle:**
- CLIF-to-VCode lowering rules
- Pattern matching for ARM-specific optimizations

#### Instruction Format Example

```isle
(type MInst (enum
  (Nop0)
  (Nop4)
  (AluRRR (alu_op ALUOp) (size OperandSize)
          (rd WritableReg) (rn Reg) (rm Reg))
  (AluRRImm12 (alu_op ALUOp) (size OperandSize)
              (rd WritableReg) (rn Reg) (imm12 Imm12))
  ...))
```

#### ALU Operations

```isle
(type ALUOp (enum
  (Add) (Sub) (Orr) (And) (Eor)
  (SDiv) (UDiv) (RotR) (Lsr) (Asr) (Lsl)
  ...))
```

#### Helper Function Pattern

```isle
(decl alu_rrr (ALUOp Type Reg Reg) Reg)
(rule (alu_rrr op ty src1 src2)
  (let ((dst WritableReg (temp_writable_reg $I64))
        (_ Unit (emit (MInst.AluRRR op (operand_size ty) dst src1 src2))))
    dst))
```

**Verification Status:**
- All integer operations formally verified with **Crocus** (ASPLOS 2024)
- Reproduced 3 known bugs including CVE rated 9.9/10 severity
- Identified 2 previously-unknown bugs

### RISC-V Backend Implementation

**Location:** `/wasmtime/cranelift/codegen/src/isa/riscv64/`

**Implementation Details:**
- Added in 2022 with ~21,000 lines of code
- Contributed by outside developer (testament to ISLE accessibility)
- Supports RV64GC (most common 64-bit variant)
- Uses LP64D ABI with 16-byte stack alignment

#### ISLE Files

- `inst.isle` - Base instruction definitions
- `inst_vector.isle` - Vector instruction support
- `lower.isle` - Lowering rules
- `abi.rs` - ABI implementation in Rust

#### Extension-Aware Code Generation

```isle
;; Conditional lowering based on ISA extensions
(rule (lower (sext_i8 x))
  (if (has_zbb)
    (sext_b x)           ;; Use Zbb extension instruction
    (sra (sll x 56) 56)  ;; Fallback to shift sequence
  ))
```

**Benefits for Embedded:**
- Targets specific RISC-V implementations
- Optimizes for available extensions
- Falls back gracefully when extensions unavailable

#### Immediate Loading Strategy

**Priority-based rules:**
1. Attempt single-instruction encoding (LUI, ADDI)
2. Fall back to constant pool loads for complex immediates
3. Optimizes for common cases

---

## 5. Optimization Techniques

### Acyclic E-Graphs (Aegraphs) - Mid-End Framework

**Purpose:** Solve phase-ordering problems in optimization

**E-Graph Basics:**
- Represent equivalence classes of expressions
- Record which values are equivalent without choosing representations
- Enable combining optimizations from multiple passes

**Cranelift's Innovation: Acyclic Variant**
- Restrict union operations to node creation time
- Levelized structure (nodes created in topological order)
- Union-find for partial canonicalization
- Cascades-style rule application from database query optimization

**Performance Results:**
- ~16% runtime speedups on real WebAssembly workloads
- Comparable compilation times to previous mid-end
- Enabled by default since 2023

**Academic Paper:**
"Acyclic E-graphs for Efficient Optimization in a Production Compiler" (PLDI 2023)

### Control Flow Integration

**Side-Effect Skeleton:**
- Original CFG maintained for non-pure instructions
- Pure operators "float" in e-graph above CFG
- Hybrid representation enables aggressive reordering

**Node Types:**
- **Param nodes:** Block parameters (CFG roots)
- **Pure nodes:** Side-effect-free, location-independent
- **Inst nodes:** Side-effecting, never deduplicated
- **Result nodes:** Projections extracting specific results

### Scoped Elaboration Algorithm

**Converts e-graph back to linear CFG code:**

Process:
1. Dominator-tree traversal
2. Generate node values as low as possible in dominator tree
3. Prevents partially-dead code
4. Maximally reuses already-computed values
5. Uses scoped hashmap mirroring SSA domination invariant

**Subsumes Multiple Passes:**
- Global Value Numbering (GVN)
- Loop-Invariant Code Motion (LICM)
- Rematerialization
- Avoids expensive fixpoint iterations

### ISLE-Based Rewrites

**Machine-Independent Optimizations:**

```isle
;; Strength reduction
(rule (simplify (imul x (power_of_two log2y)))
      (ishl x log2y))

;; Algebraic simplification
(rule (simplify (iadd x 0)) x)

;; Constant folding
(rule (simplify (iadd (iconst a) (iconst b)))
      (iconst (add_const a b)))
```

**Benefits:**
- Declarative specification enables formal verification
- Tool-based rule discovery (e.g., Ruler) becomes feasible
- Single rule-application engine for all rewrites
- Fine-grained interleaving replaces manual pass sequencing

### Backend-Specific Optimizations

**Instruction Fusion Examples:**

```isle
;; ARM64: Fused multiply-add
(rule (lower (fadd (fmul x y) z))
      (fmadd x y z))

;; x86: Load-op fusion
(rule (lower (iadd x (load addr)))
      (add_mem x addr))
```

**Peephole Optimizations:**
- Redundant move elimination
- Dead code elimination during lowering
- Address mode folding

### Register Allocation (regalloc2)

**Features:**
- Backtracking algorithm with range splitting
- Live range splitting to minimize spills
- Move coalescing to eliminate redundant copies
- SSA deconstruction integrated with allocation

**Performance Impact:**
- 10-20% compilation time improvement vs previous allocator
- Up to 7% runtime performance improvement
- Fewer compile-time outliers

**Repository:** https://github.com/bytecodealliance/regalloc2

---

## 6. Formal Verification of Cranelift

### Multi-Layered Verification Strategy

1. **Fuzzing and Differential Testing**
2. **Symbolic Verification**
3. **Formal Verification of ISLE Rules**
4. **Static Analysis**

### VeriISLE: Formal Verification of Instruction Selection

**Overview:**
VeriISLE (CMU 2023) verifies ISLE lowering rules using SMT solvers.

**Approach:**
- Translates ISLE rules to SMT formulas
- Verifies full functional equivalence between CLIF and machine code semantics
- Modular annotation language for term semantics
- Automatic verification without requiring full rewrite

**Results:**
- Reproduced 3 known bugs (including CVE rated 9.9/10)
- Identified 2 previously-unknown bugs
- Discovered underspecified compiler invariant
- Successfully verified integer operations in AArch64 backend

**Key Innovation: Modularity**
Annotations added alongside ISLE definitions:

```isle
;; Semantic annotation
(spec (iadd x y) (bvadd x y))

;; Verification happens automatically
(rule (lower (iadd x y))
  (alu_rrr Add $I64 x y))
```

**Paper:** http://reports-archive.adm.cs.cmu.edu/anon/2023/CMU-CS-23-126.pdf

### Crocus: Lightweight WebAssembly Verification

**Publication:** ASPLOS 2024

**Authors:** Alexa VanHattum, Monica Pardeshi, Chris Fallin, Adrian Sampson, Fraser Brown

**Focus:** Verifying WebAssembly-to-native instruction selection in Cranelift

**Coverage:**
- WebAssembly 1.0 integer operations
- ARM AArch64 backend
- Proves correctness of instruction lowering rules

**Bug Detection:**
- Reproduced 3 known bugs including 9.9/10 CVE
- Found 2 new bugs
- Analyzed root causes to improve compiler design

**Lightweight Approach:**
- Modular verification (rule-by-rule)
- Doesn't require verifying entire compiler
- Practical for production compilers

**Repository:** https://github.com/avanhatt/asplos24-ae-crocus
**Paper:** https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf

### Fuzzing Infrastructure

**Differential Execution Fuzzers:**

Three separate fuzz targets comparing execution results:

1. **Cranelift vs. V8** - Compare against V8's TurboFan compiler
2. **Cranelift vs. Wasm Spec Interpreter** - Against reference implementation
3. **Cranelift vs. CLIF Interpreter** - Machine-independent IR interpreter

**wasm-mutate: Semantic-Preserving Fuzzer**
- Generates semantically-equivalent Wasm module variations
- Enables better fuzzing coverage
- Any difference in execution indicates bug

**Continuous Fuzzing:**
- Member of Google's OSS-Fuzz initiative
- 24/7 fuzzing infrastructure
- Automatically detects and reports bugs

### Register Allocator Verification

**Symbolic Verification:**
- Fuzz target generates arbitrary input programs
- Checker symbolically verifies register allocation correctness
- Validates allocation constraints satisfied
- Ensures no illegal register usage

**Properties Verified:**
- All virtual registers mapped to physical registers or stack slots
- Register constraints satisfied (fixed registers, tied operands, etc.)
- SSA deconstruction correct
- Spill/reload correctness

---

## 7. Performance Characteristics

### Compilation Speed

**Benchmarks:**
- ~20-35% faster than LLVM (2024 research)
- Originally showed order-of-magnitude improvements
- Explicit design goal: optimize for JIT compilation speed

**Scale:**
- 10 optimization pass sets (vs. LLVM's 96, GCC's 372)
- Function-level parallelism through independent per-function compilation

### Runtime Performance

**Benchmarks:**
- Generated code runs ~14% slower than LLVM-optimized code
- ~2% slower than V8's TurboFan compiler

**Trade-off:**
Faster compilation for slightly slower execution - ideal for JIT scenarios and development workflows

### Use in Production

**Wasmtime (Bytecode Alliance):**
- Primary WebAssembly runtime
- Production use at Fastly, Shopify, others

**Firefox:**
- Originally developed for Firefox's WebAssembly JIT
- Later shifted to other runtimes

**Wasmer:**
- Alternative WebAssembly runtime
- Supports Cranelift backend

---

## 8. Integration with WebAssembly

### Compilation Pipeline

```
WebAssembly Binary
    ↓
Validation
    ↓
Translation to CLIF
    ↓
Mid-End Optimization (E-graphs)
    ↓
ISLE Lowering
    ↓
Register Allocation
    ↓
Machine Code Generation
    ↓
Executable Code
```

**Located in:** `cranelift/wasm/src/code_translator.rs`

### WebAssembly-Specific Features

**Memory Access:**
- Wasm linear memory model
- Explicit bounds checking
- Guard pages for efficient trap handling
- Spectre mitigations on bounds checks

**Control Flow Translation:**
- Wasm structured control flow → CFG
- Block/loop/if → basic blocks
- br_table → indexed jump with bounds check

**Function Calls:**
- Direct calls to other Wasm functions
- Indirect calls through tables (with type checking)
- Host function imports
- Calling convention: `fast` (specialized for Wasm)

### Sandboxing and Security

**Bounds Checking:**

```isle
;; Memory load with bounds check
(rule (lower (load.i32 addr))
  (if-let checked (bounds_check addr heap_size)
    (load_checked checked)
    (trap OutOfBounds)))
```

**Spectre Mitigations:**
- Speculative execution barriers on bounds checks
- Added in 2022 for heap, table, and branch table accesses
- Vendor-recommended barrier instructions (LFENCE on x86)

**Control-Flow Integrity:**
- AArch64 hardware CFI features supported
- Return address signing (PAC)
- Branch target identification (BTI)

---

## 9. Synthesis Implications

### For WebAssembly-to-Native Synthesis:

#### 1. ISLE as Synthesis Rule Language

**Benefits:**
- Declarative specification
- Formal verification support (VeriISLE)
- Modular rule development
- Type-safe synthesis rules

**Use in Synth:**
- Define target-specific synthesis rules
- Verify correctness with SMT solvers
- Build library of proven-correct transformations

#### 2. E-Graph Optimization

**Benefits:**
- Solves phase-ordering problems
- Explores all equivalent programs
- Provably optimal extraction

**Use in Synth:**
- Apply to component-level optimization
- Combine with equality saturation (egg library)
- Generate optimal code without manual pass ordering

#### 3. Multi-Target Support

**Benefits:**
- Proven backends for ARM, RISC-V, x86
- Modular architecture
- Clear separation of concerns

**Use in Synth:**
- Leverage existing backends as templates
- Add embedded-specific optimizations
- Reuse verification infrastructure

#### 4. Formal Verification Integration

**Benefits:**
- VeriISLE demonstrates practical formal verification
- Modular verification approach
- Found real bugs in production compiler

**Use in Synth:**
- Adopt VeriISLE methodology
- Verify synthesis rules for safety-critical use
- Build certification evidence

---

## 10. Recommendations for Synth Project

### Phase 1: Foundation
- Study Cranelift codebase (especially AArch64 and RISC-V backends)
- Understand ISLE language and compiler
- Experiment with VeriISLE for verification

### Phase 2: Extension
- Add embedded-specific ISLE rules (Cortex-M, embedded RISC-V)
- Implement XIP support in VCode generation
- Add hardware-assisted bounds checking rules

### Phase 3: Optimization
- Integrate e-graph optimization for component composition
- Implement cross-component inlining
- Add target-specific peephole optimizations

### Phase 4: Verification
- Adopt VeriISLE for synthesis rule verification
- Integrate with proof-carrying code approach
- Build certification artifacts

### Phase 5: Production
- Optimize compilation speed for embedded workflows
- Implement profiling and benchmarking
- Create embedded-specific runtime integration

---

## 11. Key Resources

### Documentation
- Cranelift Main Site: https://cranelift.dev/
- ISLE Language Reference: https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/isle/docs/language-reference.md
- Cranelift IR Documentation: https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md

### Academic Papers
- **Crocus (ASPLOS 2024):** https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf
- **VeriISLE (CMU 2023):** http://reports-archive.adm.cs.cmu.edu/anon/2023/CMU-CS-23-126.pdf
- **Aegraphs (PLDI 2023):** Acyclic E-graphs for Efficient Optimization

### Blog Posts
- Chris Fallin's Blog: https://cfallin.org/blog/
- Benjamin Bouvier: "A primer on code generation in Cranelift" (2021)
- Bytecode Alliance Progress Reports (2021, 2022)

### Source Code
- Wasmtime Repository: https://github.com/bytecodealliance/wasmtime
- AArch64 Backend: `/wasmtime/cranelift/codegen/src/isa/aarch64/`
- RISC-V Backend: `/wasmtime/cranelift/codegen/src/isa/riscv64/`
- ISLE Compiler: `/wasmtime/cranelift/isle/`
- E-graph Framework: `/wasmtime/cranelift/codegen/src/egraph/`

---

**Document Status:** Complete
**Next Steps:** Integrate ISLE methodology into synthesis architecture
