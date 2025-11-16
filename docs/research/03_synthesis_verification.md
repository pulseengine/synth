# Synthesis Approaches and Compiler Verification for WebAssembly-to-Native

## Executive Summary

This document presents comprehensive research on synthesis approaches and compiler verification frameworks applicable to proving correctness of WebAssembly-to-native synthesis. The research covers hardware synthesis analogies, compiler verification frameworks, synthesis tools, proof techniques, and specific methodologies for verified compilation.

---

## 1. Hardware Synthesis Analogies

### 1.1 High-Level Synthesis (HLS): C/C++ to RTL

**Definition and Process:**
High-level synthesis (HLS) is "an automated design process that takes an abstract behavioral specification of a digital system and finds a register-transfer level structure that realizes the given behavior." It converts high-abstraction-level descriptions into register-transfer level (RTL) for ASIC and FPGA implementation.

**Input Languages:**
- ANSI C/C++
- SystemC
- MATLAB

**Key Tools:**
- Xilinx Vitis HLS (formerly Vivado HLS)
- Intel HLS Compiler
- Siemens Catapult HLS
- Open-source: Vericert (formally verified)

**Verification Methodology:**

**Sequential Logic Equivalence Checking (SLEC):** Tools formally verify correctness of hand-written RTL versus high-level models in C++ or SystemC, proving equivalence even with differences in language, timing, and interfaces. This is crucial because HLS transformations are advanced and equivalence verification may require formal expertise.

**Vericert - Verified HLS in Coq:**
Vericert is the first mechanically verified HLS tool that preserves the behavior of input software. It extends CompCert with:
- A new hardware-oriented intermediate language
- A Verilog back end
- Proof of correctness in Coq
- Support for all int operations, non-recursive function calls, local arrays/pointers, and control-flow structures

Published at OOPSLA 2021, Vericert demonstrates that formally verified HLS is achievable using proof assistants.

### 1.2 FPGA Synthesis and Equivalence Checking

**Traditional HDLs:**
Logic design uses hardware description languages (HDLs) like Verilog and VHDL. Traditional FPGA development requires expertise in these HDLs.

**Equivalence Checking:**
Equivalence checking uses mathematical modeling techniques to prove that two representations of a design exhibit the same behavior. Two types exist:

1. **Combinatorial Equivalence Checking:** Shows that a design after logic synthesis is the same as the input RTL description by comparing combinatorial logic between corresponding registers.

2. **Sequential Equivalence Checking (SLEC):** Can compare designs with fundamentally different timing, enabling un-timed or partially timed models to be compared against RTL models. This is necessary for mass adoption of high-level synthesis.

**Application:** In complex SoC designs, equivalence checking validates operations from logic synthesis, power optimization, testability insertion, and functional ECOs. Since it's based on vectorless formal proof, it catches errors that simulation might miss.

### 1.3 Synthesis vs. Compilation: Critical Differences

**Program Synthesis:**
- Constructs a program that provably satisfies a given high-level formal specification
- Specifications are usually non-algorithmic statements in logical calculus
- Describes *what* you want, not *how* to achieve it
- Rewriting rules should be *complete* - able to transform specifications into every equivalent program

**Compilation:**
- Transforms existing source code into executable programs through well-defined phases
- Analysis phase reads source, divides into parts, checks errors
- Synthesis phase (back-end) generates target program from intermediate representation
- Rules are deterministic and algorithmic

**Key Distinction:** "Deductive synthesis looks like a regular compiler which transforms input programs through rewriting rules, but the difference is that the synthesizer's rewriting rules should be complete—they should be able to transform the specification into every equivalent program."

**Convergence:** Recent superoptimization tools blur this distinction, being particularly effective at finding small sequences of unusual optimized code.

### 1.4 Hardware Synthesis Lessons for Software

**Equivalence Proofs:**
Hardware synthesis has decades of experience with formal equivalence checking between abstraction levels. These techniques apply to software:
- Formal methods for verifying transformation correctness
- Vectorless proof approaches that don't require exhaustive testing
- Handling timing and sequencing differences between representations
- Managing state space explosion through abstraction

**Structured Verification:**
Hardware verification uses hierarchical approaches that verify components independently then compose them. This maps well to compiler verification with modular passes.

---

## 2. Compiler Verification Frameworks

### 2.1 CompCert: Verified C Compiler

**Overview:**
CompCert is "the first realistic formally verified compiler providing a machine-checked mathematical proof that the code it generates matches the source code." It compiles nearly all of ISO C 2011 to ARM, PowerPC, RISC-V, and x86.

**Verification Approach:**

**Semantic Preservation:** CompCert verifies that every compilation pass preserves semantics. Formal semantics are given for every source, intermediate, and target language, from C to assembly.

**Simulation Diagrams:** The core proof technique uses simulation diagrams relating transitions in the source language to transitions in the target language. Four kinds of simulation diagrams imply semantic preservation:

1. **Forward Simulation:** Given a program P1 and transformed program P2, each transition step in P1 with trace t must correspond to transitions in P2 with the same trace t, preserving an invariant relation ≈ between states.

2. **Backward Simulation:** Every behavior of compiled code is also a behavior of source code. Hard to build when one source step implements as several compiled steps.

3. **Lockstep Simulation:** One-to-one correspondence between steps
4. **Multi-step Simulation:** One source step maps to multiple target steps

**Memory Model:**
CompCert uses a sophisticated memory model shared between semantics of C and intermediate languages. The memory model supports transformations called extensions and injections that preserve properties of memory operations. This is crucial for proving semantics preservation across optimization passes.

**Trust Base:**
- Machine-checked proofs in Coq (versions 8.20+)
- Formalized memory model and semantics
- Verified floating-point arithmetic
- Verified parser and type-checker

**Recent Updates (2024-2025):**
- Version 3.16 (September 2025): Added position-independent code/executable support
- Version 3.15 (December 2024): Improved value analysis precision and constant propagation

**Commercial Adoption:**
CompCert earned the 2021 ACM Software System Award for "lasting influence" on research and industrial practice, with commercial support from AbsInt.

### 2.2 CakeML: Verified ML Compiler

**Overview:**
CakeML is a functional programming language with a proven-correct compiler that can bootstrap itself. It includes an ecosystem of proofs and tools.

**Compiler Backend:**
The verified CakeML compiler backend includes mechanized proofs of correctness for all compilation phases from high-level functional programs to machine code.

**Recent Developments (2024-2025):**
- March 2024: Papers accepted by AAAI, ESOP, CAV, and IJCAR on end-to-end verification
- January 2024: "CakeML: A verified implementation of ML" received Most Influential POPL Paper Award at POPL 2024
- PureCake: Verified compiler for Haskell-like language within CakeML ecosystem

**Key Innovation:**
CakeML demonstrates that entire language ecosystems can be verified, including compilers, runtime systems, and proof infrastructure.

### 2.3 Verified LLVM Components

**Alive2: Bounded Translation Validation**

Alive2 is a formal verification framework for LLVM optimizations that performs automatic verification through SMT solvers.

**Technical Approach:**
- Consists of libraries and tools for analysis and verification of LLVM code and transformations
- Designed to avoid false alarms, fully automatic through Z3 SMT solver
- Requires no changes to LLVM

**Bounded Verification Strategy:**
Alive2 uses bounded translation validation to bound resources:
- Unrolls loops up to a given bound
- Limits execution time and memory consumption
- Errs on the side of soundness (zero false-alarm rate goal)

**Bug Discoveries:**
- 47 new bugs discovered by running over LLVM's unit test suite
- 28 bugs fixed
- 8 patches to LLVM Language Reference (definitive IR semantics description)
- 95 total bugs reported, with 25 related to undef semantics

**Alive (Predecessor):**
Alive is a domain-specific language for writing optimizations that can automatically prove them correct or generate counterexamples. Used to translate 300+ LLVM optimizations and found 8 incorrect ones.

**AliveInLean:**
A verified LLVM peephole optimization verifier combining formal verification with automation in the Lean theorem prover.

### 2.4 Translation Validation Frameworks

**Definition:**
Translation validation checks whether a specific compilation is correct by inspecting source (input) and target (output) programs. Instead of verifying the optimization is valid for all inputs upfront, it verifies at compile time that the optimization behaved correctly for the particular input given.

**SMT-Based Approach:**
- Encodes return values from both source and target programs
- Employs SMT solvers (Z3) to compare encodings
- Flags any discrepancies
- Fits well with fast-moving industrial compilers

**Applications:**

**Machine Learning Compilers:** SMT-based translation validation framework for Multi-Level IR (MLIR) used by deep learning compilers.

**Microsoft UTC Compiler (utcTV):** Translation validation for Microsoft's C++ compiler has identified several bugs not found by other methods.

**Challenges:**
- Making SMT solvers prove verification conditions in reasonable time
- Language constructs that prevent reasonable solving time: floating points, wide integer divisions, complex memory operations

**Key Advantage:**
Translation validation works per-compilation rather than requiring verification of the entire compiler algorithm, making it practical for rapidly evolving compilers.

### 2.5 Proof-Carrying Code (PCC)

**Concept:**
Proof-carrying code is a software mechanism allowing a host system to verify properties about an application via a formal proof accompanying the executable code. Originally described in 1996 by George Necula and Peter Lee.

**Typed Assembly Language (TAL):**
In 1999, Greg Morrisett, David Walker, and others reformulated PCC as "Typed Assembly Language" - a strongly typed assembly language based on generic RISC instruction sets, with a type system supporting:
- Tuples
- Polymorphism
- Existential packages
- Function pointers

**Foundational Proof-Carrying Code (FPCC):**
Princeton FPCC project focused on proving correctness of PCC-checkers using:
- Standard ML as source language
- SPARC machine language as target
- Twelf as proof language

**Relation to Verified Compilers:**
Verified compilers like CompCert guarantee that safety properties proved on source code hold for executable compiled code, essentially providing proof-carrying guarantees through compiler verification.

---

## 3. Synthesis Tools and Optimizers

### 3.1 Equality Saturation and E-graphs

**Core Concept:**
Equality saturation constructs an e-graph that represents a large set of programs equivalent to an input program, then extracts the "best" program by repeatedly applying pattern-based rewrites.

**E-graphs:**
An e-graph efficiently represents a congruence relation over many expressions. Originally developed in the late 1970s for automated theorem provers, they've been repurposed for compiler optimizations and program synthesizers.

### 3.2 egg: Fast and Extensible Equality Saturation

**Overview:**
egg is a fast and flexible e-graph library implemented in Rust. It's used to build program optimizers, synthesizers, and verifiers.

**Key Innovations:**

1. **Rebuilding:** A new amortized invariant restoration technique providing asymptotic speedups over current techniques.

2. **E-class Analyses:** A general mechanism integrating domain-specific analyses into the e-graph, reducing need for ad hoc manipulation.

**Performance:**
In verification benchmarks, egg performed verification 15× faster than Z3 (or 47× faster with batched evaluation).

**Recognition:**
Won Distinguished Paper Award at POPL 2021.

**Verification Use Case:**
An equality saturation engine verifies equalities by adding left and right sides to an e-graph, running axioms as rewrites, and checking if both sides end up in the same e-class.

### 3.3 Herbie: Floating-Point Accuracy Optimizer

**Purpose:**
Herbie automatically improves the error of floating-point expressions.

**E-graph Application:**
Herbie simplifies expressions by creating an equivalence graph and applying rewrite rules at all nodes. From the final equivalence graph, Herbie chooses the program represented by the smallest tree.

**Correctness Strategy:**
Rather than proving transformations correct in advance, Herbie:
- Generates candidate optimizations through rewriting
- Validates each transformation by testing against original expression using concrete numerical inputs
- Uses statistical analysis of error metrics for confidence

**Results:**
Often reduces floating-point error by 40-60% within practical time constraints.

**Recognition:**
Won Distinguished Paper Award at PLDI 2015.

### 3.4 SMT-Based Synthesis: Rosette and Sketch

**Rosette:**

Rosette is a solver-aided programming language that extends Racket with language constructs for program synthesis, verification, and more.

**Key Features:**
- Compiles code to logical constraints solved with off-the-shelf SMT solvers (Z3 by default)
- Combines virtualized access to solvers with Racket's metaprogramming
- Makes it easy to develop synthesis and verification tools for new languages

**Approach:** Write an interpreter for your language in Rosette, and you get synthesis and verification tools for free!

**Sketch:**

Sketch offers a Java-ish language equipped with synthesis features. The synthesis query uses the solver to search for a correct program in a space of candidate implementations defined by a syntactic sketch.

**Sketch Filling:**
A sketch is a program with holes, which the solver fills with expressions from a specified set of options. Unlike full synthesis, sketch filling is first-order logic (not second-order), enabling SAT/SMT solvers.

**Applications:**
Three case studies using Rosette for web scraping, spatial programming, and superoptimization of bitvector programs demonstrate versatility.

### 3.5 Superoptimizers

**Definition:**
Superoptimization is the process where a compiler automatically finds the optimal sequence for loop-free instruction sequences, rather than just improving code partially.

**STOKE: Stochastic Superoptimizer**

**Approach:**
- Formulates loop-free binary superoptimization as stochastic search
- Uses Markov Chain Monte Carlo (MCMC) sampler
- Randomly adds, removes, modifies, or reorders instructions
- Encodes transformation correctness and performance improvement in cost function

**Verification Strategy:**
Two-stage approach:
1. Runtime testing during optimization to rapidly evaluate candidates (tolerates incorrect intermediate solutions)
2. Symbolic verification at completion to guarantee equivalence

**Correctness:** Restricts to loop-free instruction sequences, making symbolic verification "much easier."

**Souper: Synthesizing Superoptimizer**

**Approach:**
- Synthesis-based superoptimizer for LLVM IR subset
- Uses SMT-based approach
- Verifies that every replacement on each program is correct
- Ensures superoptimized programs are semantically equivalent

### 3.6 Equality Saturation for Superoptimization

**Modern Approach:**
Equality saturation splits optimization into two phases:
1. **Exploration:** Uses e-graphs to compactly generate and store all rewritings of input program
2. **Extraction:** Selects optimal program from e-graph

**Advantages:**
- Applies all possible substitutions at once
- Avoids sensitivity to substitution order
- Explores larger fragment of exponential space of equivalent graphs

**Tools:**
- **Hydra:** Generalizes peephole optimizations with program synthesis. Generalized optimizations are formally verified and automatically convertible to C++ code for LLVM passes.
- **Tensat:** Synthesizes optimized graphs up to 23% faster in runtime while reducing optimization time by up to 300×.

**Automatic Generation:**
Superoptimization can automatically generate general-purpose peephole optimizers, potentially learning millions of optimizations (vs. hundreds in current peephole optimizers).

---

## 4. Proof Techniques

### 4.1 Bisimulation and Equivalence Proofs

**Definition:**
Two systems are bisimulation equivalent whenever they can perform the same sequences of actions to reach bisimulation equivalent states.

**Strong vs. Weak Bisimulation:**
- **Strong:** All labels of transitions are considered visible
- **Weak:** Ignores some actions, considered internal and invisible

**Application to Correctness:**
If the same formalism models both specification and implementation, theories based on equivalences can prove that a concrete description is correct with respect to an abstract one. If a certain behavior equivalence exists between specification and implementation, the software is considered correct.

**Compiler Correctness:**
Weak bisimulation on labelled transition systems gives an elegant framework to prove contextual equivalence of original and transformed programs. Gordon and Howe represent a program's behavior by a labelled transition system whose bisimilarity relation is a congruence that coincides with contextual equivalence.

### 4.2 Refinement Types

**Definition:**
Refinement types extend type systems by allowing types to be refined with logical predicates. For example, `{x: int | x > 0}` represents positive integers.

**Advantages:**
- Logic of specifications restricted to decidable fragments
- Verification and inference completely automatic
- No "proof terms" required as in full dependent types
- Significant automation

**Limitations:**
- Cannot use arbitrary functions in specifications (unlike dependent types)
- Restricts class of properties that can be written

**Tools:**
- **LiquidHaskell:** Refinement type system for Haskell
- Applications to secure implementations and compiler correctness

### 4.3 Dependent Types for Correctness

**Capabilities:**
Dependent types can express more properties than refinement types, allowing arbitrary functions in specifications.

**Challenges:**
- Reconciling non-terminating expressions with decidable type checking is unclear
- Soundness requires careful restriction of terms in types
- Less automation than refinement types, requiring explicit proof terms

**Trade-off:**
Dependent types provide greater expressiveness at the cost of requiring more manual proof work compared to refinement types.

### 4.4 SMT Solving for Verification

**Role in Compiler Verification:**
SMT solvers are automatic theorem provers for first-order logic with theories (integers, bit vectors, floating points, etc.).

**Applications:**
1. **Translation Validation:** Encode source and target program semantics, use SMT to prove equivalence
2. **Optimization Verification:** Verify specific optimization instances are correct
3. **Peephole Verification:** Prove individual rewrite rules correct

**Tools and Solvers:**
- **Z3:** Microsoft Research SMT solver (most common)
- **CVC5:** Alternative SMT solver
- Used by Alive2, Rosette, Souper, VeriISLE

**Challenges:**
- Certain constructs prevent reasonable solving time:
  - Floating points
  - Wide integer divisions
  - Complex memory operations
- Making proofs complete in reasonable time requires careful encoding

### 4.5 Property-Based Testing (QuickCheck-style)

**Concept:**
Property-based testing writes assertions about logical properties that functions should fulfill, then generates many random test cases to falsify assertions.

**How It Works:**
1. Define properties functions should satisfy
2. QuickCheck generates random test cases
3. If a falsifying case is found, QuickCheck reduces it to minimal failing subset (shrinking)

**Compiler Testing Applications:**
- Compiler testing using sentence generators
- Increases test coverage significantly
- Complements formal verification

**Implementations:**
Available in numerous languages: Haskell (original), Rust, Julia, C++, Java, Erlang.

**Relation to Verification:**
While not formal proof, property-based testing provides high confidence and catches edge cases that might be missed in manual test writing or even formal verification attempts.

---

## 5. WebAssembly-Specific Verification

### 5.1 WebAssembly Formal Verification

**Mechanized Isabelle Specification:**

A mechanized Isabelle specification for WebAssembly includes:
- Verified executable interpreter
- Type checker
- Fully mechanized proof of type system soundness

**Type Soundness Properties:**
1. **Preservation:** Given a configuration with type t* in i, if it steps to a new configuration, types are preserved
2. **Progress:** If a configuration has type t*, then either it is a Trap (exception) or it can take another step

**Impact:** This work exposed several issues with the official WebAssembly specification.

**Iris-Wasm:**

Iris-Wasm is a mechanized higher-order separation logic building on:
- Wasm 1.0 specification mechanized in Coq
- Iris framework

**Capabilities:**
- Formal verification of functional correctness of WebAssembly programs
- Verification even when programs invoke and are invoked by unknown code
- Higher-order reasoning about program behavior

**wasm-verify:**

A proof-of-concept tool for formally verifying WebAssembly functions, based on "Specification and verification of WebAssembly programs" master's thesis.

**Current Capabilities:**
- Partial correctness results
- Total correctness (requiring termination proofs) is unsupported

### 5.2 WebAssembly Memory Model

**Linear Memory:**
A contiguous, mutable array of raw bytes that can be created with initial size but grown dynamically.

**Bounds Checking:**
Accesses to linear memory are bounds-checked at the region level, potentially resulting in a trap at runtime. A trap occurs if an access is not within current memory bounds.

**Security Guarantees:**
- The specification guarantees no program can break WebAssembly's memory model
- Memory regions are isolated from runtime internal memory
- Set to zero by default unless otherwise initialized

**Limitations:**
- Bounds checking performed at linear memory region granularity (not context-sensitive)
- Data in linear memory can overwrite adjacent objects
- WebAssembly modules are not safe from memory vulnerabilities within their own linear memory (buffer overflow, use-after-free)

**Research Extensions:**
- **Progressive Memory Safety:** Proposes new safe memory segment accessed exclusively through handles (strongly-typed objects encapsulating bounds-checked, memory-safe pointers)
- **Cage:** Utilizes memory tagging to replace software-based bounds checks while preserving external memory safety

### 5.3 WebAssembly Instruction Selection Verification

**Cranelift and ISLE:**

ISLE (Instruction Selection/Lowering Expressions) is a domain-specific language for Cranelift that:
- Expresses instruction-lowering patterns for four target architectures
- Supports machine-independent optimizing rewrites
- Designed with verification in mind

**Term-Rewriting Approach:**
- Declarative rules express equivalences between IR operations and machine instructions
- External extractors and constructors (Rust functions) destructure inputs and build outputs
- Strong type system facilitates correctness checking
- Overlap checker identifies when multiple rules match same input

**VeriISLE: ISLE Verifier**

VeriISLE verifies rules written in Cranelift's ISLE DSL using SMT solvers to automatically verify full functional equivalence.

**Results:**
- First formal verification effort for instruction-lowering phase of efficiency-focused production compiler
- Verified natural subset of rules necessary to compile integer computations in WebAssembly 1.0
- Out of 14 Wasmtime CVEs, VeriISLE reproduced known CVEs and identified 3 new faults (2 patched)

**Design Benefits:**
- Allows developers to gradually annotate new rules
- Quick updates to annotations as rules evolve
- Essential for evolving production compiler

**Arrival:**

Another instruction-selection verifier for Cranelift with features:
1. Automatically reasons about chains of instruction-selection rules
2. Introduces lightweight, efficient method for reasoning about stateful rules
3. Automatically derives high-assurance machine code specifications

### 5.4 WebAssembly JIT vs. AOT Compilation

**AOT (Ahead-of-Time) Benefits:**
- Dramatically simplifies runtime design and overhead compared to JIT
- Brings significant security benefits: all code is known a-priori, making exploits harder to hide
- Eliminates JIT bugs (most productive source of CVEs in production browsers)

**JIT Security Risks:**
- Compiles Wasm code into machine code at runtime
- Dynamic nature complicates detecting and preventing attacks
- Attackers can inject malicious code into compilation process

**Verification Implications:**
- WebAssembly's ISA designed to be fast to compile (suitable for AOT or JIT)
- AOT compilation recommended for enhanced security in security-critical environments
- Supports only structured control flow, amenable to security verification techniques including symbolic execution

---

## 6. Verified Instruction Scheduling and Register Allocation

### 6.1 Translation Validation Approach

**Register Allocation Validation:**
Translation validation algorithms for register allocation based on backward dataflow inference of equations between variables, registers, and stack locations can handle:
- Sophisticated forms of spilling
- Live range splitting

**Soundness:** The soundness of such algorithms has been mechanically proved using the Coq proof assistant.

**CompCert Initially:**
Initially did not support fully verified instruction scheduling, instead relying on translation validation which validates each compilation case.

### 6.2 Fully Verified Instruction Scheduling

Recent work achieved the first mechanized library for fully verified instruction scheduling while keeping proof workload acceptably lightweight.

**Certified and Efficient Scheduling:**
Published work on "Certified and efficient instruction scheduling: application to interlocked VLIW processors" demonstrates fully verified scheduling with mechanized proofs.

### 6.3 Combinatorial Optimization Approach

A combinatorial optimization approach to register allocation and instruction scheduling:
- Has potential to solve these problems optimally
- Captures complete set of transformations used in state-of-the-art compilers
- Scales to medium-sized functions up to 1,000 instructions

**Unison:**
Open-source combinatorial approach integrated with LLVM.

---

## 7. Peephole Optimization Verification

### 7.1 Alive and Verified Peephole Rules

**Alive:**
A domain-specific language for writing LLVM optimizations that can automatically:
- Prove them correct
- Generate counterexamples if incorrect
- Translate to C++ code for LLVM optimization passes

**Results:**
Translated 300+ LLVM optimizations and found 8 incorrect ones.

### 7.2 Verifying Peephole Rewriting in SSA

**AliveInLean:**
Recent work combines convenience of automation with versatility of interactive theorem provers for verifying peephole rewrites across domain-specific IRs.

**Approach:**
- Formalizes core calculus for SSA-based IRs
- Generic over the IR and covers regions
- Provides scaffolding for defining and verifying peephole rewrites
- Offers tactics to eliminate abstraction overhead

**Verification:**
Peephole rules proven correct with Z3 before being compiled into actual code. When proof fails, a (hopefully minimal) counterexample is printed.

### 7.3 Challenges

Peephole optimizations are:
- Individually difficult to get right, particularly with undefined behavior
- A persistent source of bugs when taken together
- Very easy to write incorrectly for all corner cases

---

## 8. Recent Developments and Tools (2023-2025)

### 8.1 Certified Compilation Advances

**CPP 2025 (Certified Programs and Proofs):**
Scheduled for January 20-21, 2025, with topics including:
- Certified or certifying programming, compilation, linking
- OS kernels, runtime systems, security monitors
- Hardware verification
- Proof assistants (ACL2, Agda, Coq, Dafny, F*, HOL4, HOL Light, Idris, Isabelle, Lean, Mizar)

**Coq Renamed to Rocq:**
Rocq (former Coq) allows expression of mathematical assertions, mechanically checks proofs, helps find formal proofs, and extracts certified programs from constructive proofs.

### 8.2 CertiCoq: Verified Coq Compiler

CertiCoq is a compiler for Gallina (Coq's specification language) targeting Clight (compilable with CompCert).

**Goal:** Build end-to-end verified compiler bridging gap between formally verified source programs and compiled executables.

**Key Publications:**
- "Compositional Optimizations for CertiCoq" (ICFP 2021)
- "Deriving Efficient Program Transformations from Rewrite Rules" (ICFP 2021)

**Verified Extraction:**
Recent work at PLDI 2024: "Verified Extraction from Coq to OCaml" implements extraction based on MetaCoq's certified erasure, including:
- Full pipeline with standard transformations (eta-expansion, inlining)
- Proof-generating manner
- Verified optimization pass removing unused arguments

### 8.3 MLIR and Multi-Level Verification

**MLIR (Multi-Level IR):**
Compiler IR with similarities to traditional three-address SSA but introduces polyhedral loop optimization concepts as first-class.

**Transform Dialect:**
Allows declarative specification for controlling compiler transformations via the transform dialect. Enables requesting transformations using compiler IR itself.

**Verification Support:**
- Operation semantics described abstractly using Traits and Interfaces
- Traits describe verification constraints on valid IR
- Complex invariants captured and checked
- Dialect Conversion framework for verified transformations

**Recent Research:**
"First-Class Verification Dialects for MLIR" introduces collection of semantics-supporting MLIR dialects for encoding compiler IR semantics, supporting separation of concerns between three domains of expertise.

### 8.4 Machine Learning Compiler Verification

SMT-based translation validation for MLIR frameworks used by deep learning compilers represents growing importance of verification in ML compilation.

---

## 9. Synthesis from Specifications

### 9.1 Program Synthesis Overview

Program synthesis is the task of automatically discovering executable code given user intent expressed through:
- Input-output examples
- Demonstrations
- Natural language
- Formal specifications

### 9.2 Counterexample-Guided Inductive Synthesis (CEGIS)

**Approach:**
CEGIS enables solving second-order exists-forall queries (like program synthesis) with off-the-shelf SMT solvers by decomposing into multiple first-order existentially quantified queries.

**Process:**
1. Generate candidate program
2. Check if it satisfies specification
3. If not, generate counterexample
4. Refine candidate to handle counterexample
5. Repeat until correct program found

**Advantage:**
Encoding verification and synthesis of entire program as single SMT query becomes possible.

### 9.3 Synthesis vs. Verification

**Synthesis:**
- Constructs programs rather than verifying given ones
- Progress must be explicitly encoded by inferring ranking functions to prevent generating non-terminating programs

**Verification:**
- Only partial correctness typically assumed
- Uses formal proof techniques

**Commonality:**
Both use formal proof techniques and comprise approaches of different degrees of automation.

---

## 10. Application to WebAssembly-to-Native Synthesis

### 10.1 Key Insights for WebAssembly Synthesis

**Structured Control Flow:**
WebAssembly's structured control flow makes it amenable to:
- Security verification techniques including symbolic execution
- Formal verification of transformations
- Proof of equivalence between WebAssembly and native code

**Type Soundness:**
Mechanized proof of WebAssembly type soundness provides foundation for verified compilation:
- Preservation and progress properties proven
- Type system guarantees safety properties
- These guarantees must be preserved through native code generation

### 10.2 Proof Strategy for Synthesis Correctness

Based on research findings, a WebAssembly-to-native synthesis tool should employ:

**1. Layered Verification Architecture:**

**Level 1: Specification Mechanization**
- Mechanize WebAssembly semantics in proof assistant (Coq, Isabelle, Lean)
- Mechanize target architecture semantics
- Prove type soundness and safety properties

**Level 2: Synthesis Rules**
- Express synthesis rules in declarative DSL (similar to ISLE)
- Make rules amenable to SMT verification
- Each rule proven correct with respect to semantics

**Level 3: Optimization Passes**
- Use equality saturation (e-graphs) for optimization exploration
- Verify optimizations preserve semantics using:
  - Translation validation (per-compilation checking)
  - SMT-based equivalence checking
  - Bisimulation proofs for behavioral equivalence

**Level 4: Memory Model**
- Formalize WebAssembly linear memory model
- Formalize target memory model
- Prove transformations preserve memory safety properties
- Bounds checking guarantees maintained in native code

**2. Simulation-Based Proof:**

Following CompCert's approach:

**Forward Simulation:**
- Each WebAssembly execution step corresponds to one or more native code steps
- Trace equivalence preserved
- Invariant relation between WebAssembly state and native state

**Backward Simulation:**
- Every behavior of native code is also a behavior of WebAssembly code
- Useful for optimizations that may reorder or combine operations

**Memory Injection:**
- Prove memory transformations preserve safety
- Bounds checking in WebAssembly translates to correct bounds checking in native code

**3. SMT-Based Translation Validation:**

For each compilation instance:
- Encode WebAssembly semantics as SMT formulas
- Encode generated native code semantics as SMT formulas
- Use Z3 or similar solver to prove equivalence
- Generate counterexamples if equivalence fails

**4. Equality Saturation for Optimization:**

Using egg-style approach:
- Build e-graph of equivalent programs
- Apply rewrite rules (all proven correct)
- Extract optimal program from e-graph
- Verify extraction preserves semantics

### 10.3 Specific Techniques for WebAssembly Guarantees

**Maintaining Memory Safety:**
1. Prove bounds checking correct in native code
2. Use CompCert-style memory model with injections
3. Verify linear memory abstraction preserved
4. Prove no out-of-bounds accesses possible

**Maintaining Type Safety:**
1. Preserve WebAssembly type invariants through compilation
2. Use typed intermediate representations
3. Prove type preservation (refinement of preservation lemma)
4. Consider typed assembly language approach for native code

**Maintaining Control Flow Integrity:**
1. WebAssembly's structured control flow simplifies verification
2. Prove control flow graph of native code respects WebAssembly structure
3. No arbitrary jumps that violate WebAssembly semantics
4. Use weak bisimulation to handle timing differences

### 10.4 Recommended Tool Stack

Based on research findings:

**Proof Assistant:** Coq or Lean 4
- Coq: Most mature, used by CompCert, CakeML, Vericert
- Lean 4: Modern, good automation, used by AliveInLean

**SMT Solver:** Z3
- Most widely used
- Best tool support (Rosette, Alive2, VeriISLE)
- Good performance on bit-vector reasoning

**E-graph Library:** egg (if using Rust) or egglog
- High performance
- Well-tested
- Active community

**Intermediate Representations:**
- Follow MLIR multi-level approach
- WebAssembly → High-level IR → Mid-level IR → Low-level IR → Native
- Each transformation verified independently
- Compose proofs for end-to-end guarantee

### 10.5 Verification Workflow

**Phase 1: Mechanize Semantics**
1. Formalize WebAssembly operational semantics
2. Formalize target ISA semantics
3. Prove basic properties (type soundness, memory safety)

**Phase 2: Implement and Verify Synthesis Rules**
1. Design synthesis rules in declarative DSL
2. Prove each rule correct using SMT (VeriISLE-style)
3. Build library of verified rules

**Phase 3: Implement Optimization Passes**
1. Use equality saturation for optimization exploration
2. Verify each optimization preserves semantics
3. Prove composition of optimizations correct

**Phase 4: End-to-End Proof**
1. Prove simulation between WebAssembly and final native code
2. Prove memory model transformations correct
3. Prove all safety properties preserved
4. Extract verified compiler from proof

**Phase 5: Testing and Validation**
1. Property-based testing (QuickCheck-style) for confidence
2. Differential testing against other WebAssembly compilers
3. Translation validation on real programs
4. Fuzzing to find corner cases

### 10.6 Case Studies to Emulate

**CompCert:**
- Simulation diagram approach
- Memory model with injections
- Modular pass verification
- Machine-checked proofs

**Vericert:**
- C-to-Verilog (analogous to WebAssembly-to-native)
- Extends CompCert methodology
- Proves HLS correct
- Shows feasibility of cross-abstraction verification

**VeriISLE:**
- Instruction selection verification
- SMT-based approach
- Practical for production compiler
- Found real bugs in Wasmtime

**Alive2:**
- Translation validation per-compilation
- Bounded verification
- Zero false-alarm goal
- Found many LLVM bugs

---

## 11. Challenges and Open Problems

### 11.1 Scalability Challenges

**SMT Solver Performance:**
- Complex programs can create formulas too large for SMT solvers
- Floating-point operations particularly challenging
- May need timeouts and bounded verification

**Proof Complexity:**
- End-to-end proofs for realistic compilers are large (CompCert: ~100,000 lines of Coq)
- Maintenance burden as compiler evolves
- Requires deep expertise in theorem proving

### 11.2 Completeness vs. Automation Trade-offs

**Refinement Types:**
- More automation, less expressiveness
- May not capture all desired properties

**Dependent Types:**
- More expressiveness, less automation
- Requires more manual proof effort

**SMT-Based Approaches:**
- Automatic but bounded
- May time out on complex queries

### 11.3 WebAssembly-Specific Challenges

**Memory Model:**
- Linear memory model different from native memory
- Bounds checking semantics must be preserved
- Pointer arithmetic semantics differ

**Numeric Semantics:**
- WebAssembly has precise numeric semantics
- Must preserve exact behavior in native code
- Floating-point operations particularly tricky

**Extensions:**
- New WebAssembly proposals (SIMD, threads, GC) add complexity
- Proofs must be updated for new features

### 11.4 Performance vs. Verification Trade-offs

**Verified Compilers Often Slower:**
- CompCert produces slower code than GCC/Clang in some cases
- Verification limits aggressive optimizations
- Trade-off between correctness guarantees and performance

**Synthesis May Enable Better Optimizations:**
- Exploring larger space of equivalent programs
- Finding optimizations humans miss
- But: verification of synthesis more complex

---

## 12. Conclusions and Recommendations

### 12.1 Synthesis vs. Compilation for WebAssembly

**Compilation Approach (Traditional):**
- Well-understood
- Existing verification frameworks (CompCert)
- Deterministic, predictable

**Synthesis Approach (Novel):**
- Explore larger space of implementations
- Potentially find better optimizations
- More complex to verify

**Recommendation:**
Use hybrid approach:
- Core translation verified as traditional compiler (CompCert-style)
- Optimization passes use synthesis techniques (equality saturation)
- Each synthesis step verified (translation validation)
- Best of both worlds: correctness guarantees + optimization power

### 12.2 Recommended Verification Strategy

**Short-term (Prototype):**
1. Implement translation validation using SMT (Alive2-style)
2. Use property-based testing for confidence
3. Focus on core WebAssembly features

**Medium-term (Production):**
1. Mechanize WebAssembly semantics in Coq/Lean
2. Implement synthesis rules with SMT verification (VeriISLE-style)
3. Verify critical optimization passes
4. Use equality saturation with verified rewrites

**Long-term (Full Verification):**
1. Complete end-to-end mechanized proof
2. All passes proven correct in proof assistant
3. Memory model fully formalized and proven
4. Extract verified synthesizer from proof

### 12.3 Key Techniques to Apply

**Must Have:**
1. SMT-based translation validation for each compilation
2. Mechanized WebAssembly semantics
3. Simulation proofs (forward or backward)
4. Memory model with correctness proofs

**Should Have:**
1. Equality saturation for optimization
2. Declarative synthesis rules (ISLE-style DSL)
3. Per-rule SMT verification
4. Property-based testing

**Nice to Have:**
1. Full extraction in proof assistant
2. Refinement types for intermediate representations
3. Proof-carrying code generation
4. Certified optimizations library

### 12.4 Expected Benefits

**Correctness Guarantees:**
- Mathematical proof of semantic preservation
- No compiler-introduced bugs
- Safe for security-critical applications

**Optimization Opportunities:**
- Synthesis explores larger space than traditional compilation
- Equality saturation finds non-obvious optimizations
- Formally verified means can use aggressive optimizations safely

**Maintenance Benefits:**
- Declarative rules easier to understand and modify
- SMT verification catches bugs early
- Type system prevents entire classes of errors

### 12.5 Research Gaps to Address

**Synthesis-Specific Verification:**
- Limited work on verifying synthesis for low-level code generation
- Most synthesis work focuses on high-level programs
- Need techniques for verifying synthesis of machine code

**WebAssembly Memory Model:**
- Linear memory semantics differ from traditional memory models
- Verification of memory transformations needs attention
- Bounds checking preservation underexplored

**Performance of Verified Synthesis:**
- Unknown if verified synthesis can match hand-optimized code
- Need case studies and benchmarks
- Performance vs. verification trade-offs not well understood

---

## 13. References and Resources

### Key Papers

**Compiler Verification:**
- Xavier Leroy. "Formal verification of a realistic compiler." Communications of the ACM, 2009.
- Kumar et al. "CakeML: A Verified Implementation of ML." POPL 2014.
- Tan et al. "The verified CakeML compiler backend." Journal of Functional Programming, 2019.

**Translation Validation:**
- Lopes et al. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021.
- Samet et al. "SMT-Based Translation Validation for Machine Learning Compiler." CAV 2022.

**Equality Saturation:**
- Willsey et al. "egg: Fast and Extensible Equality Saturation." POPL 2021.
- Panchekha et al. "Automatically Improving Accuracy for Floating Point Expressions." PLDI 2015.

**Superoptimization:**
- Schkufza et al. "Stochastic Superoptimization." ASPLOS 2013.
- Sasnauskas et al. "Souper: A Synthesizing Superoptimizer." arXiv 2017.

**WebAssembly Verification:**
- Watt. "Mechanising and Verifying the WebAssembly Specification." CPP 2018.
- Vassena et al. "Iris-Wasm: Robust and Modular Verification of WebAssembly Programs." PACMPL 2023.

**Instruction Selection Verification:**
- Pardeshi et al. "VeriISLE: Verifying Instruction Selection in Cranelift." CMU Tech Report 2023.
- Ho et al. "Scaling Instruction-Selection Verification." preprint 2024.

**High-Level Synthesis:**
- Herklotz et al. "Formal Verification of High-Level Synthesis." OOPSLA 2021.

**Program Synthesis:**
- Torlak and Bodik. "Growing Solver-Aided Languages with Rosette." Onward! 2013.
- Solar-Lezama. "Program Synthesis by Sketching." PhD Thesis, 2008.

### Tools and Frameworks

**Proof Assistants:**
- Coq/Rocq: https://coq.inria.fr/
- Lean 4: https://lean-lang.org/
- Isabelle: https://isabelle.in.tum.de/

**Verified Compilers:**
- CompCert: https://compcert.org/
- CakeML: https://cakeml.org/
- CertiCoq: https://certicoq.org/
- Vericert: https://vericert.ymhg.org/

**SMT Solvers:**
- Z3: https://github.com/Z3Prover/z3
- CVC5: https://cvc5.github.io/

**E-graph Libraries:**
- egg: https://github.com/egraphs-good/egg
- egglog: https://github.com/egraphs-good/egglog

**Synthesis Tools:**
- Rosette: https://github.com/emina/rosette
- Herbie: https://herbie.uwplse.org/

**Verification Tools:**
- Alive2: https://github.com/AliveToolkit/alive2
- VeriISLE: http://reports-archive.adm.cs.cmu.edu/anon/2023/CMU-CS-23-126.pdf

**WebAssembly Tools:**
- Cranelift: https://cranelift.dev/
- Wasmtime: https://github.com/bytecodealliance/wasmtime

### Community Resources

- EGRAPHS Workshop: Annual workshop at PLDI
- CPP Conference: Certified Programs and Proofs
- Coq Workshop: Annual gathering of Coq users
- PLDI, POPL, OOPSLA: Major PL conferences with verification work

---

## Appendix A: Glossary

**AOT (Ahead-of-Time) Compilation:** Compiling code before execution rather than during runtime.

**Bisimulation:** Relation between two systems showing they can perform same sequences of actions to reach equivalent states.

**E-graph:** Data structure efficiently representing congruence relation over many expressions.

**Equality Saturation:** Technique using e-graphs to apply all rewrite rules simultaneously, then extract optimal program.

**Forward Simulation:** Proof technique showing each source step corresponds to target steps with preserved semantics.

**ISLE (Instruction Selection/Lowering Expressions):** DSL for expressing instruction selection rules in Cranelift.

**JIT (Just-in-Time) Compilation:** Compiling code during execution.

**Linear Memory:** WebAssembly's memory model: contiguous, mutable array of bytes.

**Mechanized Proof:** Proof checked by machine (proof assistant) rather than human.

**Peephole Optimization:** Optimization examining small window of instructions for improvement opportunities.

**Refinement:** Relation showing one system is more defined/constrained than another while preserving properties.

**RTL (Register Transfer Level):** Hardware design abstraction describing data flow between registers.

**Semantic Preservation:** Property that compiled code has same behavior as source code.

**Simulation Diagram:** Visual representation of simulation relation between source and target programs.

**SMT (Satisfiability Modulo Theories):** Solver for logical formulas with theories (integers, bit-vectors, etc.).

**Superoptimization:** Finding optimal sequence of instructions for given code.

**Synthesis:** Automatically generating program from specification.

**Translation Validation:** Verifying specific compilation instance correct (vs. verifying compiler always correct).

**Weak Bisimulation:** Bisimulation ignoring internal/invisible actions.

---

## Appendix B: Comparison Matrix

| Framework | Language | Technique | Automation | Expressiveness | Maturity |
|-----------|----------|-----------|------------|----------------|----------|
| CompCert | C | Forward/Backward Simulation | Manual Proof | High | Production |
| CakeML | ML | Simulation | Manual Proof | High | Production |
| Alive2 | LLVM IR | SMT Translation Validation | Automatic | Medium | Production |
| VeriISLE | ISLE/Cranelift | SMT Per-Rule | Automatic | Medium | Research |
| egg | Generic | Equality Saturation | Automatic | Medium | Production |
| Rosette | Generic | SMT Synthesis | Semi-Automatic | High | Production |
| Vericert | C→Verilog | CompCert Extension | Manual Proof | High | Research |
| STOKE | x86-64 | Stochastic + SMT | Automatic | Low | Research |

---

*Research compiled: 2025-11-16*
*Focus: WebAssembly-to-Native Synthesis Verification*
