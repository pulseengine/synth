# Formal Verification and Qualification of WebAssembly for Safety-Critical Systems

## Comprehensive Research Report

**Research Focus:** WebAssembly formal verification, safety certification, and qualification for automotive (ISO 26262) and medical device (IEC 62304) applications

**Date:** 2025-11-16

---

## Executive Summary

This research investigates the state of formal verification, certification pathways, and qualification strategies for WebAssembly (Wasm) in safety-critical systems. While WebAssembly offers strong memory safety and type safety guarantees with a formally specified semantics, its deployment in certified safety-critical systems (automotive ISO 26262, medical IEC 62304, avionics DO-178C) remains largely in the research and proof-of-concept phase rather than production deployment.

**Key Findings:**

1. **Formal Verification:** Multiple mechanized specifications of WebAssembly exist in Isabelle, Coq, and K Framework with machine-checked proofs of type soundness and memory safety
2. **Certification Gap:** No publicly documented production deployments or specific qualification guidance exists for WebAssembly under ISO 26262, IEC 62304, or DO-178C
3. **Verified Compilation:** Several verified compiler projects exist (CertiCoq-Wasm, self-certifying frameworks) but CompCert does not yet target WebAssembly
4. **Safety Guarantees:** WebAssembly provides strong sandboxing, type safety, memory safety at the module level, and control-flow integrity, but vulnerabilities in source code (C/C++) are inherited
5. **Runtime Verification:** Projects like VeriWasm, Wasmtime, and WAMR incorporate formal verification techniques including proof-carrying code and translation validation

---

## 1. Safety Standards Context

### 1.1 ISO 26262 (Automotive Functional Safety)

**Overview:**
- ISO 26262 is the international standard for functional safety of electrical/electronic systems in road vehicles
- Published by ISO in 2011, revised in 2018
- Uses Automotive Safety Integrity Levels (ASIL) ranging from A (lowest) to D (highest)
- ASIL D requires failure rate of 10^-9 per hour (one failure in 114,155 years)

**Formal Verification Requirements:**
- ASIL C and D: Highly recommend semi-formal notation and semi-formal verification methods
- ASIL D: Recommends formal methods for software design
- Tool Confidence Level (TCL) system ranges from 1-3, with compilers typically requiring TCL3 qualification

**WebAssembly Status:**
- **No specific guidance or documented implementations found**
- General formal verification approaches for ISO 26262 are well-established for traditional systems
- WebAssembly would need to address:
  - Compiler tool qualification (ISO 26262-8)
  - Runtime verification
  - Deterministic execution requirements
  - Integration with AUTOSAR platforms

### 1.2 IEC 62304 (Medical Device Software)

**Overview:**
- IEC 62304 defines life cycle requirements for medical device software
- Software classified into three safety classes:
  - Class A: No injury possible
  - Class B: Non-serious injury possible
  - Class C: Death or serious injury possible
- Not a formal certification standard but compliance required for product approval
- Requires comprehensive software lifecycle, risk management, traceability, and documentation

**WebAssembly Status:**
- **No specific guidance or documented implementations found**
- Would need to demonstrate:
  - Software safety classification
  - Hazard analysis
  - Risk management integration
  - Verification and validation processes
  - Configuration management
  - Problem resolution processes

### 1.3 DO-178C (Avionics Software Certification)

**Overview:**
- DO-178C: "Software Considerations in Airborne Systems and Equipment Certification"
- Primary standard for FAA, EASA, and Transport Canada certification
- DO-330 provides guidance for software tool qualification
- Covers complete software lifecycle with rigorous process requirements

**WebAssembly Status:**
- **No specific implementations or qualification data found**
- Tool qualification under DO-330 would be critical for any WebAssembly compiler/runtime
- Would require:
  - Tool Operational Requirements (TOR)
  - Tool Qualification Plan
  - Tool verification cases
  - Tool qualification data

---

## 2. Formal Verification of WebAssembly

### 2.1 WebAssembly Specification and Formal Semantics

**W3C Standardization:**
- WebAssembly 1.0 standardized by W3C in 2019
- Uniquely specified with full pen-and-paper formal semantics
- Four required artifacts for standardization:
  1. Formal specification with declarative typing and reduction rules (LaTeX)
  2. Prose pseudocode with algorithmic semantics (reStructuredText)
  3. Reference interpreter (OCaml)
  4. Test suite

**Key Properties:**
- Mostly deterministic formal semantics
- Rules out undefined behavior
- Type-safe by design
- Linear-time validation algorithm
- Decidable type checking

**GitHub Repository:**
- Official specification: https://github.com/WebAssembly/spec
- Reference interpreter written in OCaml
- Formatted specification: https://webassembly.github.io/spec/

### 2.2 Mechanized Specifications in Theorem Provers

#### WasmCert Project

**WasmCert-Isabelle:**
- Mechanized specification in Isabelle/HOL theorem prover
- Verified executable interpreter and type checker
- Machine-verified proof of type soundness
- Exposed issues in official WebAssembly specification during mechanization
- Includes progress and preservation theorems

**WasmCert-Coq:**
- Repository: https://github.com/WasmCert/WasmCert-Coq
- Current master formalizes Wasm 2.0 plus future extension proposals
- Type safety results for Wasm typing system
- Soundness and completeness results for type checker
- Published at FM'21 conference

**Impact:**
- Close adherence to published language standard
- Exposed specification bugs that influenced WebAssembly development
- Provides foundation for certified software development in Coq community
- Both mechanizations distributed under open source licenses

#### K Framework Semantics

**KWasm:**
- Repository: https://github.com/runtimeverification/wasm-semantics
- Formal semantics of WebAssembly in K Framework
- Dual nature: both human-readable specification and correct-by-construction interpreter
- Supports concrete execution and symbolic reasoning

**Verification Applications:**
- Coverage measurement of test suites
- Formal verification of programs compiled to Wasm
- Used by Runtime Verification for smart contract verification
- Komet tool: K-powered fuzzing and formal verification for WebAssembly (Soroban)

### 2.3 Type Soundness and Memory Safety Proofs

**Soundness Theorems:**
- **Progress Theorem:** Well-typed programs either (a) are terminal values, (b) take evaluation step, or (c) trap
- **Preservation Theorem:** Programs remain well-typed as they execute
- Multiple mechanized proofs in Isabelle and Coq
- Recent work on "progressful interpreters" that certify both soundness and progress using dependent types

**Memory Safety Guarantees:**

Type Safety:
- Prevents invalid calls or illegal accesses to locals
- Guarantees proper function signatures
- Type checking at validation time (linear time)
- Runtime type checks for indirect calls

Memory Safety:
- Module memory protected from other modules
- Bounds checking at linear memory region level
- Implicit bounds check on every memory access (causes trap if out of bounds)
- Guard pages used to reduce bounds checking overhead
- Linear memory computed with infinite precision to avoid wrapping

Control-Flow Integrity:
- Immutable compiled code
- Protected call stack invulnerable to buffer overflows
- Code addresses and call stack are inaccessible
- Indirect calls subject to type signature checks
- Implements coarse-grained type-based CFI

**Important Limitations:**
- Memory safety only applies to WebAssembly's linear memory abstraction
- Does NOT prevent buffer overflows within data structures in linear memory
- Memory-unsafe C/C++ code remains unsafe when compiled to Wasm
- Vulnerabilities can be inherited from source languages
- Stack-based buffer overflows possible (no stack canaries by default)

### 2.4 Advanced Verification Research

#### MSWasm (Memory-Safe WebAssembly)

- Research project addressing WebAssembly's memory safety limitations
- Provides precise formal semantics proving robust memory safety
- Well-typed MSWasm programs are memory-safe by construction
- Enables reasoning about C-to-MSWasm compiler security guarantees
- ArXiv: https://arxiv.org/abs/2208.13583

#### CT-Wasm (Constant-Time WebAssembly)

- Repository: https://github.com/PLSysSec/ct-wasm
- Type-driven extension for cryptographic code
- Published at POPL 2019

**Security Guarantees:**
- Type system ensures information flow security
- Resistant to timing side-channel attacks
- Constant-time guarantees verifiable in linear time
- Mechanized in Coq with soundness proofs

**Implementations:**
- OCaml reference interpreter
- Native implementation for Node.js and Chromium (extends V8)
- CT-Wasm to Wasm rewrite tool

**Evaluation:**
- Ported Salsa20, SHA-256, TEA, and full TweetNaCl library
- Experimentally verified constant-time execution
- Demonstrates expressiveness for real cryptographic code

#### Iris-Wasm

- Published at PLDI 2023
- Paper: https://dl.acm.org/doi/abs/10.1145/3591265
- Higher-order separation logic framework
- Built on WasmCert-Coq specification
- Mechanized in Coq using Iris framework

**Capabilities:**
- Modular verification of individual modules
- Compositional reasoning across module boundaries
- Logical relation enforcing robust safety
- Proves unknown adversarial code can only affect modules through explicit exports
- Formal verification of functional correctness even with unknown code
- Demonstrates WebAssembly's strong module isolation

---

## 3. Verified Compilation and Certified Compilers

### 3.1 CompCert (Baseline for Comparison)

**Overview:**
- Formally verified optimizing C compiler
- Target architectures: ARM, PowerPC, RISC-V, x86
- Only production compiler formally verified to be exempt from miscompilation
- Proved to behave exactly as specified by C semantics
- Programmed and proven in Rocq (formerly Coq) proof assistant
- Received 2021 ACM Software System Award

**Relevance to Safety-Critical Systems:**
- Used for qualifying compilers under ISO 26262, IEC 61508
- Provides model for what verified compilation should achieve
- **Does NOT target WebAssembly** - this is a gap in the ecosystem

### 3.2 CertiCoq-Wasm

**Overview:**
- Repository: https://github.com/womeier/certicoqwasm
- Verified WebAssembly backend for CertiCoq
- Published at CPP 2025 conference
- Implemented and verified in Coq proof assistant

**Technical Details:**
- Compiles from Gallina (Coq programming language) to WebAssembly
- Works from CertiCoq's minimal lambda calculus in ANF
- Mechanized with respect to WasmCert-Coq formalization
- Verified correctness proof in theories/CodegenWasm/
- Implements Coq's primitive integer operations as efficient Wasm instructions
- Identified corner case leading to unsoundness in primitive operations

**Practical Applications:**
- Case study 1: Extracting and running Gallina program on web
- Case study 2: ConCert smart contract on Concordium blockchain
- Demonstrates practical usability of verified compilation
- Not yet available in upstream CertiCoq

### 3.3 Self-Certifying Compilation Framework

**Paper:** Springer Link: https://link.springer.com/chapter/10.1007/978-3-030-67067-2_7

**Approach:**
- Compiler generates correctness proof for each optimization
- Proofs checked automatically by independent proof validator
- Alternative to full compiler verification (CompCert style)

**Implementation:**
- Open source: https://github.com/nokia/web-assembly-self-certifying-compilation-framework
- Nokia research project
- Proof-carrying code approach for WebAssembly

**Comparison to CompCert:**
- CompCert: Verify compiler once, trust all compilations
- Self-certifying: Verify each compilation separately
- Self-certifying: More flexible, easier to extend
- CompCert: Stronger guarantees, higher assurance

### 3.4 LLVM and WebAssembly Backend

**Current Status:**
- Clean WebAssembly backend in upstream Clang/LLVM
- Used by Emscripten and PNaCl projects
- Built-in control-flow integrity extended to WebAssembly target
- No formal verification of LLVM WebAssembly backend exists

**Related Work:**
- Crellvm: Verified credible compilation for LLVM (general, not Wasm-specific)
- VeriWasm: Translation validator for Cranelift-compiled WebAssembly
- Gap: No CompCert-style verified LLVM backend for WebAssembly

---

## 4. Proof-Carrying Code and Formal Methods

### 4.1 Proof-Carrying Code Approaches

**Historical Context:**
- PCC pioneered by George Necula at Berkeley
- Classic approach: Code carries formal proof of safety properties
- Inspired by JVM bytecode verifier and .NET verification

**WebAssembly Applications:**

**GitHub Discussion:**
- Issue #492: https://github.com/WebAssembly/design/issues/492
- Proposals for PCC-inspired verification
- Ensure programs don't overwrite memory outside their bounds
- Store proofs alongside WebAssembly modules

**Wasmtime Implementation:**
- Proof-carrying code in Cranelift/Wasmtime
- Carries "facts" about program values from IR to machine code
- Checks facts against machine instruction semantics
- Guards against instruction lowering bugs
- Prevents holes in Wasm sandbox

### 4.2 Runtime Verification and Translation Validation

#### VeriWasm

**Overview:**
- UCSD, Stanford, and Fastly collaboration
- Static offline verifier for native x86-64 binaries
- Performs static analysis of disassembled machine code

**Verification Approach:**
- Proves all heap accesses are properly to Wasm heap
- Cannot escape sandbox
- Forwards static analysis
- Originally for AOT-compiled Wasm

**Challenges:**
- Chris Fallin attempted revival for modern Wasmtime
- Found forwards static analysis too difficult and slow
- Led to alternative PCC-based solution

#### VeriISLE

**Paper:** CMU-CS-23-126: http://reports-archive.adm.cs.cmu.edu/anon/2023/CMU-CS-23-126.pdf

**Approach:**
- Modular verification for Cranelift instruction lowering
- Annotation language for ISLE (instruction selector DSL)
- Concise semantics alongside definitions
- Eliminates instruction lowering as source of sandbox escapes

**Verification Techniques:**
- Formally verified CLIF to machine instruction lowerings
- Covers all integer operations in aarch64 backend
- Proves correctness for all compilations
- Symbolic translation validation

### 4.3 Formal Verification Tools

#### wasm-verify

- Proof-of-concept formal verification tool
- Design-by-contract approach
- Specification language for:
  - Preconditions
  - Loop invariants
  - Postconditions

#### Stack Builders Tool

- Source: https://www.stackbuilders.com/insights/increasing-confidence-in-WebAssembly-code-with-formal-verification/
- Increases confidence in WebAssembly code
- Formal verification platform

#### Wasmati

**Paper:** https://www.sciencedirect.com/science/article/pii/S0167404822001407

**Approach:**
- Static vulnerability scanner for WebAssembly
- Based on code property graph (CPG) generation
- Detects security vulnerabilities in WebAssembly binaries

**Capabilities:**
- Buffer overflow detection in loops
- Identifies when buffer bounds not checked in loop exit conditions
- Static analysis specifically designed for WebAssembly's representation

---

## 5. Qualification Strategies for WebAssembly Runtimes

### 5.1 Tool Qualification Under Safety Standards

#### ISO 26262 Tool Qualification

**Tool Confidence Levels (TCL):**
- TCL1: No qualification needed
- TCL2: Moderate confidence required
- TCL3: Highest confidence (typical for compilers)

**Determination Factors:**
- Tool Impact (TI): Can error lead to safety hazard?
- Tool Error Detection (TD): Probability of preventing/detecting errors

**Compiler Qualification:**
- Extremely difficult to verify compilers systematically
- TCL3 typically assigned to compilers
- ASIL level determines qualification methods
- For ASIL D: Requires validation of software tool itself
- Qualification requirements:
  - Verification on target system hardware
  - Documented errors that can be avoided
  - State-of-the-art verification techniques
  - Structural code coverage analysis (ASIL D)

**WebAssembly Implications:**
- Both WebAssembly compiler AND runtime would need qualification
- Two-stage compilation (source → Wasm → native) complicates qualification
- Could qualify Wasm as intermediate representation
- Runtime/JIT compiler would need separate qualification

#### DO-330 Tool Qualification (Avionics)

**Requirements:**
- Tool Operational Requirements (TOR)
- Tool Qualification Plan
- Tool verification cases
- Tool qualification data

**WebAssembly Gaps:**
- No documented qualification efforts found
- Would require extensive qualification data
- Multi-stage compilation creates challenges
- Runtime compilation/JIT would need specific consideration

### 5.2 WebAssembly Runtime Implementations

#### Wasmtime

**Repository:** https://github.com/bytecodealliance/wasmtime
**Organization:** Bytecode Alliance

**Security Approach:**
- Implemented in Rust (memory-safe language)
  - 70% of browser security bugs are memory safety issues
  - Rust eliminates this class of bugs
- Formal verification collaboration with academic researchers
- VeriWasm integration for translation validation
- Proof-carrying code in Cranelift
- Security-focused design

**Formal Verification Efforts:**
- Collaborating with academic researchers
- Formal verification of critical Cranelift parts
- Translation validation
- Proof-carrying code guards against lowering bugs

**Known Vulnerabilities:**
- CVE-2023-26489: Memory out-of-bounds read/write
- Demonstrates need for ongoing verification

#### WAMR (WebAssembly Micro Runtime)

**Repository:** https://github.com/bytecodealliance/wasm-micro-runtime
**Organization:** Bytecode Alliance

**Target Applications:**
- Embedded systems and IoT
- Edge computing
- Trusted Execution Environments (TEE)
- Smart contracts
- Cloud native applications

**Technical Characteristics:**
- Small binary size:
  - ~85K for interpreter
  - ~50K for AOT
- Low memory usage
- Highly configurable

**Execution Modes:**
- Interpreter
- Ahead-of-Time (AOT) compilation
- Just-in-Time (JIT) compilation
  - Fast JIT tier
  - LLVM JIT tier
  - Dynamic tier-up

**Platform Support:**
- Linux, Linux SGX, MacOS, Android, Windows
- **RTOS:** Zephyr, VxWorks, NuttX, RT-Thread, FreeRTOS (ESP-IDF)
- AliOS-Things

**Licensing:**
- Apache 2.0 with LLVM exception
- Allows commercial use

**Safety-Critical Relevance:**
- RTOS integration crucial for embedded safety-critical systems
- AOT compilation provides determinism
- Small footprint suitable for resource-constrained devices
- Certification status unknown

### 5.3 RTOS Integration

#### Zephyr RTOS Integration

**Project:** Ocre (LF Edge)
- WebAssembly containers on Zephyr
- OCI-like containers over 1,000x lighter than Docker/Podman
- Leverages WAMR for execution

**Advantages of Zephyr:**
- Modular, configurable design
- Rich subsystems and libraries
- Supports over 700 boards
- Better library support than FreeRTOS

**Platform Agnostic:**
- Reference implementation on Zephyr
- Can be ported to FreeRTOS, VxWorks, Linux

**Safety-Critical Potential:**
- RTOS provides real-time scheduling
- Memory management
- Interrupt handling
- Deterministic execution
- Could enable safety-certified Wasm runtime

#### FreeRTOS

**Integration Status:**
- WAMR supports FreeRTOS (ESP-IDF)
- Initially used by Ocre project
- Limited library support compared to Zephyr
- Less flexibility

**Certification Context:**
- SAFERTOS: Safety-certified variant
- Could potentially run certified WAMR

### 5.4 Determinism and Real-Time Behavior

**WebAssembly Determinism:**

**Generally Deterministic Execution:**
- Limited sources of non-determinism
- Can be controlled by:
  - Disabling threads
  - Disabling non-deterministic SIMD instructions
  - Canonicalizing floating-point NaN values

**Current Limitations:**
- No threads in base WebAssembly (yet)
- No concurrent memory access non-determinism
- Careful control of extension features needed

**Real-Time Suitability:**
- AOT compilation provides predictable execution
- No garbage collector pauses
- Bounded execution time possible
- Memory bounds known at instantiation
- Suitable for hard real-time with proper runtime

**Safety-Critical Implications:**
- Determinism required for ISO 26262 ASIL C/D
- Reproducible execution needed for certification
- WebAssembly offers better determinism than JavaScript
- Comparable to native code when using AOT

---

## 6. Safety Guarantees of WebAssembly

### 6.1 Type Safety

**Validation-Time Guarantees:**
- Linear-time validation algorithm
- Single-pass over bytecode
- Integrated into decoder
- Decidable type checking
- Sound and complete algorithm

**Type System Properties:**
- Structural typing for functions
- Numeric types only (i32, i64, f32, f64)
- Reference types (funcref, externref)
- No composite data structures at type level
- No "uninitialized" values possible

**Runtime Type Checks:**
- Indirect function calls type-checked at runtime
- Single pointer comparison cost
- Coarse-grained control-flow integrity
- Table-based vtables in trusted space

### 6.2 Memory Safety

**Module-Level Isolation:**
- Each module has isolated linear memory
- Protected from other modules
- Even in same virtual address space
- Cannot access other module's memory

**Bounds Checking:**
- Implicit bounds check on every memory access
- Causes trap if out of bounds
- Guard pages reduce overhead (wasm32)
- V8 uses explicit bounds checks
- Infinite precision computation (no wrapping)

**Linear Memory Characteristics:**
- Contiguous byte array
- Accessed by load/store instructions
- Growable (memory.grow)
- Initial and maximum size specified
- Bounds enforced by runtime

**Stack Protection:**
- Call stack separate from linear memory
- Not directly accessible to code
- Invulnerable to buffer overflows
- Protected returns

**Limitations:**
- Bounds checking at region granularity, not object-level
- Buffer overflows within linear memory data structures POSSIBLE
- No protection for C/C++ data structures
- Unsafe source code remains unsafe

### 6.3 Control-Flow Integrity

**Built-in CFI:**
- Immutable compiled code
- Cannot modify code at runtime
- Structured control flow (blocks, loops, if)
- Indirect calls type-checked

**Attack Prevention:**
- No code injection possible
- Buffer overflows cannot affect control flow
- Protected call stack
- Code addresses inaccessible

**Mitigations Not Needed:**
- Data Execution Prevention (DEP) - built-in
- Stack Smashing Protection (SSP) - stack protected
- Address Space Layout Randomization (ASLR) - sandbox isolated

### 6.4 Sandboxing and Isolation

**Module Isolation:**
- Strong isolation between modules
- Iris-Wasm proves robust safety
- Unknown adversarial code only affects through explicit exports
- Capability-based security model

**WASI Capability Model:**
- WebAssembly System Interface
- Principle of least privilege
- Pre-opened directories for filesystem
- Constrained sockets for networking
- Explicit environment variable enumeration
- Runtime controls capabilities

**Embedded/IoT Applications:**
- Proof-of-concept WASI-USB interface
- WASI-I2C interface
- Hardware isolation with pluggable drivers
- Minimal overhead (8% for USB)
- Enhances supply chain security

---

## 7. Standards Compliance Approaches

### 7.1 Current State Assessment

**Production Deployments:**
- **ISO 26262 (Automotive):** No documented WebAssembly deployments found
- **IEC 62304 (Medical):** No documented WebAssembly deployments found
- **DO-178C (Avionics):** No documented WebAssembly deployments found

**Research & Development:**
- WasmCon 2024 panel: "Safety-Critical Meets Web-Native"
- Academic research on formal verification
- Proof-of-concept embedded systems
- Bytecode Alliance working on standards

**Gap Analysis:**
- No specific regulatory guidance for WebAssembly
- No qualified compilers or runtimes
- No certification artifacts available
- Tool qualification data missing
- Hazard analysis methodologies not established

### 7.2 Potential Qualification Pathways

#### Pathway 1: Runtime Qualification

**Approach:**
- Qualify WebAssembly runtime as execution platform
- Analogous to Java VM or .NET CLR qualification
- Runtime becomes qualified tool

**Requirements:**
- Tool Operational Requirements (TOR)
- Verification of runtime behavior
- Hazard analysis of runtime failures
- Regression test suite
- Configuration management

**Challenges:**
- JIT compilation complicates verification
- AOT mode more amenable to qualification
- Need deterministic execution guarantees
- Memory management verification

#### Pathway 2: Compiler + Runtime Qualification

**Approach:**
- Qualify source-to-Wasm compiler
- Qualify Wasm runtime separately
- Composition of qualified tools

**Requirements:**
- Separate TOR for each tool
- Interface specification between tools
- End-to-end verification
- Traceability through compilation stages

**Advantages:**
- Modular qualification
- Can update tools independently
- Clear separation of concerns

**Challenges:**
- Two-stage qualification costly
- Interface verification complex
- Combined failure modes must be analyzed

#### Pathway 3: Formal Verification Approach

**Approach:**
- Leverage mechanized specifications (WasmCert)
- Use verified compilation (CertiCoq-Wasm style)
- Provide formal correctness proofs

**Requirements:**
- Mechanized specification in Coq/Isabelle
- Extracted verified interpreter/compiler
- Soundness proofs
- Memory safety proofs
- Control-flow integrity proofs

**Advantages:**
- Strongest assurance
- Mathematical guarantees
- Reduced testing burden
- Follows CompCert model

**Challenges:**
- High development cost
- Requires theorem proving expertise
- Performance vs. verification tradeoff
- Regulatory acceptance uncertain

#### Pathway 4: Self-Certifying Compilation

**Approach:**
- Generate proof for each compilation
- Independent proof checker
- Runtime verification

**Requirements:**
- Proof generation in compiler
- Verified proof checker (small TCB)
- Proof artifacts as part of qualification data
- Proof checking in build process

**Advantages:**
- Catches compilation errors
- Smaller trusted computing base
- More flexible than full verification
- Each compilation independently verified

**Challenges:**
- Proof generation overhead
- Proof checking performance
- Storage of proof artifacts
- Regulatory acceptance

### 7.3 Bytecode Alliance Initiatives

**Organization:**
- Founded by Mozilla, Fastly, Intel, Red Hat
- Nonprofit dedicated to secure software foundations
- Leading WASI standards development
- Leading Rust to WebAssembly working group

**Security Vision:**
- Secure by default ecosystem
- Fix software foundation vulnerabilities
- Safe use of untrusted code
- Nanoprocesses with limited capabilities

**Standards Leadership:**
- WebAssembly Community Group (W3C)
- WASI Subgroup
- Component Model development
- Interface Type standardization

**Roadmap:**
- WASI Preview 2 implementation
- Component Model finalization
- Dog Food Registry (security reviewed)
- Safety and security standards development

**Safety-Critical Potential:**
- Industry collaboration
- Standards-based approach
- Security focus aligns with safety
- Could develop certification guidance

### 7.4 Specific Challenges for Safety Standards

#### ISO 26262 Challenges

**Software Classification:**
- Where does Wasm fit in software architecture?
- ASIL decomposition across Wasm boundary?
- Safety mechanisms in Wasm modules vs. runtime

**V-Model Integration:**
- How to integrate Wasm in development process?
- Verification methods for Wasm code
- Testing strategies for Wasm modules
- Traceability through compilation

**AUTOSAR Integration:**
- Classic Platform: deeply embedded, predictable
- Adaptive Platform: more flexible
- No documented AUTOSAR + Wasm integration
- Would need platform-specific guidance

#### IEC 62304 Challenges

**Software Safety Classification:**
- How to classify Wasm runtime (Class A/B/C)?
- How to classify Wasm modules?
- Risk analysis for runtime failures
- Hazard analysis methodology

**Lifecycle Processes:**
- Software development planning
- Requirements analysis
- Architectural design
- Detailed design
- Unit testing
- Integration testing
- System testing

**SOUP (Software of Unknown Provenance):**
- Is public Wasm runtime SOUP?
- How to qualify open-source runtimes?
- Anomaly list requirements
- Known vulnerabilities documentation

#### DO-178C Challenges

**Software Level Determination:**
- Level A (catastrophic)
- Level B (hazardous)
- Level C (major)
- Level D (minor)
- Level E (no safety effect)

**Objectives Compliance:**
- Requirements-based testing
- Structural coverage analysis
- Traceability
- Verification independence

**Tool Qualification (DO-330):**
- Development tool qualification
- Verification tool qualification
- Compiler as development and verification tool
- Runtime environment qualification

---

## 8. Research Gaps and Future Directions

### 8.1 Current Research Gaps

**Certification Guidance:**
- No published qualification strategies
- No regulatory position papers
- No industry consensus on approaches
- No standard certification artifacts

**Tool Qualification:**
- No qualified WebAssembly compilers
- No qualified WebAssembly runtimes
- No qualification kits available
- No TCL/TQL determination guidance

**Hazard Analysis:**
- No standard hazard analysis methods
- No failure mode analysis for Wasm
- No common mode failure analysis
- No systematic approach to Wasm-specific hazards

**Testing and Verification:**
- No MC/DC testing guidance for Wasm
- No structural coverage tools
- No formal verification integration with certification
- No requirements traceability tools

**Real-World Deployments:**
- No public case studies
- No lessons learned
- No best practices
- No performance data for safety-critical applications

### 8.2 Promising Research Directions

**Verified Compilation:**
- Extend CompCert to WebAssembly target
- More verified backends (CertiCoq-Wasm model)
- Integration with WasmCert specifications
- Verified JIT compilers

**Runtime Verification:**
- Extend VeriWasm to modern runtimes
- Proof-carrying code standardization
- Runtime monitoring frameworks
- Formal methods for AOT compilation

**Determinism and Real-Time:**
- Real-time WebAssembly profile
- WCET analysis tools
- Scheduling analysis
- Integration with real-time operating systems

**Safety Patterns:**
- Safe subset definitions
- Coding standards (MISRA-like)
- Architecture patterns for safety
- Partitioning strategies

**Formal Methods Integration:**
- Seamless Coq/Isabelle to Wasm compilation
- Proof preservation through compilation
- Runtime proof checking
- Verified libraries for safety-critical applications

### 8.3 Industry Collaboration Needs

**Standards Bodies:**
- ISO TC 22 SC 32 WG 8 (ISO 26262)
- IEC SC 62A (IEC 62304)
- RTCA SC-205 (DO-178C)
- W3C WebAssembly Community Group

**Potential Activities:**
- Position papers on Wasm in safety-critical
- Addendums to existing standards
- Qualification guidance documents
- Reference architectures

**Industry Consortia:**
- Bytecode Alliance safety initiatives
- AUTOSAR WebAssembly working group (potential)
- Medical device manufacturers collaboration
- Automotive OEM collaboration

---

## 9. Practical Recommendations

### 9.1 For Researchers

**High-Priority Research:**
1. Complete verified compilation chain (source to Wasm to native)
2. Develop qualification strategies for ISO 26262, IEC 62304, DO-178C
3. Create real-time WebAssembly profile
4. Develop WCET analysis tools
5. Create safety-oriented coding standards

**Collaboration Opportunities:**
- Work with Bytecode Alliance
- Engage with standards bodies
- Partner with medical device/automotive companies
- Publish certification case studies

### 9.2 For Industry

**Near-Term:**
1. Evaluate WebAssembly for non-safety-critical components
2. Develop hazard analysis methodologies
3. Assess tool qualification requirements
4. Build internal expertise
5. Participate in standards development

**Medium-Term:**
1. Pilot projects in lower-ASIL automotive
2. Proof-of-concept in Class A medical devices
3. Develop qualification artifacts
4. Create internal coding standards
5. Build verification toolchains

**Long-Term:**
1. Full qualification for ASIL D / Class C / Level A
2. Production deployments
3. Contribute to public certification guidance
4. Develop certified runtimes
5. Share lessons learned

### 9.3 For Tool Developers

**Priority Features:**
1. Deterministic execution modes
2. AOT compilation with verification
3. WCET analysis support
4. Structural coverage tools
5. Requirements traceability
6. Safety-oriented profiles

**Certification Support:**
1. Develop tool qualification kits
2. Create verification test suites
3. Document known limitations
4. Provide safety manuals
5. Support evidence generation

---

## 10. Conclusions

### 10.1 Current State

WebAssembly has strong theoretical foundations for safety-critical use:
- Formally specified semantics
- Multiple mechanized proofs of soundness
- Strong type safety and memory safety at module level
- Control-flow integrity
- Sandboxing and isolation

However, practical deployment in certified systems faces significant challenges:
- No documented production deployments in ISO 26262, IEC 62304, or DO-178C contexts
- No qualified compilers or runtimes available
- No regulatory guidance or industry consensus
- Tool qualification pathways unclear
- Real-time and determinism guarantees need more work

### 10.2 Formal Verification Achievements

Significant formal verification work has been accomplished:
- **WasmCert (Isabelle & Coq):** Mechanized specifications with soundness proofs
- **K Framework:** Executable semantics with verification capabilities
- **Iris-Wasm:** Separation logic for modular verification
- **CT-Wasm:** Verified constant-time cryptography
- **CertiCoq-Wasm:** Verified compilation from Coq
- **VeriWasm/VeriISLE:** Translation validation for native code
- **MSWasm:** Enhanced memory safety guarantees

These provide strong foundation for certification but need integration into qualification processes.

### 10.3 Path Forward

The path to WebAssembly qualification for safety-critical systems requires:

1. **Standardization:** Development of qualification guidance by standards bodies
2. **Tool Qualification:** Creation of qualified compilers and runtimes
3. **Industry Collaboration:** Sharing of approaches, challenges, and solutions
4. **Research Translation:** Converting academic verification work into certification artifacts
5. **Pilot Projects:** Real-world demonstrations in lower-criticality systems
6. **Regulatory Engagement:** Working with certification authorities for acceptance

### 10.4 Outlook

WebAssembly has significant potential for safety-critical embedded systems:
- Strong security properties align with safety needs
- Formal verification provides high assurance
- Sandboxing enables mixed-criticality systems
- Portability reduces hardware lock-in
- Small footprint suits embedded constraints

However, substantial work remains before production deployment in certified systems. The next 3-5 years will be critical for establishing qualification pathways, developing certified tools, and demonstrating real-world viability.

The combination of strong formal foundations, active research community, and industry interest through the Bytecode Alliance suggests that WebAssembly qualification for safety-critical systems is achievable, though significant effort will be required to bridge the gap between research and certification.

---

## 11. References and Resources

### 11.1 Key Academic Papers

**WebAssembly Specification and Semantics:**
- "Mechanising and Verifying the WebAssembly Specification" (CPP 2018)
- "Two Mechanisations of WebAssembly 1.0" (FM 2021)
- "Bringing the Web up to Speed with WebAssembly" (PLDI 2017, CACM)
- "Bringing the WebAssembly Standard up to Speed with SpecTec" (POPL 2024)

**Formal Verification:**
- "Iris-Wasm: Robust and Modular Verification of WebAssembly Programs" (PLDI 2023)
- "CT-Wasm: Type-Driven Secure Cryptography for the Web Ecosystem" (POPL 2019)
- "Memory Safety Preservation for WebAssembly" (PriSC 2020)
- "MSWasm: Soundly Enforcing Memory-Safe Execution of Unsafe Code" (OOPSLA 2022)

**Verified Compilation:**
- "CertiCoq-Wasm: A Verified WebAssembly Backend for CertiCoq" (CPP 2025)
- "A Self-certifying Compilation Framework for WebAssembly" (FASE 2021)

**Security and Analysis:**
- "Wasmati: An Efficient Static Vulnerability Scanner for WebAssembly" (COSE 2022)
- "Everything Old is New Again: Binary Security of WebAssembly" (USENIX Security 2020)
- "Provably-Safe Multilingual Software Sandboxing using WebAssembly" (USENIX 2022)

### 11.2 GitHub Repositories

**Specifications and Mechanizations:**
- Official WebAssembly spec: https://github.com/WebAssembly/spec
- WasmCert-Coq: https://github.com/WasmCert/WasmCert-Coq
- K Framework semantics: https://github.com/runtimeverification/wasm-semantics
- CT-Wasm: https://github.com/PLSysSec/ct-wasm
- CertiCoq-Wasm: https://github.com/womeier/certicoqwasm

**Runtimes:**
- Wasmtime: https://github.com/bytecodealliance/wasmtime
- WAMR: https://github.com/bytecodealliance/wasm-micro-runtime

**Tools:**
- Self-certifying framework: https://github.com/nokia/web-assembly-self-certifying-compilation-framework

### 11.3 Standards and Specifications

**Safety Standards:**
- ISO 26262:2018 - Road vehicles — Functional safety
- IEC 62304:2006 - Medical device software — Software life cycle processes
- DO-178C - Software Considerations in Airborne Systems and Equipment Certification
- DO-330 - Software Tool Qualification Considerations
- IEC 61508 - Functional Safety of Electrical/Electronic/Programmable Electronic Safety-related Systems

**WebAssembly Standards:**
- WebAssembly Core Specification: https://webassembly.github.io/spec/
- WASI (WebAssembly System Interface): https://github.com/WebAssembly/WASI

### 11.4 Organizations

**Standards Bodies:**
- W3C WebAssembly Community Group
- Bytecode Alliance: https://bytecodealliance.org/
- ISO TC 22 SC 32 (Road vehicles - Functional safety)
- IEC SC 62A (Common aspects of electrical equipment used in medical practice)
- RTCA SC-205 (Software Considerations in Airborne Systems)

### 11.5 Tools and Frameworks

**Theorem Provers:**
- Coq/Rocq: https://coq.inria.fr/
- Isabelle/HOL: https://isabelle.in.tum.de/
- K Framework: https://kframework.org/
- Iris Project: https://iris-project.org/

**Verified Compilers:**
- CompCert: https://compcert.org/

**WebAssembly Tools:**
- Emscripten: https://emscripten.org/
- wabt (WebAssembly Binary Toolkit): https://github.com/WebAssembly/wabt

---

## Document Information

**Author:** AI Research Assistant
**Date:** 2025-11-16
**Version:** 1.0
**Purpose:** Comprehensive research on WebAssembly formal verification and safety-critical system qualification

**Scope:**
- Formal verification techniques
- Safety standards (ISO 26262, IEC 62304, DO-178C)
- Verified compilation approaches
- Runtime qualification strategies
- Memory safety and type safety guarantees
- Current research state and gaps

**Limitations:**
- Based on publicly available information as of November 2025
- No access to proprietary certification efforts
- Rapidly evolving field - some information may become outdated
- No hands-on certification experience represented

**Recommendations for Use:**
- Starting point for certification planning
- Research direction identification
- Gap analysis for qualification projects
- Educational resource for formal methods in safety-critical systems
