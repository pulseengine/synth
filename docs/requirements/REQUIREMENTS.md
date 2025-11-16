# Synth: WebAssembly Component Synthesizer Requirements

**Project:** Synth - WebAssembly Component Model Synthesizer for Embedded Systems
**Version:** 0.1.0
**Last Updated:** 2025-11-16
**Status:** Draft

---

## 1. Executive Summary

Synth is a **synthesis tool** for WebAssembly Component Model applications targeting embedded systems. Unlike traditional compilers or transpilers, Synth **synthesizes** optimal native implementations from WebAssembly components, similar to how VHDL synthesis generates optimized hardware layouts.

### Analogy: Hardware Synthesis for Software

Just as VHDL synthesis transforms high-level hardware descriptions to optimized gate-level implementations:

```
VHDL → Synthesis → Optimized Gates/Layout → FPGA/ASIC
```

Synth transforms WebAssembly components to optimized native implementations:

```
WebAssembly Components → Synthesis → Optimized Native Code → ARM/RISC-V
```

### Key Differentiators

1. **Component-Aware:** Analyzes entire component compositions, not individual modules
2. **Hardware-Integrated:** Leverages MPU/PMP for bounds checking, multi-memory for isolation
3. **Target-Optimized:** Synthesizes code specifically for Cortex-M, RISC-V embedded profiles
4. **Formally Verified:** Proof-carrying synthesis with mechanically-verified correctness
5. **Safety-Qualified:** Designed for automotive, medical, industrial certification

---

## 2. Business Requirements

### BR-001: Safety-Critical Qualification
**Priority:** MUST HAVE
**Rationale:** Target automotive (ISO 26262), medical (IEC 62304), industrial sectors

**Requirements:**
- BR-001.1: Generate qualification artifacts for safety standards
- BR-001.2: Support formal verification of synthesis correctness
- BR-001.3: Provide traceability from WebAssembly to native code
- BR-001.4: Enable deterministic, reproducible builds
- BR-001.5: Support qualified tool chain integration (CompCert, etc.)

### BR-002: Competitive Performance
**Priority:** MUST HAVE
**Rationale:** Must achieve ≥80% native performance for adoption

**Requirements:**
- BR-002.1: Synthesize code achieving ≥80% of hand-written native performance
- BR-002.2: Support AOT compilation for deterministic execution
- BR-002.3: Enable hardware-accelerated bounds checking (MPU/PMP)
- BR-002.4: Support XIP (execute-in-place) for flash-constrained systems
- BR-002.5: Minimize code size (<20% overhead vs native)

### BR-003: Multi-Target Support
**Priority:** MUST HAVE
**Rationale:** Support major embedded architectures

**Requirements:**
- BR-003.1: ARM Cortex-M (M3, M4, M7, M33, M55)
- BR-003.2: RISC-V (RV32IMAC, RV32GC, RV64GC)
- BR-003.3: Extensible architecture for additional targets
- BR-003.4: Target-specific optimization opportunities
- BR-003.5: Hardware feature detection and adaptation

### BR-004: Developer Experience
**Priority:** SHOULD HAVE
**Rationale:** Enable rapid adoption and development

**Requirements:**
- BR-004.1: Simple CLI interface for synthesis
- BR-004.2: Integration with standard toolchains (Clang, Rust, GCC)
- BR-004.3: Clear error messages and diagnostics
- BR-004.4: Documentation and examples
- BR-004.5: Profiling and optimization guidance

---

## 3. Functional Requirements

### FR-001: Component Model Support
**Priority:** MUST HAVE

**Requirements:**
- FR-001.1: Parse WebAssembly Component Model binary format
- FR-001.2: Validate component structure and interfaces
- FR-001.3: Support WIT (WebAssembly Interface Types) definitions
- FR-001.4: Handle component composition (shared-everything and shared-nothing)
- FR-001.5: Support canonical ABI lowering and lifting
- FR-001.6: Multi-memory proposal support for isolation

### FR-002: Synthesis Pipeline
**Priority:** MUST HAVE

**Requirements:**
- FR-002.1: **Analysis Phase**
  - Component dependency graph construction
  - Memory layout analysis
  - Call graph construction
  - Data flow analysis
  - Hardware capability detection

- FR-002.2: **Optimization Phase**
  - Dead code elimination across components
  - Function inlining (cross-component where beneficial)
  - Constant propagation
  - Memory layout optimization
  - Bounds check optimization

- FR-002.3: **Synthesis Phase**
  - Target-specific instruction selection (ISLE-based)
  - Register allocation
  - Hardware protection mapping (MPU/PMP)
  - XIP binary generation
  - Relocation and linking

- FR-002.4: **Verification Phase**
  - Translation validation (SMT-based)
  - Bounds checking verification
  - CFI verification
  - Memory isolation proofs

### FR-003: Memory Management
**Priority:** MUST HAVE

**Requirements:**
- FR-003.1: **Linear Memory Synthesis**
  - Allocate linear memories for components
  - Optimize memory layout for target
  - Generate bounds checking code
  - Support static and dynamic memories

- FR-003.2: **Multi-Memory Support**
  - Map WebAssembly memories to hardware protection regions
  - MPU region allocation for ARM Cortex-M
  - PMP entry allocation for RISC-V
  - Optimize for hardware-accelerated bounds checking

- FR-003.3: **Memory Protection**
  - Generate MPU/PMP configuration code
  - Synthesize bounds checks using hardware traps where possible
  - Fall back to software checks when hardware unavailable
  - Verify memory isolation between components

### FR-004: Direct Function Calls
**Priority:** SHOULD HAVE

**Requirements:**
- FR-004.1: Devirtualize component imports/exports when possible
- FR-004.2: Replace indirect calls with direct calls for known targets
- FR-004.3: Inline component boundaries for shared-everything linking
- FR-004.4: Optimize calling conventions for target architecture

### FR-005: Target-Specific Optimizations
**Priority:** MUST HAVE

**Requirements:**
- FR-005.1: **ARM Cortex-M**
  - Thumb-2 instruction selection
  - Helium (MVE) SIMD support for M55
  - MPU configuration (8/16 regions)
  - FPU detection and optimization
  - XIP support for flash execution

- FR-005.2: **RISC-V**
  - Compressed instruction support (C extension)
  - Bit manipulation (B extension) when available
  - Vector extension support (V extension)
  - PMP configuration (up to 16 entries)
  - Custom instruction support

### FR-006: Formal Verification
**Priority:** SHOULD HAVE (MUST HAVE for safety-critical)

**Requirements:**
- FR-006.1: **Synthesis Rule Verification**
  - ISLE-based synthesis rules
  - SMT-based verification (VeriISLE approach)
  - Mechanized semantics in Coq/Lean
  - Proof of correctness for each rule

- FR-006.2: **Translation Validation**
  - Per-compilation SMT checking (Alive2 approach)
  - Verify WebAssembly semantics preserved
  - Check bounds checking correctness
  - Validate control-flow integrity

- FR-006.3: **Memory Safety Proofs**
  - Prove linear memory bounds
  - Verify no cross-component access (shared-nothing)
  - Validate MPU/PMP configuration correctness
  - Check stack isolation

### FR-007: Optimization Framework
**Priority:** SHOULD HAVE

**Requirements:**
- FR-007.1: **E-Graph Optimization**
  - Equality saturation for component-level optimization
  - Integration with egg library
  - Provably optimal code extraction
  - Avoid phase-ordering problems

- FR-007.2: **Link-Time Optimization**
  - Cross-component optimization for shared-everything linking
  - Dead code elimination across boundaries
  - Constant propagation through component interfaces
  - Function specialization

### FR-008: Safety Guarantees
**Priority:** MUST HAVE

**Requirements:**
- FR-008.1: **Maintain WebAssembly Safety Properties**
  - Memory bounds checking (explicit or hardware-assisted)
  - Control-flow integrity (typed indirect calls)
  - Module/component isolation
  - Stack protection
  - Deterministic traps

- FR-008.2: **Additional Safety for Embedded**
  - Worst-case execution time (WCET) analysis support
  - Real-time determinism (no GC, no JIT)
  - Stack overflow detection
  - Hardware fault integration (MPU/PMP faults)

---

## 4. Non-Functional Requirements

### NFR-001: Performance
**Priority:** MUST HAVE

**Requirements:**
- NFR-001.1: Compilation speed <10x slower than LLVM
- NFR-001.2: Generated code ≥80% of native performance
- NFR-001.3: Code size <120% of native equivalent
- NFR-001.4: Startup time <100ms for typical embedded application
- NFR-001.5: Memory footprint <512KB for synthesizer runtime

### NFR-002: Reliability
**Priority:** MUST HAVE

**Requirements:**
- NFR-002.1: No compiler crashes (handle all valid inputs)
- NFR-002.2: Deterministic output (same input → same output)
- NFR-002.3: Comprehensive error handling
- NFR-002.4: >99% correctness on WebAssembly test suite
- NFR-002.5: Continuous fuzzing integration

### NFR-003: Maintainability
**Priority:** SHOULD HAVE

**Requirements:**
- NFR-003.1: Written in Rust for memory safety
- NFR-003.2: Modular architecture (pluggable backends)
- NFR-003.3: Comprehensive test suite (unit, integration, end-to-end)
- NFR-003.4: Clear code documentation
- NFR-003.5: CI/CD pipeline with automated testing

### NFR-004: Portability
**Priority:** SHOULD HAVE

**Requirements:**
- NFR-004.1: Run on Linux, macOS, Windows
- NFR-004.2: Support cross-compilation
- NFR-004.3: Minimal dependencies
- NFR-004.4: Container-based distribution option

### NFR-005: Security
**Priority:** MUST HAVE

**Requirements:**
- NFR-005.1: No unsafe Rust except in isolated, audited modules
- NFR-005.2: Input validation for all WebAssembly files
- NFR-005.3: Bounds checking in synthesizer itself
- NFR-005.4: Regular security audits
- NFR-005.5: CVE response process

---

## 5. Technical Requirements

### TR-001: Input Formats
**Priority:** MUST HAVE

**Requirements:**
- TR-001.1: WebAssembly Component Model binary (.wasm)
- TR-001.2: WIT interface definitions (.wit)
- TR-001.3: Configuration files for synthesis options (TOML/YAML)
- TR-001.4: Target specification files

### TR-002: Output Formats
**Priority:** MUST HAVE

**Requirements:**
- TR-002.1: **Native Binary Formats**
  - ELF for embedded Linux
  - Raw binary for bare-metal
  - HEX/BIN for flash programming

- TR-002.2: **Intermediate Formats**
  - LLVM IR (for integration with LLVM toolchain)
  - Textual assembly (.s files)
  - Object files (.o) for linking

- TR-002.3: **Metadata**
  - Debug information (DWARF)
  - Profiling information
  - Verification artifacts (proofs, SMT traces)

### TR-003: Toolchain Integration
**Priority:** SHOULD HAVE

**Requirements:**
- TR-003.1: Integration with Clang/LLVM
- TR-003.2: Integration with Rust toolchain
- TR-003.3: Integration with GCC (for CompCert)
- TR-003.4: CMake/Cargo build system support
- TR-003.5: IDE integration (LSP for WIT files)

### TR-004: Synthesis Configuration
**Priority:** MUST HAVE

**Requirements:**
- TR-004.1: **Target Selection**
  - CPU architecture (arm, riscv)
  - Specific variant (cortex-m4, rv32imac)
  - Available features (fpu, simd, mpu, pmp)

- TR-004.2: **Memory Configuration**
  - Flash size and location
  - RAM size and location
  - MPU/PMP region count and sizes
  - Stack sizes

- TR-004.3: **Optimization Settings**
  - Optimization level (size, speed, balanced)
  - Inline threshold
  - Unroll limits
  - Vectorization preferences

- TR-004.4: **Safety Settings**
  - Enable/disable hardware bounds checking
  - Enable/disable software bounds checking
  - Stack overflow detection method
  - Trap handling strategy

### TR-005: Verification Infrastructure
**Priority:** SHOULD HAVE (MUST HAVE for safety-critical)

**Requirements:**
- TR-005.1: **SMT Solver Integration**
  - Z3 for translation validation
  - Support for bit-vector reasoning
  - Timeout and resource limits

- TR-005.2: **Proof Assistant Integration**
  - Coq for mechanized proofs
  - Lean 4 as alternative
  - Export proofs in standard formats

- TR-005.3: **Fuzzing Integration**
  - OSS-Fuzz for continuous fuzzing
  - Differential testing against other runtimes
  - Property-based testing (QuickCheck-style)

---

## 6. Constraints and Assumptions

### Constraints

**C-001: WebAssembly Limitations**
- Only WebAssembly Component Model MVP features
- No dynamic module loading (all components known at synthesis time)
- No JIT compilation (AOT only)

**C-002: Target Limitations**
- ARM Cortex-M: M3 and above (ARMv7-M minimum)
- RISC-V: RV32IMAC minimum (RV32GC or RV64GC preferred)
- Minimum 64KB RAM, 256KB flash
- No operating system dependency (bare-metal and RTOS)

**C-003: Development Constraints**
- Written in Rust (stable channel)
- MIT/Apache-2.0 dual licensing
- Open source development model

### Assumptions

**A-001: Component Composition**
- All component dependencies known at synthesis time
- Components follow WebAssembly Component Model specification
- WIT interfaces correctly describe component contracts

**A-002: Target Environment**
- Hardware supports basic memory protection (MPU/PMP preferred)
- Adequate flash/RAM for synthesized code
- Standard C runtime available (minimal: newlib-nano)

**A-003: Verification**
- SMT solvers (Z3) available in development environment
- Proof assistants (Coq/Lean) available for certification work
- Sufficient compute resources for verification (may be slow)

**A-004: Performance Expectations**
- 80% of native performance acceptable for most use cases
- Code size overhead <20% acceptable
- Compilation time can be minutes (not seconds) for full verification

---

## 7. Success Criteria

### Phase 1: Prototype (Months 1-3)
- ✓ Parse WebAssembly Component Model binaries
- ✓ Generate working C code via w2c2 integration
- ✓ Achieve >70% native performance on Cortex-M4
- ✓ Demonstrate multi-component composition
- ✓ Run on at least one embedded target (Nordic nRF52, STM32)

### Phase 2: Optimization (Months 4-6)
- ✓ ISLE-based synthesis rules for ARM Cortex-M
- ✓ Hardware-assisted bounds checking (MPU)
- ✓ Achieve ≥80% native performance
- ✓ XIP support for flash execution
- ✓ Cross-component inlining and optimization

### Phase 3: Verification (Months 7-9)
- ✓ SMT-based translation validation working
- ✓ VeriISLE-style rule verification for key synthesis rules
- ✓ Mechanized semantics for subset of WebAssembly in Coq
- ✓ Formal proof of memory safety for synthesized code

### Phase 4: RISC-V Support (Months 10-12)
- ✓ RISC-V backend with ISLE rules
- ✓ PMP-based memory protection
- ✓ Compressed instruction support
- ✓ Achieve ≥80% native performance on RISC-V

### Phase 5: Qualification (Months 13-18)
- ✓ Generate qualification artifacts
- ✓ Pilot safety-critical project (ASIL B or Class A)
- ✓ Formal verification of critical synthesis paths
- ✓ Certification readiness documentation

---

## 8. Out of Scope (for MVP)

### OS-001: Advanced WebAssembly Features
- WebAssembly GC (garbage collection proposal)
- WebAssembly threads (multi-threading)
- WebAssembly exception handling
- WASI Preview 3 async/futures

### OS-002: Additional Targets
- x86/x86-64 (not embedded)
- Xtensa (ESP32)
- ARMv8-A (Cortex-A) except for prototyping
- MIPS or other legacy architectures

### OS-003: Runtime Features
- JIT compilation
- Dynamic module loading
- Hot-reloading/OTA updates during execution
- Garbage collection runtime

### OS-004: High-Level Tools
- Source-level debugger
- Visual profiler UI
- IDE plugins (beyond basic LSP)
- Package manager for components

---

## 9. Dependencies

### Critical Dependencies

**D-001: Bytecode Alliance Projects**
- wasmtime (reference for Component Model)
- wasm-tools (parsing, validation)
- wit-bindgen (WIT processing)

**D-002: Compilation Infrastructure**
- Cranelift (ISLE reference, e-graph optimization)
- LLVM (alternative backend)
- Binaryen (optimization passes)

**D-003: Verification Tools**
- Z3 SMT solver
- Coq proof assistant
- egg (equality saturation)

**D-004: Embedded Toolchains**
- ARM GCC / Clang for ARM targets
- RISC-V GCC / Clang for RISC-V targets
- OpenOCD or similar for flashing/debugging

### Optional Dependencies

**D-005: Quality Assurance**
- OSS-Fuzz for continuous fuzzing
- Valgrind for memory checking
- AFL++ for additional fuzzing

**D-006: Benchmarking**
- CoreMark for embedded performance
- PolyBench for compute benchmarks
- Real-world workload suites

---

## 10. Risks and Mitigations

### R-001: Performance Risk
**Risk:** Synthesized code may not achieve 80% native performance
**Impact:** HIGH
**Mitigation:**
- Prototype early with benchmarks
- Profile and optimize hot paths
- Hardware-assisted bounds checking
- SIMD/vector utilization

### R-002: Verification Complexity
**Risk:** Formal verification may be too complex/expensive
**Impact:** MEDIUM
**Mitigation:**
- Start with translation validation (lighter weight)
- Incremental verification (verify critical paths first)
- Leverage existing work (VeriISLE, CompCert)
- Consider hybrid approach (formal + extensive testing)

### R-003: Safety Qualification
**Risk:** Regulatory acceptance of WebAssembly uncertain
**Impact:** HIGH
**Mitigation:**
- Engage with standards bodies early
- Pilot projects with certification consultants
- Build on precedent (qualified compilers like CompCert)
- Generate comprehensive qualification artifacts

### R-004: Resource Constraints
**Risk:** Limited development resources for ambitious project
**Impact:** MEDIUM
**Mitigation:**
- Phased approach with clear milestones
- Leverage existing open-source components
- Community engagement and contributions
- Focus on MVP features first

### R-005: Toolchain Compatibility
**Risk:** Integration with existing embedded toolchains challenging
**Impact:** MEDIUM
**Mitigation:**
- Standard output formats (ELF, HEX, BIN)
- Compatible with GCC/Clang workflows
- Clear documentation and examples
- Test with popular development boards

---

## 11. Acceptance Criteria

### AC-001: Functional Completeness
- [ ] All MUST HAVE functional requirements implemented
- [ ] ≥80% of SHOULD HAVE functional requirements implemented
- [ ] Comprehensive test suite with >90% code coverage

### AC-002: Performance Targets
- [ ] ≥80% native performance on Cortex-M7
- [ ] ≥80% native performance on RISC-V RV32GC
- [ ] <20% code size overhead
- [ ] <100ms startup time

### AC-003: Correctness
- [ ] Pass WebAssembly Component Model test suite
- [ ] Zero known correctness bugs
- [ ] Formal verification of critical synthesis rules
- [ ] Translation validation passing for all test cases

### AC-004: Safety
- [ ] Memory bounds checking verified
- [ ] Control-flow integrity maintained
- [ ] Component isolation proven
- [ ] Qualification artifacts generated

### AC-005: Usability
- [ ] Documentation complete
- [ ] Examples for common use cases
- [ ] Clear error messages
- [ ] Integration with standard toolchains working

---

## 12. References

### Standards
- WebAssembly Component Model: https://github.com/WebAssembly/component-model
- ISO 26262 (Automotive)
- IEC 62304 (Medical Devices)
- DO-178C (Avionics)

### Research Papers
- Crocus (ASPLOS 2024): Lightweight WebAssembly Verification
- VeriISLE (CMU 2023): Verifying Instruction Selection
- CompCert: Verified C Compiler
- Vericert: Verified High-Level Synthesis

### Tools and Frameworks
- Cranelift: https://cranelift.dev/
- WAMR: https://github.com/bytecodealliance/wasm-micro-runtime
- egg: https://egraphs-good.github.io/
- Z3: https://github.com/Z3Prover/z3

### Related Projects
- pulseengine/loom: Initial WebAssembly optimizations (reference)
- Bytecode Alliance: WebAssembly ecosystem
- Rust Embedded Working Group

---

**Document Status:** Draft v0.1
**Next Review:** After architecture design
**Approval Required:** Technical Lead, Product Owner
