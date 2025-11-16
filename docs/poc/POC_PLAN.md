# Synth Proof-of-Concept Implementation Plan

**Project:** Synth - WebAssembly Component Synthesizer PoC
**Version:** 0.1.0
**Last Updated:** 2025-11-16
**Target Completion:** 3 months
**Status:** Planning

---

## 1. PoC Objectives

### 1.1 Primary Goals

**G-001: Demonstrate Feasibility**
- Prove WebAssembly Component synthesis for embedded targets is viable
- Achieve ≥70% native performance (target: 80%)
- Generate working code for ARM Cortex-M4

**G-002: Validate Architecture**
- Test key architectural decisions (e-graphs, ISLE, MPU mapping)
- Identify implementation challenges early
- Refine architecture based on learnings

**G-003: Create Foundation**
- Build core infrastructure reusable for production
- Establish development workflow and tooling
- Create baseline for future enhancements

### 1.2 Success Criteria

- [ ] Synthesize simple WebAssembly component to ARM Cortex-M4 code
- [ ] Run synthesized code on physical hardware (STM32F4 or Nordic nRF52)
- [ ] Achieve ≥70% of native C performance on CoreMark benchmark
- [ ] Demonstrate MPU-based memory isolation
- [ ] Generate working XIP binary
- [ ] Complete in ≤3 months with 1-2 developers

### 1.3 Scope Limitations

**In Scope:**
- Single component (not multi-component composition)
- ARM Cortex-M4F target only
- Basic optimization (no advanced e-graph yet)
- Simple w2c2-based transpilation approach
- MPU configuration for memory isolation
- CoreMark and simple benchmarks

**Out of Scope:**
- Multi-component composition
- RISC-V target
- Advanced formal verification (translation validation only)
- SIMD optimization
- Full ISLE implementation
- Safety certification artifacts

---

## 2. Technical Approach

### 2.1 Phase 1 Strategy: Hybrid Approach

**Rationale:** Start with proven technologies, layer in custom synthesis incrementally

**Architecture:**

```
WebAssembly Component
    ↓
[1] Parse with wasm-tools (validate component structure)
    ↓
[2] Transpile to C with w2c2 (proven approach)
    ↓
[3] Analyze C code for optimization opportunities
    ↓
[4] Apply synthesis transformations
    ↓
[5] Compile with ARM GCC (proven toolchain)
    ↓
[6] Generate MPU configuration code
    ↓
[7] Link and create XIP binary
    ↓
ARM Cortex-M4 Native Binary
```

**Why This Approach:**
- **Fast time-to-result:** Leverage w2c2 (proven, ~93% native performance)
- **Low risk:** w2c2 already works, we enhance rather than build from scratch
- **Incremental complexity:** Add custom synthesis on top of working baseline
- **Clear comparison:** Can benchmark w2c2 baseline vs synthesized code

### 2.2 Technology Stack

**WebAssembly Tooling:**
- `wasm-tools` (Bytecode Alliance) - Component parsing/validation
- `wit-parser` - WIT interface processing
- `w2c2` - Initial transpilation to C

**Synthesis/Optimization:**
- Custom Rust code for analysis and transformation
- `clang` or `arm-none-eabi-gcc` for final compilation
- `wasm-opt` (Binaryen) for pre-optimization

**Target Hardware:**
- STM32F407 Discovery Board (Cortex-M4F, 192KB RAM, 1MB Flash, MPU)
  - OR -
- Nordic nRF52840 DK (Cortex-M4F, 256KB RAM, 1MB Flash, MPU)

**Development Tools:**
- Rust (stable) for synthesizer implementation
- OpenOCD for flashing/debugging
- Segger J-Link (optional, better debugging)
- Logic analyzer / oscilloscope for profiling

---

## 3. Implementation Phases

### Phase 1: Foundation (Weeks 1-2)

#### Week 1: Project Setup & Tool Integration

**Tasks:**

**1.1 Repository Setup**
- [ ] Initialize Git repository
- [ ] Set up Cargo workspace structure
- [ ] Configure CI/CD (GitHub Actions)
  - Rust fmt/clippy checks
  - Unit tests
  - Integration tests

**1.2 Component Parser**
- [ ] Integrate `wasm-tools` for parsing
- [ ] Create ComponentAST representation
- [ ] Implement basic validation
- [ ] Write tests with sample components

**1.3 w2c2 Integration**
- [ ] Build w2c2 from source
- [ ] Create Rust wrapper for w2c2 invocation
- [ ] Test transpilation of simple Wasm modules
- [ ] Verify generated C code compiles

**Deliverables:**
- Working project structure
- Component parser parsing valid components
- w2c2 generating C code from WebAssembly

**Success Metrics:**
- All CI checks passing
- Parse official WebAssembly Component examples
- w2c2 transpile simple components successfully

#### Week 2: Baseline Compilation Pipeline

**Tasks:**

**2.1 ARM Toolchain Integration**
- [ ] Set up `arm-none-eabi-gcc` toolchain
- [ ] Create linker scripts for target hardware (STM32F407 or nRF52840)
- [ ] Implement build script (Cargo build.rs or Makefile)
- [ ] Test compilation of w2c2-generated C code

**2.2 Hardware Bring-Up**
- [ ] Set up development board
- [ ] Install OpenOCD and configure for target
- [ ] Flash simple "hello world" (blink LED)
- [ ] Set up serial console for printf debugging

**2.3 Runtime Library**
- [ ] Implement minimal WASM runtime for w2c2 output
  - Memory management (linear memory)
  - Trap handling
  - System integration (UART for printf)
- [ ] Port to target RTOS if needed (FreeRTOS or bare-metal)

**Deliverables:**
- End-to-end compilation: WebAssembly → C → ARM binary
- Binary running on physical hardware
- Debug output working (UART/RTT)

**Success Metrics:**
- Flash and run simple WebAssembly on hardware
- Printf/LED blink working
- No crashes, stable execution

---

### Phase 2: Optimization & MPU (Weeks 3-5)

#### Week 3: Memory Layout Analysis

**Tasks:**

**3.1 Memory Analyzer**
- [ ] Implement analysis of w2c2-generated C code
  - Identify linear memory allocations
  - Track memory access patterns
  - Detect constant memory regions
- [ ] Build memory layout optimizer
  - Optimal placement for XIP
  - Alignment for MPU (power-of-2 sizes)

**3.2 MPU Mapper**
- [ ] Implement MPU region allocator
  - Map WebAssembly linear memory to MPU regions
  - Configure permissions (RO/RW/RWX)
  - Handle subregions if needed
- [ ] Generate MPU configuration code
  - Initialize MPU regions at startup
  - Enable MPU and fault handlers

**3.3 Bounds Check Optimization**
- [ ] Analyze w2c2 bounds checks
- [ ] Identify checks covered by MPU
- [ ] Generate code to disable redundant software checks
- [ ] Implement fault handler for MPU violations

**Deliverables:**
- Memory layout optimizer working
- MPU configuration generated
- Bounds checks optimized

**Success Metrics:**
- MPU successfully isolates linear memory
- MPU fault on out-of-bounds access
- Reduced number of software bounds checks

#### Week 4: XIP Binary Generation

**Tasks:**

**4.1 XIP-Capable Code Generation**
- [ ] Modify compilation for position-independent code
  - Ensure constants in flash
  - Minimize relocations
  - Use indirect function calls via tables

**4.2 Flash Layout Optimization**
- [ ] Organize sections for XIP
  - .text in flash (RO, executable)
  - .rodata in flash (RO)
  - .data initial values in flash, copy to RAM
  - .bss in RAM (zero-initialized)

**4.3 Startup Code**
- [ ] Implement efficient startup
  - Minimal .data copying
  - .bss zeroing
  - MPU initialization
  - Jump to main

**Deliverables:**
- XIP binary running from flash
- Minimal RAM usage
- Fast startup time

**Success Metrics:**
- Binary executes directly from flash
- RAM usage <50% of available
- Startup time <10ms

#### Week 5: Performance Optimization

**Tasks:**

**5.1 Baseline Benchmarking**
- [ ] Port CoreMark to WebAssembly
- [ ] Compile and run via synthesis pipeline
- [ ] Measure performance vs native ARM compilation
- [ ] Profile hot spots (logic analyzer / cycle counters)

**5.2 Targeted Optimizations**
- [ ] Identify performance bottlenecks
  - Excessive bounds checks
  - Suboptimal instruction selection
  - Register spilling
- [ ] Apply manual optimizations to w2c2 output
  - Inline critical functions
  - Optimize memory access patterns
  - Use ARM-specific instructions

**5.3 Compiler Optimization Tuning**
- [ ] Experiment with GCC flags
  - `-O2`, `-O3`, `-Os`, `-Ofast`
  - `-flto` (link-time optimization)
  - ARM-specific: `-mcpu=cortex-m4`, `-mfloat-abi=hard`
- [ ] Measure impact of each optimization

**Deliverables:**
- Benchmarking framework
- Performance data (baseline and optimized)
- Optimization guide

**Success Metrics:**
- Achieve ≥70% of native performance on CoreMark
- Identify and document optimization opportunities
- Establish performance improvement roadmap

---

### Phase 3: Synthesis Enhancements (Weeks 6-8)

#### Week 6: Custom Synthesis Rules

**Tasks:**

**6.1 Pattern Matching Infrastructure**
- [ ] Implement AST pattern matching for C code
  - Identify common idioms in w2c2 output
  - Build pattern library (loops, memory accesses, calls)

**6.2 Synthesis Rule Engine (Simplified ISLE)**
- [ ] Design simple rule-based transformation system
  - Pattern → replacement pairs
  - Condition checking
  - Priority handling
- [ ] Implement rule application engine
  - Single-pass or iterative
  - Conflict resolution

**6.3 Initial Synthesis Rules**
- [ ] Implement ARM-specific optimizations
  - Replace multiply-by-power-of-2 with shifts
  - Fuse adds with shifted operands
  - Use conditional execution where beneficial
- [ ] Implement WebAssembly-specific optimizations
  - Optimize common Wasm patterns
  - Specialize for known memory layouts

**Deliverables:**
- Rule-based transformation engine
- Initial set of synthesis rules
- Demonstrated performance improvement

**Success Metrics:**
- ≥5% performance improvement from synthesis rules
- Rules provably correct (manual verification)
- No regressions in functionality

#### Week 7: Call Graph Optimization

**Tasks:**

**7.1 Call Graph Analysis**
- [ ] Build call graph from w2c2 C code
  - Direct calls (statically known)
  - Indirect calls (function pointers)
  - Call frequency estimation

**7.2 Devirtualization**
- [ ] Identify indirect calls with known targets
  - Single implementation (can always devirtualize)
  - Limited implementations (specialize)
- [ ] Transform indirect → direct calls
- [ ] Measure performance impact

**7.3 Inlining Optimization**
- [ ] Implement inlining heuristics
  - Small functions (< threshold)
  - Functions called once
  - Hot functions in critical path
- [ ] Apply aggressive inlining with LTO
- [ ] Measure code size vs performance trade-off

**Deliverables:**
- Call graph analyzer
- Devirtualization pass
- Inlining optimizer

**Success Metrics:**
- ≥10% reduction in indirect calls
- ≥3% performance improvement from devirtualization
- Acceptable code size increase (<10%)

#### Week 8: Translation Validation Prototype

**Tasks:**

**8.1 SMT Solver Integration**
- [ ] Integrate Z3 Rust bindings
- [ ] Implement basic SMT query generation
  - Encode simple arithmetic operations
  - Encode memory operations
  - Encode control flow

**8.2 Semantics Encoding**
- [ ] Define WebAssembly semantics for subset
  - Integer arithmetic (i32 only for PoC)
  - Memory load/store
  - Control flow (if, loop, br)
- [ ] Define ARM semantics for same subset
  - ARM instructions (add, sub, ldr, str, etc.)
  - Register state
  - Memory state

**8.3 Validation Queries**
- [ ] Generate equivalence queries
  - For each synthesized function
  - Compare WebAssembly semantics vs ARM semantics
  - Check: ∀ inputs, outputs equivalent
- [ ] Run validation on synthesized code
- [ ] Report results (UNSAT = correct, SAT = bug + counterexample)

**Deliverables:**
- SMT-based translation validator
- Validation of PoC synthesized code
- Bug reports if validation fails

**Success Metrics:**
- Successfully encode subset of WebAssembly and ARM semantics
- Validate at least one synthesized function
- Detect intentional bug (negative test)

---

### Phase 4: Evaluation & Documentation (Weeks 9-10)

#### Week 9: Comprehensive Benchmarking

**Tasks:**

**9.1 Benchmark Suite**
- [ ] CoreMark (standard embedded benchmark)
- [ ] Dhrystone (integer performance)
- [ ] Custom WebAssembly benchmarks
  - Memory-intensive operations
  - Compute-intensive operations
  - Control-flow-heavy code

**9.2 Comparative Analysis**
- [ ] Native ARM C compilation (baseline)
- [ ] w2c2 baseline (unoptimized synthesis)
- [ ] Synth PoC (optimized synthesis)
- [ ] WAMR AOT (if time permits)

**9.3 Metrics Collection**
- [ ] Performance: Cycles, wall-clock time, CoreMark score
- [ ] Code size: Text, data, BSS, total flash usage
- [ ] Memory: RAM usage, stack depth
- [ ] Compilation time: Synthesis time vs native compilation

**Deliverables:**
- Comprehensive benchmark results
- Performance comparison tables
- Graphs and visualizations

**Success Metrics:**
- ≥70% native performance achieved
- <20% code size overhead
- Clear performance improvement story

#### Week 10: Documentation & Demo

**Tasks:**

**10.1 Technical Documentation**
- [ ] Architecture documentation (actual implementation)
- [ ] API documentation (Rustdoc)
- [ ] Developer guide (how to extend)
- [ ] Build and usage instructions

**10.2 User Documentation**
- [ ] Getting started guide
- [ ] Example projects
  - Simple "hello world"
  - CoreMark benchmark
  - Real application (e.g., LED controller)
- [ ] Troubleshooting guide

**10.3 Demo Preparation**
- [ ] Create demo video/presentation
- [ ] Prepare live demo on hardware
  - Show synthesis process
  - Flash and run on board
  - Demonstrate MPU isolation
  - Show performance comparison

**10.4 PoC Report**
- [ ] Executive summary
- [ ] Technical achievements
- [ ] Performance results
- [ ] Lessons learned
- [ ] Roadmap for production version

**Deliverables:**
- Complete documentation set
- Demo materials
- PoC final report

**Success Metrics:**
- Documentation clear and comprehensive
- Demo runs smoothly
- PoC report identifies path forward

---

## 4. Detailed Technical Tasks

### 4.1 Component Parser Implementation

**File:** `synth/src/frontend/parser.rs`

```rust
use wasm_tools::Parser;
use wit_parser::Interface;

pub struct ComponentParser {
    parser: Parser,
}

impl ComponentParser {
    pub fn parse_file(&self, path: &Path) -> Result<ComponentAST> {
        // 1. Read WebAssembly binary
        // 2. Parse with wasm-tools
        // 3. Validate component structure
        // 4. Extract WIT interfaces
        // 5. Build ComponentAST
    }
}

pub struct ComponentAST {
    pub modules: Vec<CoreModule>,
    pub components: Vec<Component>,
    pub interfaces: HashMap<String, WITInterface>,
}
```

**Tests:**
- Parse valid WebAssembly Component
- Reject invalid components
- Handle malformed binaries gracefully

### 4.2 w2c2 Integration

**File:** `synth/src/transpiler/w2c2.rs`

```rust
use std::process::Command;

pub struct W2C2Transpiler {
    w2c2_path: PathBuf,
}

impl W2C2Transpiler {
    pub fn transpile(&self, wasm: &[u8]) -> Result<String> {
        // 1. Write WASM to temp file
        // 2. Invoke w2c2: w2c2 input.wasm output.c
        // 3. Read generated C code
        // 4. Return as string
    }
}
```

**Tests:**
- Transpile simple Wasm module
- Handle w2c2 errors
- Verify output compiles

### 4.3 MPU Configuration Generator

**File:** `synth/src/hardware/mpu.rs`

```rust
pub struct MPURegion {
    pub base_address: u32,
    pub size: MPUSize,  // Must be power-of-2
    pub permissions: MPUPermissions,
    pub subregions: Option<u8>,
}

pub struct MPUMapper {
    pub available_regions: u8,  // Usually 8
}

impl MPUMapper {
    pub fn allocate_regions(&self, memories: &[Memory]) -> Result<Vec<MPURegion>> {
        // 1. Align memories to power-of-2 boundaries
        // 2. Allocate MPU regions
        // 3. Configure permissions
        // 4. Return MPU configuration
    }

    pub fn generate_config_code(&self, regions: &[MPURegion]) -> String {
        // Generate C code to configure MPU
    }
}
```

**Generated Code Example:**
```c
void mpu_init(void) {
    MPU->CTRL = 0;  // Disable MPU during config

    // Region 0: Linear Memory (64KB, RW, User accessible)
    MPU->RNR = 0;
    MPU->RBAR = 0x20000000;
    MPU->RASR = (SIZE_64KB | RW | USER | ENABLE);

    // Region 1: Stack (16KB, RW, User accessible)
    MPU->RNR = 1;
    MPU->RBAR = 0x20010000;
    MPU->RASR = (SIZE_16KB | RW | USER | ENABLE);

    MPU->CTRL = MPU_ENABLE | MPU_PRIVDEFENA;  // Enable MPU
}
```

### 4.4 XIP Binary Layout

**Linker Script:** `synth/templates/cortex-m4.ld`

```ld
MEMORY
{
    FLASH (rx)  : ORIGIN = 0x08000000, LENGTH = 1024K
    RAM (rwx)   : ORIGIN = 0x20000000, LENGTH = 192K
}

SECTIONS
{
    .text : {
        KEEP(*(.vector_table))
        *(.text*)
        *(.rodata*)
    } > FLASH

    .data : {
        _sdata = .;
        *(.data*)
        _edata = .;
    } > RAM AT > FLASH

    .bss : {
        _sbss = .;
        *(.bss*)
        *(COMMON)
        _ebss = .;
    } > RAM

    /* Linear memory in RAM */
    .wasm_memory (NOLOAD) : ALIGN(0x10000) {
        _wasm_memory_start = .;
        . += 0x10000;  /* 64KB */
        _wasm_memory_end = .;
    } > RAM
}
```

### 4.5 Translation Validation

**File:** `synth/src/verification/validator.rs`

```rust
use z3::{Context, Solver};

pub struct TranslationValidator {
    context: Context,
}

impl TranslationValidator {
    pub fn validate_function(&self, wasm_fn: &WasmFunction, arm_fn: &ARMFunction) -> Result<ValidationResult> {
        let solver = Solver::new(&self.context);

        // 1. Encode WebAssembly semantics
        let wasm_formula = self.encode_wasm_semantics(wasm_fn);

        // 2. Encode ARM semantics
        let arm_formula = self.encode_arm_semantics(arm_fn);

        // 3. Query: wasm_formula ≡ arm_formula
        solver.assert(&wasm_formula._eq(&arm_formula).not());

        // 4. Check satisfiability
        match solver.check() {
            SatResult::Unsat => Ok(ValidationResult::Correct),
            SatResult::Sat => {
                let model = solver.get_model();
                Ok(ValidationResult::Incorrect(model))
            }
            SatResult::Unknown => Err(Error::VerificationTimeout),
        }
    }
}
```

---

## 5. Hardware Setup

### 5.1 Recommended Development Board

**Option 1: STM32F407 Discovery**
- **Pros:**
  - Cheap (~$20)
  - Excellent documentation
  - Large community
  - 192KB RAM, 1MB Flash
  - 8 MPU regions

- **Cons:**
  - Older board
  - Micro-USB (not USB-C)

**Option 2: Nordic nRF52840 DK**
- **Pros:**
  - Modern board
  - Bluetooth (bonus feature)
  - 256KB RAM, 1MB Flash
  - 8 MPU regions
  - Excellent Rust support

- **Cons:**
  - More expensive (~$50)

**Recommendation: Nordic nRF52840 DK** (more RAM, better tooling)

### 5.2 Development Tools

**Required:**
- OpenOCD (open-source JTAG/SWD)
- ARM GCC toolchain (arm-none-eabi-gcc)
- Serial terminal (minicom, screen, or PuTTY)

**Optional but Recommended:**
- Segger J-Link (faster, better debugging)
- Logic analyzer (Saleae, cheap clones)
- Oscilloscope for performance analysis

### 5.3 Software Environment

**Host OS:** Linux (Ubuntu/Debian recommended), macOS, or Windows with WSL2

**Required Software:**
```bash
# Rust toolchain
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
rustup target add thumbv7em-none-eabihf

# ARM GCC toolchain
sudo apt install gcc-arm-none-eabi binutils-arm-none-eabi

# OpenOCD
sudo apt install openocd

# Serial terminal
sudo apt install minicom

# Optional: Segger J-Link
# Download from segger.com
```

---

## 6. Success Metrics

### 6.1 Quantitative Metrics

| Metric | Target | Stretch Goal |
|--------|--------|--------------|
| **Performance** | ≥70% of native | ≥80% of native |
| **Code Size** | <130% of native | <120% of native |
| **Compilation Time** | <30 seconds | <10 seconds |
| **RAM Usage** | <80% of available | <60% of available |
| **MPU Overhead** | <10% vs no bounds check | <5% vs no bounds check |

### 6.2 Qualitative Metrics

- [ ] Code runs stably on hardware (no crashes after 1 hour)
- [ ] MPU successfully catches out-of-bounds access
- [ ] XIP binary boots and runs from flash
- [ ] Synthesis pipeline handles real WebAssembly components
- [ ] Translation validator detects intentional bug

### 6.3 Comparison Benchmarks

**CoreMark Scores (expected):**
- Native ARM C: ~250 CoreMark/MHz
- Synth PoC (target): ≥175 CoreMark/MHz (70%)
- Synth PoC (stretch): ≥200 CoreMark/MHz (80%)

**Code Size (CoreMark):**
- Native ARM C: ~10KB
- Synth PoC (target): <13KB
- Synth PoC (stretch): <12KB

---

## 7. Risk Management

### 7.1 Technical Risks

**R-001: Performance Target Not Met**
- **Probability:** Medium
- **Impact:** High
- **Mitigation:**
  - Start with w2c2 (proven baseline ~93%)
  - Profile early and often
  - Focus optimization on hot paths
  - Acceptable fallback: Achieve 70% and document path to 80%

**R-002: MPU Complexity**
- **Probability:** Medium
- **Impact:** Medium
- **Mitigation:**
  - Thorough ARM MPU documentation review
  - Start with simple single-region mapping
  - Test MPU configuration standalone
  - Fallback: Software bounds checks only

**R-003: w2c2 Integration Issues**
- **Probability:** Low
- **Impact:** High
- **Mitigation:**
  - Test w2c2 standalone first
  - Have wasm2c as backup option
  - Consider direct LLVM backend as alternative

**R-004: Hardware Availability**
- **Probability:** Low
- **Impact:** Medium
- **Mitigation:**
  - Order hardware early (week 0)
  - Have backup board option
  - QEMU emulation as last resort (less realistic)

### 7.2 Schedule Risks

**R-005: Scope Creep**
- **Probability:** High
- **Impact:** Medium
- **Mitigation:**
  - Strict adherence to PoC scope
  - Document "nice-to-have" for future
  - Weekly scope review

**R-006: Learning Curve**
- **Probability:** Medium
- **Impact:** Medium
- **Mitigation:**
  - Allocate time for learning (embedded, ARM, MPU)
  - Pair programming for knowledge transfer
  - Reference implementations (WAMR, Cranelift)

---

## 8. Deliverables

### 8.1 Code Deliverables

- [ ] Synth PoC source code (Rust)
  - Component parser
  - w2c2 integration
  - MPU mapper
  - Synthesis engine (basic)
  - Translation validator (prototype)

- [ ] Example projects
  - Hello World WebAssembly component
  - CoreMark benchmark
  - Simple application (LED blink via WebAssembly)

- [ ] Test suite
  - Unit tests (>80% coverage)
  - Integration tests
  - Hardware tests (automated via OpenOCD)

### 8.2 Documentation Deliverables

- [ ] PoC Architecture Document (actual implementation)
- [ ] Getting Started Guide
- [ ] Developer Guide
- [ ] API Documentation (Rustdoc)
- [ ] Benchmark Results Report
- [ ] Lessons Learned Document
- [ ] Roadmap to Production

### 8.3 Demonstration Deliverables

- [ ] Demo video (5-10 minutes)
  - Synthesis process walkthrough
  - Flashing and running on hardware
  - Performance comparison
  - MPU isolation demonstration

- [ ] Live demo setup
  - Hardware with synthesized code running
  - Serial console showing output
  - Performance metrics displayed

- [ ] Presentation slides
  - Problem statement
  - Solution approach
  - Results
  - Next steps

---

## 9. Timeline

```
Week 1-2:   Foundation (Parser, w2c2, ARM toolchain)
Week 3-5:   Optimization (MPU, XIP, Performance)
Week 6-8:   Synthesis (Rules, Call graph, Validation)
Week 9-10:  Evaluation (Benchmarks, Documentation, Demo)

Milestones:
- End of Week 2:  Code running on hardware
- End of Week 5:  ≥60% native performance
- End of Week 8:  ≥70% native performance, validation working
- End of Week 10: Complete PoC with documentation
```

### 9.1 Gantt Chart

```
Task                      | W1 | W2 | W3 | W4 | W5 | W6 | W7 | W8 | W9 | W10 |
--------------------------|----|----|----|----|----|----|----|----|----|----|
Project Setup             |████|    |    |    |    |    |    |    |    |    |
Component Parser          |████|    |    |    |    |    |    |    |    |    |
w2c2 Integration          |████|████|    |    |    |    |    |    |    |    |
ARM Toolchain             |    |████|    |    |    |    |    |    |    |    |
Hardware Bring-Up         |    |████|    |    |    |    |    |    |    |    |
Memory Analysis           |    |    |████|    |    |    |    |    |    |    |
MPU Mapper                |    |    |████|████|    |    |    |    |    |    |
XIP Binary                |    |    |    |████|    |    |    |    |    |    |
Performance Optimization  |    |    |    |    |████|    |    |    |    |    |
Synthesis Rules           |    |    |    |    |    |████|    |    |    |    |
Call Graph Opt            |    |    |    |    |    |    |████|    |    |    |
Translation Validation    |    |    |    |    |    |    |    |████|    |    |
Benchmarking              |    |    |    |    |    |    |    |    |████|    |
Documentation & Demo      |    |    |    |    |    |    |    |    |    |████|
```

---

## 10. Budget & Resources

### 10.1 Hardware Budget

| Item | Quantity | Unit Cost | Total |
|------|----------|-----------|-------|
| Nordic nRF52840 DK | 2 | $50 | $100 |
| USB cables / accessories | - | - | $20 |
| **Total Hardware** | | | **$120** |

### 10.2 Software/Services Budget

| Item | Cost |
|------|------|
| GitHub (free tier) | $0 |
| CI/CD (GitHub Actions free tier) | $0 |
| Development tools (all open-source) | $0 |
| **Total Software** | **$0** |

### 10.3 Personnel

**Assumption:** 1-2 developers, 3 months

**Required Skills:**
- Rust programming (intermediate)
- Embedded systems (basic)
- WebAssembly (basic, can learn)
- ARM Cortex-M (basic, can learn)

**Time Commitment:**
- Lead developer: 100% (full-time)
- Secondary developer (optional): 50% (part-time)

---

## 11. Next Steps After PoC

### 11.1 If PoC Succeeds (≥70% performance)

**Immediate:**
- Refine architecture based on learnings
- Plan production implementation
- Seek funding/resources for full project

**Short-term (3-6 months):**
- Implement full ISLE-based synthesis
- Add RISC-V backend
- E-graph optimization integration
- Multi-component composition

**Medium-term (6-12 months):**
- Advanced formal verification
- Safety certification preparation
- Community building
- Industrial pilot projects

### 11.2 If PoC Partially Succeeds (50-70% performance)

**Analysis:**
- Identify bottlenecks
- Determine if fundamental or implementation issue
- Decide: Refine approach or pivot

**Options:**
- Focus on specific use cases where performance acceptable
- Invest in deeper optimization
- Explore alternative approaches (LLVM backend, etc.)

### 11.3 If PoC Fails (<50% performance)

**Retrospective:**
- Document what was learned
- Identify root causes
- Determine viability of overall approach

**Pivot Options:**
- Pure LLVM-based approach (slower compile, better performance)
- Target different platforms (where WebAssembly overhead less critical)
- Focus on safety/certification instead of performance

---

## 12. Conclusion

This PoC plan provides a structured, achievable path to demonstrating WebAssembly Component synthesis for embedded systems. By starting with proven technologies (w2c2) and incrementally adding custom synthesis, we minimize risk while building toward the full vision.

**Key Success Factors:**
- Realistic scope (single component, one target)
- Proven baseline (w2c2 ~93% performance gives margin)
- Incremental complexity (working system enhanced, not built from scratch)
- Clear metrics (≥70% performance, measurable)
- Hardware validation (real embedded board, not just simulation)

**Expected Outcome:**
A working demonstrator of WebAssembly Component synthesis achieving ≥70% native performance on ARM Cortex-M4, with clear path to production implementation achieving ≥80% performance and safety certification.

---

**Document Status:** Draft v0.1
**Approval Required:** Technical Lead
**Start Date:** TBD
**Target Completion:** TBD + 10 weeks
