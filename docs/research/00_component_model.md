# WebAssembly Component Model Research

**Status:** Complete
**Last Updated:** 2025-11-16
**Focus:** Component Model specifications, composition, memory models, optimization opportunities

---

## Executive Summary

The WebAssembly Component Model (Phase 2/3 standardization) enables modular, language-neutral component composition with strong isolation guarantees. Key findings for embedded system synthesis:

- **Multi-memory support** enables hardware-assisted isolation (MPU/MMU)
- **Shared-everything linking** allows aggressive cross-component optimization
- **Canonical ABI** provides structured interface for safe composition
- **Static linking** eliminates runtime overhead for embedded deployments
- **Component isolation** enables provable sandboxing for safety-critical systems

---

## 1. Component Model Specifications

### Current Status (2025)

- **Phase:** 2/3 of W3C standardization process
- **Browser Support:** Not yet (runtime-only: Wasmtime, WAMR)
- **Production Ready:** Yes (Bytecode Alliance implementations)
- **Specification:** https://github.com/WebAssembly/component-model

### Design Principles

1. **Layered Architecture:** Builds atop Core WebAssembly
2. **Immutability & Composition:** Components are immutable code artifacts
3. **Flexible Linking:** Multiple linking styles supported
4. **Acyclic Structure:** No circular dependencies allowed

### Component Structure

**12 Distinct Index Spaces:**
- 5 component-level: functions, values, types, instances, components
- 7 core-level: functions, tables, memories, globals, types, modules, instances

**Binary Format:**
```
Magic bytes:  0x00 0x61 0x73 0x6D (same as core modules)
Version:      0x0d 0x00 (pre-standard)
Layer field:  0x01 0x00 (component) vs 0x00 (core module)
Extension:    .wasm (can contain either)
```

---

## 2. Interface Types and Canonical ABI

### WIT (WebAssembly Interface Types)

**Purpose:** Developer-friendly Interface Description Language (IDL)

**Package Structure:**
```
namespace:package@version
Example: wasi:clocks@1.2.0
```

**Type System:**
- **Primitives:** bool, u32, s32, u64, f32, f64, string
- **Composite:** records, variants, lists, tuples, flags, enums, options, results
- **Resources:** Opaque handles to host objects (owned `0x3f`, borrowed `0x3e`)

**Specification:** https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md

### Canonical ABI

**Core Operations:**
- **Lifting:** Converts Core WebAssembly values → component-level high-level values
- **Lowering:** Transforms high-level values → Core WebAssembly execution

**Runtime State (per component instance):**
- Table structure with free-list algorithm (max 2^28 - 1 elements)
- Backpressure tracking for flow control
- Exclusive access flags for single-threaded contexts
- Resource handle management with ownership/borrow tracking

**Cross-Language Interoperability:**
Components in different languages (Go, C, Rust, Python) communicate directly:
- Standardized value mappings
- Language-neutral calling conventions
- Resource abstractions

**Specification:** https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md

---

## 3. Composition and Linking Mechanisms

### Linking Classification

**Two Primary Axes:**

1. **Memory Sharing:**
   - **Shared-everything:** Modules share memory and table instances
   - **Shared-nothing:** Components have isolated memory spaces

2. **Storage Method:**
   - **Inline:** Embedded child modules in parent binary
   - **Import:** External module references via registry

### Shared-Everything Linking

**Characteristics:**
- Modules share WebAssembly `memory` and `table` instances
- Requires common ABI agreement (e.g., C/C++ ABI from tool-conventions)
- Enables aggressive optimization opportunities

**Variants:**

**Static (Toolchain-level):**
- Fuses modules into single module before runtime
- Invisible to Component Model runtime
- Maximum optimization potential
- Tool: `wasm-ld` (LLVM linker)

**Dynamic (Runtime-level):**
- Keeps modules separate but allows shared compiled machine code
- Similar to shared libraries (e.g., libc.so)
- All modules statically declared before execution
- Enables AOT compilation of entire component graph

**Optimization Opportunities:**
- Cross-module inlining
- Dead code elimination across boundaries
- Constant propagation through imports/exports
- Shared compiled machine code (JIT cache)

### Shared-Nothing Linking

**Characteristics:**
- Components cannot share `memory` or `table` instances
- Communication only through Canonical ABI
- Each module can use different internal ABI
- Strong isolation guarantees

**Benefits:**
- Enhanced security (module isolation)
- Language heterogeneity (no ABI lock-in)
- Compositional reasoning
- Capability-based security

**Trade-offs:**
- Canonical ABI overhead for inter-component calls
- Memory overhead (separate memories per component)
- Less optimization across boundaries

### Composition Mechanisms

**1. Aliases (three targeting modes):**
- **Export aliases:** Extract definitions from instance exports
- **Core export aliases:** Access core module instance exports
- **Outer aliases:** Use de Bruijn indices for enclosing components

**2. Instance Composition:**
- Ad-hoc composition by tupling definitions
- No helper module instantiation required

**3. Tooling:**

**wasm-component-ld (Linker):**
- GitHub: https://github.com/bytecodealliance/wasm-component-ld
- Combines LLVM `wasm-ld` with `wit_component::ComponentEncoder`
- Automatically invoked by `wasm32-wasip2` target in Clang and Rust
- Latest: v0.5.19 (November 2025)

**wac (WebAssembly Composition):**
- GitHub: https://github.com/bytecodealliance/wac
- Declarative language for composing components
- Simple: `wac plug` command
- Complex: WAC language files with `wac compose`

**wasm-tools:**
```bash
# Create component
wasm-tools component new foo.wasm --adapt wasi_snapshot_preview1.wasm -o component.wasm

# Validate
wasm-tools validate component.wasm --features component-model
```

**wit-bindgen (Language Bindings):**
- GitHub: https://github.com/bytecodealliance/wit-bindgen
- Generates language-specific bindings from WIT files
- Languages: Rust, C, C++, C#, Go (TinyGo), MoonBit

---

## 4. Memory Models and Multi-Memory Support

### Multi-Memory Proposal

**Status:** Phase 4 (Standardized in WebAssembly 2.0, 2024)

**Specification:** https://github.com/WebAssembly/multi-memory/blob/main/proposals/multi-memory/Overview.md

**Design:**
- Modules can define/import multiple memories
- Memory index added to all memory-related instructions
- Each memory has separate address space

**Use Cases for Embedded Synthesis:**

1. **Security/Isolation:**
   - Separate public memory (host communication) from private memory
   - MPU/MMU protection regions aligned with memory boundaries
   - Hardware-accelerated bounds checking

2. **Real-Time Systems:**
   - Separate thread-shared from thread-local memory
   - Isolate deterministic from non-deterministic data

3. **Linking/Composition:**
   - Merge modules with multiple memories
   - Preserve memory isolation during static linking

4. **Scaling:**
   - Workaround for 4GB limit before Memory64 availability
   - Multiple 4GB regions for large-memory applications

5. **Persistence:**
   - Separate volatile from persistent memory regions
   - Selective state preservation

6. **Polyfilling:**
   - Emulate proposed features using auxiliary memory
   - GC implementation in user space

### Memory64 Proposal

**Status:** Phase 4 (Standardized November 2024)
**Browser Support:** Firefox 134, Chrome 133

**Specification:** https://github.com/WebAssembly/memory64/blob/main/proposals/memory64/Overview.md

**Capabilities:**
- Extends memory to >2^32 bytes using 64-bit indexes
- **i32 addresses:** 2^16 page limit (4GB)
- **i64 addresses:** 2^48 page limit (256TB)

**Performance Implications:**
- 10-100% performance penalty vs 32-bit mode
- Increased bounds-checking overhead for 64-bit accesses
- Higher memory consumption with 64-bit pointers

**Embedded Considerations:**
- Most embedded systems don't need >4GB
- Stick with 32-bit for Cortex-M and low-end RISC-V
- Consider for high-end embedded (automotive gateways, industrial controllers)

### Component Model Integration

**Key Constraints:**
- Components **may not export memory** (enhances sandboxing)
- Linear-memory-based Canonical ABI
- Configurable memory representations for same abstract value

**Optimization Opportunities:**
- Memory index 0: register-based optimization
- Additional memories: indirect addressing
- Custom sections for optimization hints

**Memory Protection Integration:**

For ARM Cortex-M MPU synthesis:
```
Memory 0: Linear memory (application data) - MPU region 0-N
Memory 1: Stack region - MPU region N+1
Memory 2: Runtime metadata - MPU region N+2 (privileged access)
```

For RISC-V with PMP (Physical Memory Protection):
```
Memory 0: User data (PMP entry 0)
Memory 1: Shared IPC buffer (PMP entry 1)
Memory 2: Persistent storage (PMP entry 2)
```

---

## 5. Optimization Opportunities for Embedded Synthesis

### Static Linking Optimizations

**Dead Code Elimination:**
- Remove unused component exports
- Eliminate unreachable functions across components
- Constant propagation through component boundaries

**Function Inlining:**
- Inline component calls for shared-everything linking
- Eliminate Canonical ABI overhead for static compositions
- Cross-component inlining when memory shared

**Memory Layout Optimization:**
- Merge component memories when isolation not required
- Optimize memory alignment for target architecture
- Minimize memory footprint (critical for embedded)

**Example: Cortex-M3 Target**
```
Before optimization (shared-nothing):
  Component A: 64KB memory
  Component B: 64KB memory
  Component C: 32KB memory
  Total: 160KB

After synthesis (shared-everything + optimization):
  Merged memory: 96KB (dead code eliminated)
  Memory savings: 40%
```

### AOT Compilation for Component Graphs

**Whole-Program AOT:**
- Compile entire component graph before deployment
- Enables cross-component optimization
- Eliminates runtime instantiation overhead
- Predictable performance (no JIT)

**Target-Specific Synthesis:**
- ARM Cortex-M: Thumb-2 instruction selection
- RISC-V: Compressed instruction support (C extension)
- Custom instruction patterns for specific MCUs

**XIP (Execute In Place) Support:**
- Run AOT-compiled components directly from flash/ROM
- Critical for flash-constrained embedded systems
- WAMR XIP support for WebAssembly components

### Memory Protection Hardware Integration

**ARM Cortex-M MPU:**
- Map WebAssembly memories to MPU regions
- Hardware-accelerated bounds checking
- 8-16 programmable regions (depends on Cortex-M variant)

**RISC-V PMP:**
- Physical Memory Protection for memory isolation
- Up to 16 PMP entries (RV32/RV64)
- Granularity: 4-byte minimum on some implementations

**Synthesis Strategy:**
```
1. Analyze component memory usage
2. Allocate MPU/PMP regions per component memory
3. Generate hardware configuration code
4. Synthesize bounds checks using hardware traps
5. Optimize away software bounds checks where hardware provides guarantees
```

### Direct Function Calls

**Optimization:** Replace indirect calls with direct calls when targets statically known

**Component Model Analysis:**
- Whole-program analysis identifies call targets
- Devirtualization for component imports/exports
- Specialize functions for specific component compositions

**Performance Impact:**
- Cortex-M: 3-5 cycles (direct) vs 10-15 cycles (indirect)
- Eliminates branch prediction penalties
- Enables inlining across component boundaries

### SIMD and Vector Extensions

**WebAssembly SIMD:**
- 128-bit vector operations
- Supported on Cortex-M with Helium (ARMv8.1-M)
- RISC-V Vector Extension

**Synthesis Opportunities:**
- Auto-vectorization for component-level operations
- Cross-component SIMD operation fusion
- Target-specific vector instruction selection

### Real-Time Optimizations

**Deterministic Execution:**
- AOT compilation eliminates JIT overhead
- Predictable memory layout
- No garbage collection pauses

**WCET (Worst-Case Execution Time) Analysis:**
- Static component composition enables WCET calculation
- Hardware-accelerated memory protection provides bounded trap costs
- Synthesize for worst-case instead of average-case

---

## 6. Security Boundaries and Isolation

### Component Model Security Guarantees

**Module-Level Isolation:**
- Each component has protected linear memory
- Components cannot export memory (prevents direct memory sharing)
- Capability-based security model

**Resource Management:**
- Resource handles with ownership/borrow tracking
- Lifetime validation for borrowed resources
- Type-safe resource operations

**Control-Flow Integrity:**
- Typed indirect calls
- Protected call stack
- Structured control flow

### Hardware-Assisted Sandboxing

**For Synthesis:**

1. **Analyze component dependencies**
   - Build component dependency graph
   - Identify trust boundaries

2. **Allocate hardware protection**
   - Map components to MPU/PMP regions
   - Configure privilege levels

3. **Synthesize protection checks**
   - Generate hardware configuration code
   - Optimize software checks where hardware provides guarantees

4. **Verify isolation**
   - Formal verification of memory separation
   - Prove no cross-component memory access (without ABI)

**Example: ARM Cortex-M7 with MPU**
```
Component A (untrusted): MPU region 0 (read/write, unprivileged)
Component B (trusted):   MPU region 1 (read/write, privileged)
Shared IPC buffer:       MPU region 2 (read/write, both)
Runtime:                 MPU region 3 (read-only, unprivileged)
```

### WASI Integration

**Capability-Based APIs:**
- Filesystem access with explicitly granted permissions
- Network access control
- Hardware peripheral access (embedded WASI extensions)

**Embedded WASI Extensions (in development):**
- `wasi-i2c`: I²C peripheral access
- `wasi-spi`: SPI peripheral access
- `wasi-gpio`: GPIO control
- `wasi-usb`: USB device access

---

## 7. Future Developments (WASIp3 - Expected 2025)

### Asynchronous Support

**Future Types:**
```wit
future<T> - Represents async operations
stream<T> - Continuous data flows
```

**Composable Concurrency:**
- First-class in Component Model
- Seamless async/sync bridging
- Solves function coloring problem

**Embedded Implications:**
- Event-driven embedded systems
- Async peripheral access (DMA, interrupts)
- RTOS task model integration

### Enhanced Linking

**WASIp3 Goals:**
- Improved component composition
- Better optimization opportunities
- Enhanced security model

---

## 8. Key Resources

### Official Specifications
- Component Model Explainer: https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md
- Canonical ABI: https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md
- WIT Specification: https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md
- Binary Format: https://github.com/WebAssembly/component-model/blob/main/design/mvp/Binary.md
- Linking: https://github.com/WebAssembly/component-model/blob/main/design/mvp/Linking.md
- Multi-Memory: https://github.com/WebAssembly/multi-memory/blob/main/proposals/multi-memory/Overview.md
- Memory64: https://github.com/WebAssembly/memory64/blob/main/proposals/memory64/Overview.md

### Documentation
- Bytecode Alliance Component Model: https://component-model.bytecodealliance.org/
- Wasmtime Documentation: https://docs.wasmtime.dev/

### Tooling
- wasm-component-ld: https://github.com/bytecodealliance/wasm-component-ld
- wac (Composition): https://github.com/bytecodealliance/wac
- wit-bindgen: https://github.com/bytecodealliance/wit-bindgen
- wasm-tools: https://github.com/bytecodealliance/wasm-tools

---

## 9. Synthesis Implications

### For WebAssembly Component Synthesis to Embedded Targets:

1. **Static Component Composition:**
   - All components known at build time
   - Enables whole-program optimization
   - Eliminates runtime overhead

2. **Multi-Memory for Hardware Protection:**
   - Map component memories to MPU/PMP regions
   - Hardware-accelerated isolation
   - Provably correct sandboxing

3. **Shared-Everything for Performance:**
   - Cross-component optimization
   - Minimal Canonical ABI overhead
   - Maximum inlining opportunities

4. **AOT Compilation:**
   - Target-specific code generation
   - XIP support for flash execution
   - Predictable performance

5. **Formal Verification:**
   - Component Model provides structured abstraction
   - Mechanical verification of composition correctness
   - Safety-critical certification path

**Synthesis Pipeline:**
```
WIT Interfaces
    ↓
Component Composition (wac)
    ↓
Memory Layout Analysis
    ↓
Hardware Protection Mapping (MPU/PMP)
    ↓
Optimization (shared-everything linking)
    ↓
Target-Specific Lowering (ISLE)
    ↓
AOT Compilation (Cranelift/LLVM)
    ↓
XIP Binary + Hardware Config
```

---

## 10. Recommendations for Synth Project

### Phase 1: Foundation
- Implement Component Model parser and validator
- Build component dependency analyzer
- Develop memory layout optimizer

### Phase 2: Hardware Mapping
- MPU/PMP region allocator for ARM Cortex-M and RISC-V
- Hardware configuration code generator
- Bounds check optimization (use hardware where possible)

### Phase 3: Optimization
- Shared-everything linking optimizer
- Cross-component inlining
- Dead code elimination

### Phase 4: Synthesis
- Target-specific code generation (ISLE-based)
- XIP binary generation
- Formal verification integration

### Phase 5: Certification
- Safety-critical coding standards compliance
- Qualification artifacts generation
- Formal proofs of isolation and correctness

---

**Document Status:** Complete
**Next Steps:** Integrate with synthesis architecture and PoC implementation plan
