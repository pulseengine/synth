# WebAssembly AOT Compilation and Transpilation Research

**Status:** Complete
**Last Updated:** 2025-11-16
**Focus:** AOT compilation strategies, transpilation to C/native code, optimization, preserving WebAssembly guarantees

---

## Executive Summary

WebAssembly supports multiple approaches for ahead-of-time compilation and transpilation to native code. Key findings for embedded synthesis:

- **wasm2c/w2c2:** Transpile to C (~93-100% native performance, smallest runtime)
- **Cranelift AOT:** Fast compilation (~10x LLVM speed), good performance (~86% native)
- **LLVM AOT:** Slow compilation, excellent performance (~85-90% native)
- **Binaryen wasm-opt:** Post-processing optimizer (10-15% size reduction)
- **Safety preservation:** Requires careful bounds checking and CFI maintenance

---

## 1. AOT Compilation Strategies

### Runtime-Based AOT Compilation

#### Wasmtime (Cranelift Backend)

**Command:**
```bash
wasmtime compile input.wasm -o output.cwasm
```

**Output:** Compiled WebAssembly (".cwasm") files

**Characteristics:**
- Fast compilation (~10x faster than LLVM)
- Good runtime performance (~2% slower than V8, ~14% slower than LLVM)
- Cross-platform with architecture-specific precompilation
- Security: Maintains WebAssembly sandboxing guarantees

**Use Cases:**
- Development workflows (fast iteration)
- Cold-start scenarios (serverless, edge computing)
- JIT-like AOT compilation

**Repository:** https://github.com/bytecodealliance/wasmtime

#### WasmEdge (LLVM Backend)

**Command:**
```bash
wasmedge compile --optimize 2 input.wasm output.so
```

**Characteristics:**
- Default O2 optimization level
- Excellent runtime performance (~85-90% of native)
- Focus on edge computing and AI workloads
- Supports multiple backends (LLVM, Singlepass)

**Use Cases:**
- Production deployments
- AI/ML inference at the edge
- High-performance scenarios

**Repository:** https://github.com/WasmEdge/WasmEdge

#### Wasmer (Multiple Backends)

**Backends:**
1. **LLVM:** Best performance, slow compilation
2. **Cranelift:** Balanced performance/compilation speed
3. **Singlepass:** Fastest compilation, lower performance

**Characteristics:**
- Flexible backend selection
- Cross-compilation support
- Performance: 80-85% of native

**Use Cases:**
- Multi-platform deployments
- Plugin systems
- Embedded runtimes

**Repository:** https://github.com/wasmerio/wasmer

---

## 2. Transpilation to C/C++

### wasm2c (WebAssembly Binary Toolkit)

**Repository:** https://github.com/WebAssembly/wabt

**Functionality:**
Converts WebAssembly binary modules to C source and header files.

**Generated Code Characteristics:**
- Simple, readable C code (mostly C89 subset)
- Full WebAssembly spec implementation:
  - Bounds-checking for memory/table accesses
  - Type-safety for indirect calls
  - Clean trap on stack exhaustion

**Memory Model Implementation:**

```c
typedef struct wasm_rt_memory {
    uint8_t* data;        // Linear memory bytes
    uint32_t pages;       // Current size
    uint32_t page_size;   // Default 65,536
    uint32_t max_pages;   // Maximum size
} wasm_rt_memory_t;
```

**All memory accesses through unified load/store methods guaranteed to stay within sandbox.**

**Performance Optimization:**

`WASM_RT_NO_MEMORY_CHECKS` define disables bounds checks:
- Significant performance gains
- Often faster than WASM runtimes
- Comparable to native code
- **Warning:** Loses sandboxing guarantees

**Segue Optimization:**
- Uses x86 segment registers to store linear memory location
- Reduces overhead by 8.3%
- Eliminates 44.7% of WASM overheads in SPEC CPU 2006

**Use Cases:**
- Embedding WASM in C/C++ applications
- Platforms without WASM runtime support
- Sandboxing C code (compile to WASM, transpile back for safety)
- Zero runtime overhead scenarios
- Negligible startup time requirements

**Example:**

```bash
# Convert WASM to C
wasm2c input.wasm -o output.c

# Compile with GCC
gcc output.c wasm-rt-impl.c -o executable

# With optimizations and no bounds checks (trusted code)
gcc -O3 -DWASM_RT_NO_MEMORY_CHECKS output.c wasm-rt-impl.c -o executable
```

### w2c2 (Advanced Transpiler)

**Repository:** https://github.com/turbolent/w2c2

**Enhanced Features:**
- **Streaming, single-pass compilation model**
- **C89-compatible output** for vintage systems (DOS, Mac OS 9, Windows XP)
- **Diverse architectures:** x86, ARM, PowerPC, SPARC, PA-RISC (including big-endian)
- **Separate compilation** into multiple files for large modules
- **Parallel compilation** using worker threads
- **Debug information** from DWARF line mapping
- **WASI implementation** (runs clang and Python)

**WebAssembly Support:**
- Passes **99.9% of WebAssembly core semantics test suite**
- Supports WASM 1.0 spec with extensions:
  - Threads
  - Bulk memory
  - Sign-extension

**Performance:**
~7% slower than native on Coremark 1.0 benchmark

**Key Insight from Research:**
> "The best WebAssembly runtime may be no runtime at all"

**Comparative Performance (Ed25519 benchmark):**
- w2c2: 73 seconds
- Wasmtime: 125 seconds
- **w2c2 is ~41% faster**

**Benefits:**
- **Dramatically smaller executables:** ~150KB vs 42MB for Wasmer
- **Direct C function interoperability** without FFI overhead
- **Straightforward module composition**
- **Human-readable output** for debugging
- **Use of formally-verified C compilers** (CompCert) for high-assurance code

**Limitations:**
- Unsuitable for browser arbitrary code execution
- No gas metering or preemption mechanisms
- Not ideal for dynamic code loading

**Example:**

```bash
# Transpile with debug info
w2c2 -d input.wasm output.c

# Compile with CompCert for verified compilation
ccomp -O2 output.c w2c2_base.c -o verified_executable

# Parallel compilation for large modules
w2c2 --parallel 8 large.wasm output/
```

---

## 3. Direct WebAssembly to Assembly Generation

### Cranelift Code Generation

**Pipeline:**
```
CLIF (Cranelift IR)
    ↓
Instruction Selection (Pattern Matching)
    ↓
VCode (Virtual-register Code)
    ↓
Register Allocation
    ↓
Machine Code
```

**Key Innovation: Pattern Matching**

During lowering, instruction inputs examined recursively to recognize patterns:
- Addressing modes
- Operation merging
- Instruction fusion

**Example: ARM64 Shift-Add Fusion**
```
Input: sub w1, w0, (shl w0, 21)
Output: sub w0, w1, w0, LSL 21  // Single instruction
```

**Register Allocation:**
Uses `regalloc2` crate:
- Handles tied operands
- Fixed register constraints
- Strategic move insertion
- 10-20% compilation time improvement
- Up to 7% runtime performance improvement

**Performance:**
- Compilation: ~20-35% faster than LLVM
- Runtime: ~86% of LLVM-optimized code
- Trade-off: Fast compilation for slightly slower execution

### LLVM WebAssembly Backend

**Process Flow:**

```
Source Code
    ↓
Frontend → LLVM IR
    ↓
Backend → WebAssembly Object Files
    ↓
wasm-ld → Final Module
```

**Benefits:**
- Full support for incremental compilation using object files
- Code sizes ~3.7% smaller than alternative backends
- Powerful IR optimizations and GVN (Global Value Numbering)
- Smart backend codegen

**Trade-off:**
LLVM is more powerful but slower to compile; Binaryen is faster to compile but less powerful as an optimizer.

**Optimization Levels:**
- `-O1`: Basic optimizations
- `-O2`: Most optimizations (recommended for production)
- `-O3`: Aggressive optimizations (may increase code size)
- `-Os`: Optimize for size
- `-Oz`: Aggressively optimize for size

**Link-Time Optimization (LTO):**
```bash
clang --target=wasm32-wasi -O2 -flto file1.c file2.c -o optimized.wasm
```

**Benefits:**
- 10-15% binary size reduction
- Up to 20% performance improvement
- Cross-module optimization

---

## 4. Static vs. Runtime Compilation Trade-offs

### AOT (Ahead-of-Time) Compilation

**Advantages:**
- **Fast startup:** Binary ready to run, no compilation overhead
- **Predictable performance:** No compilation during execution
- **Security:** Eliminates JIT bugs (historically "most productive source of CVEs in production browsers")
- **Deterministic execution:** Enables snapshotted, reproducible execution
- **Fine-grained sandboxing:** All code known at deployment time
- **Cold-start scenarios:** Ideal for instance-per-request models

**Disadvantages:**
- **Larger binaries:** Typically 2x size of IL-interpreted versions
- **No runtime specialization:** Cannot optimize based on observed behavior
- **Static optimization only:** Misses opportunities from type feedback, object shapes, dispatch targets
- **Load-time cost:** Trades off load-time for runtime performance

### JIT (Just-in-Time) Compilation

**Advantages:**
- **Runtime specialization:** Generates code based on observed behavior
- **Adaptive optimization:** Optimizes hot paths, adapts to changing conditions
- **Whole-function analysis:** Combines operations together
- **Smaller initial footprint:** Compiles only what's needed

**Disadvantages:**
- **Slow startup:** Compilation overhead at runtime
- **Unpredictable performance:** Warm-up periods required
- **Security concerns:** Complex JIT compilers source of vulnerabilities
- **Memory overhead:** Runtime code generation infrastructure

### Hybrid Approach: AOT + Inline Caches

**Strategy** (from Chris Fallin's research):
- Precompile common IC (Inline Cache) patterns into static code (~2,367 variations)
- Use function pointers to dispatch to precompiled IC stubs
- Compile straightforward skeleton code invoking IC sites
- Apply Profile-Guided Inlining (Winliner) for frequently-targeted stubs

**Results on Octane benchmarks:**
- Geomean speedup: 2.77x
- Range: 0.90x–4.39x depending on benchmark
- Native baseline compiler: ~5x improvement

**When to Use:**
- **AOT:** Constrained platforms (WASM, embedded), security-critical contexts, cold-start scenarios
- **JIT:** Native platforms with runtime codegen, long-running processes, variable workloads
- **Hybrid:** Platforms requiring both performance and deployment constraints

### WAMR Running Modes Comparison

**LLVM JIT:**
- Best execution performance
- Longer compilation time
- Suitable for long-running processes

**Fast JIT:**
- Lightweight, small footprint
- Quick startup
- Good performance
- Suitable for edge computing

**AOT:**
- Nearly native speed
- Very small footprint
- Quick startup
- **Ideal for embedded systems**

**Interpreter:**
- Near-immediate startup
- Slower execution
- Minimal footprint
- Suitable for severely constrained devices

---

## 5. Optimization Opportunities

### Binaryen Optimization Passes

**Repository:** https://github.com/WebAssembly/binaryen

Binaryen is a compiler and toolchain infrastructure library for WebAssembly.

#### Core Optimization Strategies

**Standard Passes:**
- **CoalesceLocals:** Register allocation via live range analysis, minimizes local count, removes copies
- **CodeFolding:** Merges duplicate code
- **DeadCodeElimination:** Removes dead code
- **DeadArgumentElimination:** Link-time optimization removing always-constant function arguments
- **MinifyImportsAndExports:** Reduces names to single characters

**Usage:**
```bash
# Basic optimization
wasm-opt -O3 input.wasm -o output.wasm

# Size optimization
wasm-opt -Oz input.wasm -o output.wasm

# With LTO
wasm-opt -O3 --low-memory-unused input.wasm -o output.wasm
```

#### Advanced Techniques

**1. Low Memory Unused (`--low-memory-unused`):**
- Assumes addresses <1024 unused
- Enables constant folding into load/store offsets
- Requires wasm-ld configuration to avoid low-address globals

**2. GUFA (Global Unified Flow Analysis):**
- Whole-program inference of constant values
- Determines exact types (valuable for WebAssembly GC)
- Infers function results even for MVP WebAssembly

**3. ReReloop (`--flatten --rereloop -Oz -Oz`):**
- Complete rewrite of control flow graph
- Several percentage points improvement
- Run `-Oz` twice afterward to clean up flattened IR

**4. Traps Never Happen (`-tnh`):**
- Assumes traps never occur
- Enables dead code removal along trap paths
- Removes crash reporting (unsuitable for error-critical apps)
- **Use only for trusted, well-tested code**

**5. Converge (`--converge`):**
- Runs optimization passes in loop until fixed point
- Benefits typically small but significant in large programs

**6. Global Effects Analysis:**
```bash
# Generate global effects file
wasm-opt --generate-global-effects -O3 input.wasm -o temp.wasm

# Use in subsequent optimizations
wasm-opt --use-global-effects temp.effects -O3 temp.wasm -o output.wasm
```

**7. Monomorphization (`--monomorphize`):**
- Specializes functions per call context
- Discovers opportunities standard inlining misses
- Control aggressiveness:
```bash
wasm-opt --monomorphize --pass-arg=monomorphize-min-benefit@75 input.wasm -o output.wasm
```

**8. Partial Inlining (`--partial-inlining-ifs=1`):**
- Inlines early-exit conditionals without full function body

#### Link-Time Optimization (LTO)

**Benefits:**
- Cross-module optimization enabling better inlining
- Dead code elimination across compilation units
- 10-15% binary size reduction typical
- Up to 20% performance improvement

**Emscripten LTO:**
```bash
emcc -flto -O2 file1.c file2.c -o output.js
```

**Note:** Binaryen is "always LTO" as it typically runs on final linked WASM.

### LLVM/Emscripten Optimizations

**Compiler Flags:**

**Speed:**
```bash
-O1, -O2, -O3  # Increasing optimization levels
-msimd128       # Enable SIMD with auto-vectorization
-mnontrapping-fptoint  # Use non-trapping float-to-int
```

**Size:**
```bash
-Os, -Oz        # Size-focused optimizations
-flto           # Link-time optimization
```

**Auto-vectorization:**
- Enabled by default at `-O2` and `-O3` with `-msimd128`
- Transforms loops with arithmetic operations into SIMD operations
- Significant gains in:
  - ML inference
  - Bioinformatics
  - Scientific computing
  - Image/video processing

**SIMD Intrinsics Support:**
```c
#include <wasm_simd128.h>

// WebAssembly SIMD intrinsics
v128_t a = wasm_v128_load(ptr);
v128_t b = wasm_i32x4_add(a, a);
```

**Cross-compiled intrinsics:**
- x86 SSE/AVX intrinsics
- ARM NEON intrinsics
- GCC/Clang SIMD Vector Extensions

### Function Inlining & Dead Code Elimination

**wasm-opt capabilities:**
- Function call inlining reduces overhead
- Advanced dead code elimination at binary instruction level
- Control flow simplification

**Performance Impact:**
- Transitioning from JIT to AOT can decrease initial load times by up to 50%
- Reduces code to execute for faster performance

**Example workflow:**
```bash
# Compile with inlining hints
clang --target=wasm32-wasi -O2 -flto \
      -Wl,--lto-O3 \
      source.c -o intermediate.wasm

# Post-process with Binaryen
wasm-opt -O3 --inline-functions-with-loops \
         --converge \
         intermediate.wasm -o optimized.wasm

# Measure results
wasm-opt --print-function-sizes optimized.wasm
```

---

## 6. Maintaining WebAssembly Guarantees in Native Code

### Core Safety Guarantees

#### Memory Isolation

**WebAssembly Specification Requirements:**
- Linear memory bounds-checked at region level
- Potential trap on out-of-bounds access
- Memory isolated from runtime internal memory
- Zero-initialized by default
- Modules protected from each other

**Implementation Approaches:**

**1. Virtual Memory Trick (32-bit):**
```
Reserve 8GB virtual memory region for all possible 32-bit addresses
Page fault if access beyond allocated size
Eliminates explicit bounds checks for static memories
```

**Overhead:**
- Static memories: Near-zero bounds check overhead
- Dynamic memories: ~55% overhead (explicit checks required)

**2. Explicit Bounds Checks:**
```c
// Every memory access
if (addr + size > memory->pages * PAGE_SIZE) {
    trap(OUT_OF_BOUNDS);
}
data = memory->data[addr];
```

**Optimization:**
- Compiler can eliminate repeated checks in same scope
- Segue optimization: Uses x86 segment registers, reduces overhead by 8.3%

**3. Two-Level Guard Pages (64-bit):**
- Addresses Memory64 challenges where virtual memory trick doesn't scale
- Reduces bounds checking overhead from >100% to 12.7%

**4. Hardware-Assisted (Cage with ARM MTE):**
- Offloads bounds checks to Memory Tagging Extension hardware
- Significant performance improvement for 64-bit WASM
- Suitable for high-end embedded (Cortex-A with MTE)

#### Control-Flow Integrity

**Guarantees:**
- Function calls must specify valid index in function/table space
- Indirect calls undergo runtime type signature verification
- Prevents code injection and ROP (return-oriented programming) attacks
- Protected call stacks immune to buffer overflows

**Implementation:**
```c
// Type-checked indirect call
typedef void (*wasm_func_ptr_t)(/* ... */);

void call_indirect(uint32_t index, /* args */) {
    if (index >= table->size) trap(UNDEFINED_ELEMENT);
    if (table->types[index] != expected_type) trap(CALL_INDIRECT_TYPE_MISMATCH);
    wasm_func_ptr_t func = table->funcs[index];
    func(/* args */);
}
```

**CFI Benefits:**
- Index-based variables (local and global) prevent buffer overflow impacts
- Function-level code reuse attacks theoretically possible but restricted vs traditional ROP

#### Software Fault Isolation (SFI)

**Wasm as SFI System:**
- Lightweight sandboxing for untrusted components
- Used by Fastly, Cloudflare for multi-tenant edge clouds
- Responsible for translating and bounds-checking linear memory accesses

**Zero-Cost Transitions:**
- Traditional SFI uses heavyweight transitions (save, clear, restore registers)
- Research identifies zero-cost conditions when sandboxed code has sufficient structure
- Enables lightweight transitions without security compromise

### Preserving Safety in Transpiled Code

#### wasm2c Approach:

**1. Unified Memory Access:**
```c
static inline uint32_t wasm_i32_load(wasm_rt_memory_t* mem, uint64_t addr) {
    WASM_RT_CHECK(addr + sizeof(uint32_t) <= mem->size);
    return *(uint32_t*)(mem->data + addr);
}
```

**Guaranteed to stay within sandbox (unless `WASM_RT_NO_MEMORY_CHECKS` defined)**

**2. Type Safety:**
```c
// Type-checked indirect calls implemented
typedef void (*wasm_rt_funcref_t)(void);

void call_indirect(uint32_t index) {
    if (index >= table.size) {
        wasm_rt_trap(WASM_RT_TRAP_UNDEFINED_ELEMENT);
    }
    // Type verification
    if (table.types[index] != expected_type) {
        wasm_rt_trap(WASM_RT_TRAP_CALL_INDIRECT_TYPE_MISMATCH);
    }
    table.data[index]();
}
```

**3. Stack Management:**
- Clean trap on stack exhaustion
- Protected from buffer overflow attacks
- Separate from linear memory

#### Sandboxing Properties

**Benefits** (compiling C→WASM→C):
> "Take existing C code, compile to WebAssembly, transpile back to C → same code but sandboxed"

**Advantages:**
- Restricts virtual memory range accessible to each instance
- Acts as sanitizer improving safety
- No runtime overhead (with checks disabled)
- Negligible startup time

**Limitations:**
- Memory-unsafe C remains unsafe when compiled to WASM
- Buffer overflows and use-after-free exploitable in WASM nearly as easily as native
- WASM provides **isolation between modules**, not memory safety **within module** from unsafe languages

### Safety Guarantees Summary

| **Property** | **WebAssembly Guarantee** | **Preserved in AOT/Transpilation** |
|--------------|---------------------------|-------------------------------------|
| Memory bounds checking | Yes (region-level) | Yes (explicit checks or virtual memory) |
| Module isolation | Yes (separate linear memories) | Yes (separate memory instances) |
| Control-flow integrity | Yes (typed indirect calls) | Yes (type verification maintained) |
| Stack protection | Yes (separate from linear memory) | Yes (protected call stack) |
| Deterministic traps | Yes (specified trap conditions) | Yes (maintained in generated code) |
| Memory safety (language-level) | No (depends on source language) | No (inherits source language properties) |

---

## 7. Link-Time Optimization for WebAssembly Components

### Component Model Linking Strategies

**Two Primary Axes:**

**1. Memory Sharing:**
- **Shared-everything:** Modules share memory and table instances
- **Shared-nothing:** Components have isolated memory spaces

**2. Storage:**
- **Inline:** Embedded child modules
- **Import:** External module references

### Shared-Everything Linking

**Static Linking (Toolchain-level):**
- Fuses code into single module before runtime
- Invisible to Component Model runtime
- Maximum optimization potential
- Tool: `wasm-ld`

**Dynamic Linking (Runtime-level):**
- Separate modules remain distinct
- Allows shared machine code (like shared libraries)
- All modules statically declared before execution
- Enables AOT compilation of entire component graph

**Optimization Opportunities:**
- Cross-module inlining
- Dead code elimination across boundaries
- Constant propagation through imports/exports
- Shared compiled machine code (JIT cache)

### Shared-Nothing Linking

**Characteristics:**
- Components cannot share memory or table instances
- Communication only through Canonical ABI
- Strong isolation guarantees
- Language heterogeneity

**Trade-offs:**
- Canonical ABI overhead
- Memory overhead (separate memories)
- Less optimization across boundaries

### Composition Workflow

```
C/C++ Source
    ↓
WebAssembly Objects (clang)
    ↓
Static Linking (wasm-ld)
    ↓
Component Wrapping
    ↓
Dynamic Linking (multiple components)
    ↓
Shared-Nothing Composition (wac/wasm-tools compose)
```

### Optimization Challenges

**Memory Overhead:**
- Composed components may require many WASM core modules (~17 in some applications)
- Each module has own memory → significant memory overhead

**Active Research:**
Optimization approaches allowing linked components to share memory while maintaining canonical ABI optimization.

**Synthesis Strategy:**
1. Analyze component memory usage
2. Identify optimization opportunities (shared-everything where safe)
3. Apply whole-program AOT compilation
4. Generate target-specific code with cross-component inlining

---

## 8. Synthesis Recommendations

### Approach Comparison for Embedded Synthesis

| **Approach** | **Compilation Speed** | **Runtime Performance** | **Binary Size** | **Embedded Suitability** |
|--------------|----------------------|-------------------------|-----------------|--------------------------|
| **wasm2c/w2c2** | Fast | Excellent (~93-100%) | Small (~150KB runtime) | Excellent |
| **Cranelift AOT** | Very Fast | Good (~86%) | Medium | Good |
| **LLVM AOT** | Slow | Excellent (~85-90%) | Small | Excellent |
| **Hybrid** | Medium | Very Good (2.77x avg) | Large | Good |

### Recommended Strategy for Synth

**Phase 1: Prototype (w2c2-based)**
- Fast iteration
- Human-readable output
- CompCert integration for verified compilation
- Excellent for Cortex-M and embedded RISC-V

**Phase 2: Production (LLVM AOT-based)**
- Maximum performance
- Target-specific optimizations
- LTO for cross-component optimization
- Binaryen post-processing

**Phase 3: Specialized (Custom ISLE-based)**
- Develop embedded-specific lowering rules
- Hardware-assisted bounds checking (MPU/PMP)
- XIP support
- Formally verified instruction selection

**Phase 4: Verified (CompCert-style)**
- Mechanized semantics in Coq
- Verified synthesis rules
- Certification artifacts
- Safety-critical qualification

---

## 9. Key Resources

### Tools
- WABT (wasm2c): https://github.com/WebAssembly/wabt
- w2c2: https://github.com/turbolent/w2c2
- Binaryen: https://github.com/WebAssembly/binaryen
- Wasmtime: https://github.com/bytecodealliance/wasmtime
- WasmEdge: https://github.com/WasmEdge/WasmEdge
- Wasmer: https://github.com/wasmerio/wasmer

### Documentation
- Binaryen Optimizer Cookbook: https://github.com/WebAssembly/binaryen/wiki/Optimizer-Cookbook
- Emscripten Optimization: https://emscripten.org/docs/optimizing/Optimizing-Code.html
- WebAssembly Security: https://webassembly.org/docs/security/

### Blog Posts
- Chris Fallin: "AOT vs JIT compilation" https://cfallin.org/blog/
- Mozilla: "WebAssembly Streaming Compilation"
- V8: "WebAssembly Compilation Pipeline"

---

**Document Status:** Complete
**Next Steps:** Integrate AOT strategies into synthesis architecture and PoC plan
