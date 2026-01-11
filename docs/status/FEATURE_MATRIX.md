# Feature Matrix: Current vs Aspirational

**Last Updated:** January 2026

This document provides an honest assessment of what works, what doesn't, and what's planned.

---

## Legend

| Symbol | Meaning |
|--------|---------|
| ✅ | Working - tested and functional |
| ⚠️ | Partial - implemented but not integrated |
| ❌ | Not implemented |
| 🔬 | Research/experimental |

---

## Core Compiler Pipeline

| Component | Status | Notes |
|-----------|--------|-------|
| WASM parsing | ✅ | wasmparser integration works |
| WIT parsing | ✅ | Custom parser implemented |
| Component validation | ⚠️ | Basic validation only |
| IR generation | ⚠️ | Types defined, generation partial |
| Optimization passes | ⚠️ | Passes exist, not wired to pipeline |
| Instruction selection | ⚠️ | Pattern matcher exists, not integrated |
| Register allocation | ⚠️ | Graph coloring implemented |
| ARM code generation | ⚠️ | Assembly generation works |
| ELF emission | ⚠️ | ELF builder exists |
| **End-to-end CLI** | ❌ | **Not wired together** |

### Reality Check

> **Unit tests pass (376/376), but there's no working compiler.**
>
> Each stage works in isolation. The CLI doesn't connect them into a functioning pipeline.

---

## WebAssembly Operations

| Category | Operations | Unit Tests | Integrated |
|----------|------------|------------|------------|
| i32 arithmetic | 52 | ✅ 100% | ❌ |
| i64 arithmetic | 40 | ✅ 100% | ❌ |
| f32 operations | 29 | ✅ 100% | ❌ |
| f64 operations | 30 | ✅ 100% | ❌ |
| **Total** | **151** | **✅ 100%** | **❌ 0%** |

### What "100% Coverage" Means

- ✅ All 151 WASM Core 1.0 operations have synthesis rules
- ✅ All 151 operations pass unit tests
- ❌ Operations are NOT tested in end-to-end compilation
- ❌ No integration tests exist

---

## Verification

| Feature | Status | Notes |
|---------|--------|-------|
| Z3 SMT solver integration | ✅ | Works in synth-verify |
| Translation validation | ⚠️ | Per-operation, not full pipeline |
| Coq proofs | 🔬 | Research artifacts, not integrated |
| Sail ARM semantics | 🔬 | Evaluated, not implemented |

### Reality Check

> Coq proofs exist in `coq/` directory but are **not used** by the Rust compiler.
> They are research artifacts demonstrating the approach.

---

## Target Support

| Target | Status | Notes |
|--------|--------|-------|
| ARM Cortex-M4 | ⚠️ | Code generation works, untested on hardware |
| ARM Cortex-M4F | ⚠️ | FPU support partial |
| ARM Cortex-M7 | ❌ | Not implemented |
| RISC-V | ❌ | Not implemented |

---

## Embedded Features

| Feature | Status | Notes |
|---------|--------|-------|
| Vector table generation | ⚠️ | Implemented, not tested |
| Reset handler | ⚠️ | Implemented, not tested |
| Linker script generation | ⚠️ | Implemented, not tested |
| MPU configuration | ⚠️ | Implemented, not tested |
| XIP (execute in place) | ❌ | Not implemented |

---

## Build System

| System | Status | Notes |
|--------|--------|-------|
| Cargo | ✅ | Works, tests pass |
| Bazel | ❌ | Broken - hardcoded paths |
| Coq/Dune | 🔬 | Separate from Rust build |

---

## Testing

| Type | Status | Coverage |
|------|--------|----------|
| Unit tests | ✅ | 376 tests, 100% pass |
| Integration tests | ❌ | None |
| QEMU tests | ❌ | None |
| Hardware tests | ❌ | Never tested |

---

## Documentation

| Document | Status |
|----------|--------|
| README | ✅ |
| Architecture | ✅ |
| Crate structure | ✅ |
| API docs (rustdoc) | ⚠️ Partial |
| User guide | ❌ |
| Development guide | ❌ |

---

## CLI Commands

| Command | Status | Notes |
|---------|--------|-------|
| `synth parse` | ⚠️ | Parses but minimal output |
| `synth synthesize` | ❌ | Not wired |
| `synth compile` | ❌ | Doesn't exist yet |
| `synth target-info` | ❌ | Not implemented |

---

## Summary

### What Actually Works

1. **Parsing:** WASM and WIT files can be parsed
2. **Unit tests:** All 376 tests pass
3. **Individual stages:** Each compiler stage works in isolation
4. **Documentation:** Well-organized docs structure

### What Doesn't Work

1. **End-to-end compilation:** Cannot compile WASM → ELF
2. **CLI:** Not connected to pipeline
3. **Bazel:** Build system broken
4. **Hardware testing:** Never tested on real device

### Priority Gap

> The gap between "tests pass" and "compiler works" is the **CLI integration**.
>
> Wiring `synth-cli` → `synth-frontend` → ... → `synth-backend` is the critical path.

---

## Aspirational Features (Not Started)

These features are mentioned in documentation but have no implementation:

- SIMD/vector operations
- RISC-V backend
- Full Component Model (only core WASM)
- ISO 26262 certification
- IEC 62304 certification
- Commercial support

---

## Conclusion

**Synth has strong foundations but is not yet a working compiler.**

The path to a working demo:
1. Wire the CLI pipeline (Phase 2)
2. Test on QEMU
3. Test on hardware
4. Release v0.1.0

See [ROADMAP.md](/ROADMAP.md) for the plan.
