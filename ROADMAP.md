# Synth Roadmap

**Focus:** Minimal working demo - Calculator running on embedded hardware

---

## Current Status

- **Phase 1:** In Progress
- **Code:** 14 crates, ~24K lines, 380+ tests passing
- **Coverage:** 151/151 WASM Core 1.0 operations (unit tests)
- **Working:** `synth compile input.wat -o output.elf --cortex-m` produces complete Cortex-M binaries
- **New:** AAPCS-compliant code generation, vector tables, startup code

---

## Phase 0: Organization & Cleanup

**Duration:** 1 week | **Status:** Nearly Complete

| Task | Status |
|------|--------|
| Consolidate root documentation | Done |
| Create docs/ structure | Done |
| Document Synth/Loom relationship | Done |
| Archive obsolete docs | Done |
| Audit crate boundaries | Done |
| Create realistic roadmap | This document |
| Document feature status | Next |

**Success Criteria:**
- [x] ≤5 markdown files at root
- [x] Clear docs/ structure
- [x] Crate architecture documented
- [ ] Honest feature matrix

---

## Phase 1: Build System & Code Generation

**Duration:** 2 weeks | **Status:** In Progress

| Task | Priority | Status |
|------|----------|--------|
| Fix Bazel dependency resolution | P0 | Done |
| Create BUILD files for all crates | P0 | Done |
| WASM → ELF integration test | P1 | Done |
| Vector table generation | P1 | Done |
| Startup code (reset handler) | P1 | Done |
| AAPCS-compliant register allocation | P1 | Done |
| Binary validation tests | P1 | Done |
| ARM cross-compilation toolchain | P1 | Open |
| Renode/QEMU testing infrastructure | P1 | Open |
| Integrate Coq/OCaml extraction | P2 | Open |
| Loom dependency integration | P2 | Open |

**Success Criteria:**
- [x] `bazel build //crates:synth` works
- [x] `synth compile input.wat -o output.elf --cortex-m` generates valid Cortex-M binary
- [x] Vector table, startup code, and function code all present
- [x] AAPCS calling convention (params in r0-r3, return in r0)
- [ ] `bazel test //...` passes
- [ ] Integration test: WASM → ELF → Renode

---

## Phase 2: Calculator Demo

**Duration:** 2 weeks

### 2a: WASM Module
| Task | Priority |
|------|----------|
| Create calculator.wat (add, sub, mul, div) | P0 |
| Unit tests for WASM module | P1 |

### 2b: Compiler CLI
| Task | Priority | Status |
|------|----------|--------|
| Wire synth-cli to full pipeline | P0 | Done |
| `synth compile input.wasm -o output.elf` | P0 | Done |
| Add `--target`, `--optimize` flags | P1 | Open |
| Add verification pass (optional) | P1 | Open |

### 2c: Zephyr Integration
| Task | Priority |
|------|----------|
| Create Zephyr calculator app | P0 |
| Integrate Synth into CMake build | P0 |
| Test on QEMU | P0 |
| Test on real hardware | P1 |

### 2d: Demo
| Task | Priority |
|------|----------|
| Documentation with screenshots | P1 |
| Demo video | P2 |

**Success Criteria:**
- [x] `synth compile calculator.wasm -o calculator.elf` works
- [ ] Calculator runs in QEMU
- [ ] Calculator runs on hardware (STM32/nRF52)
- [ ] Demo video recorded

---

## Phase 3: Polish & Release

**Duration:** 1 week

| Task | Priority |
|------|----------|
| GitHub Actions CI (Rust tests) | P0 |
| GitHub Actions CI (Bazel builds) | P0 |
| Code coverage reporting | P1 |
| Development setup guide | P1 |
| API documentation (rustdoc) | P1 |
| User guide | P1 |
| Tag v0.1.0 release | P0 |

**Success Criteria:**
- [ ] CI/CD operational
- [ ] Documentation complete
- [ ] v0.1.0 released

---

## Out of Scope (Future)

These are **not** in the current roadmap:

- SIMD/vector operations
- RISC-V backend
- Full Component Model support
- Safety certification (ISO 26262)
- Production optimizations
- Commercial features

See `docs/planning/FUTURE_ROADMAP.md` for long-term vision.

---

## Timeline Summary

| Phase | Duration | Goal |
|-------|----------|------|
| Phase 0 | Week 1 | Clean, organized repo |
| Phase 1 | Weeks 2-3 | Working Bazel build |
| Phase 2 | Weeks 4-5 | Calculator demo |
| Phase 3 | Week 6 | v0.1.0 release |

**Total: 6 weeks to working demo**

---

## Tracking

- **Issues:** [GitHub Issues](https://github.com/pulseengine/Synth/issues)
- **Milestones:** phase-0-cleanup, phase-1-bazel, phase-2-calculator, phase-3-polish
- **Project Board:** [Synth Reorganization](https://github.com/orgs/pulseengine/projects)
