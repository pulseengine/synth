# Synth Roadmap

**Updated:** February 2026

---

## Current Status

- **18 crates**, ~24K lines of Rust, **496 tests passing**
- **151/151** WASM Core 1.0 operations have synthesis rules + unit tests
- **End-to-end compilation works:** `synth compile input.wat -o output.elf`
- **Multi-backend architecture:** Backend trait, registry, ARM backend functional
- **Z3 formal verification:** `--verify` flag and `synth verify` command
- **Cortex-M binaries:** vector tables, startup code, AAPCS calling convention

---

## Completed Work

### Phase 0: Organization & Cleanup ✅

| Task | Status |
|------|--------|
| Documentation structure (91+ docs) | Done |
| Crate architecture (18 crates) | Done |
| Feature matrix | Done |
| Roadmap | Done |

### Phase 1: Build System & Code Generation ✅

| Task | Status |
|------|--------|
| Bazel BUILD files (17/18 crates) | Done |
| WASM → ARM ELF compilation | Done |
| Vector table generation | Done |
| Startup code (reset handler) | Done |
| AAPCS-compliant register allocation | Done |
| Binary validation tests | Done |
| Cortex-M complete binaries | Done |

### Multi-Backend Restructure (8 phases) ✅

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Preserve arm-compiler-v1 branch | Done |
| 2 | Extract WasmOp + wasm_decoder to synth-core | Done |
| 3 | Create Backend trait + TargetSpec | Done |
| 4 | Wrap ARM compiler as Backend | Done |
| 5 | Feature-gate synth-backend | Done |
| 6 | Backend-agnostic verification traits | Done |
| 7 | External backend crate stubs (aWsm, wasker, w2c2) | Done |
| 8 | CLI rework (--backend, --verify, backends) | Done |

### Z3 Verification ✅

| Task | Status |
|------|--------|
| Z3 0.19 API migration (605 errors fixed) | Done |
| WASM semantics encoding (30+ ops) | Done |
| ARM semantics encoding (20+ instrs) | Done |
| Translation validator (Alive2-style proofs) | Done |
| `--verify` flag wired to real Z3 | Done |
| `synth verify` standalone command | Done |
| 53 comprehensive verification tests | Done |

---

## Current Roadmap

### Phase A: End-to-End Integration (P0)

Close the gap between "unit tests pass" and "compiler actually works end-to-end."

| Task | Priority | Status |
|------|----------|--------|
| Calculator demo (add, sub, mul, div) | P0 | Open |
| Control flow through full compile path | P0 | Open |
| Memory operations through full compile path | P0 | Open |
| WAST integration test runner | P1 | Open |

**Success Criteria:**
- [ ] `synth compile calculator.wat --all-exports --cortex-m -o calculator.elf` works
- [ ] `synth verify calculator.wat calculator.elf` passes
- [ ] Control flow (if/else, loop, br) compiles end-to-end
- [ ] Memory ops (load/store) compile end-to-end

### Phase B: CI/CD & Automated Testing (P0)

| Task | Priority | Status |
|------|----------|--------|
| GitHub Actions: `cargo test --workspace` | P0 | Open |
| GitHub Actions: `cargo clippy --workspace` | P0 | Open |
| GitHub Actions: `cargo fmt --check` | P0 | Open |
| GitHub Actions: Z3 verification tests | P1 | Open |
| Pre-commit hooks | P2 | Open |

**Success Criteria:**
- [ ] PRs run tests automatically
- [ ] Code quality checks enforced
- [ ] Z3 verification tests run weekly or on synth-verify changes

### Phase C: Testing Infrastructure (P1)

| Task | Priority | Status |
|------|----------|--------|
| QEMU ARM testing harness | P0 | Open |
| Renode integration (config files exist) | P1 | Open |
| W3C spec test suite adapter (267 files exist) | P2 | Open |

**Success Criteria:**
- [ ] Compiled ELFs execute on QEMU and produce correct results
- [ ] Spec test conformance percentage tracked

### Phase D: External Backends (P2)

| Task | Priority | Status |
|------|----------|--------|
| w2c2 backend: `compile_module()` | P0 | Open |
| aWsm backend: `compile_module()` | P1 | Open |
| wasker backend: `compile_module()` | P1 | Open |
| Backend comparison tests | P2 | Open |

### Phase E: Bazel & Build (P2)

| Task | Priority | Status |
|------|----------|--------|
| Add synth-memory to BUILD.bazel | P0 | Open |
| Verify `bazel build //crates:synth` | P1 | Open |
| Verify `bazel test //...` | P1 | Open |

### Phase F: Authoritative ISA Semantics (P3, Research)

| Task | Priority | Status |
|------|----------|--------|
| Evaluate Sail ARM integration | P0 | Research |
| RISC-V via sail-riscv | P1 | Research |

**Goal:** Replace hand-written ARM semantics with machine-readable specs derived from ARM's own ISA specification, making verification proofs authoritative.

---

## Out of Scope (Future)

- SIMD/vector operations
- RISC-V backend (pending Phase F research)
- Full Component Model support
- ISO 26262 / IEC 62304 certification
- Production optimizations
- Commercial features

---

## Key Metrics

| Metric | Value |
|--------|-------|
| Crates | 18 |
| Lines of Rust | ~24K |
| Tests | 496 |
| WASM ops covered | 151/151 (100%) |
| Z3 verification tests | 53 |
| Documentation files | 91+ |
| Backends registered | 4 (1 functional) |

---

## Tracking

- **Issues:** [GitHub Issues](https://github.com/pulseengine/Synth/issues)
- **Plan:** `.claude/plans/elegant-toasting-koala.md` (detailed execution plan)
