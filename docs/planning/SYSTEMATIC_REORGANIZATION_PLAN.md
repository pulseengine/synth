# Synth Systematic Reorganization Plan

**Date**: 2025-11-21
**Status**: Planning Phase
**Goal**: Transform Synth from research prototype to production-ready embedded WebAssembly compiler

---

## 🎯 Overall Vision

Create a **minimal, working end-to-end pipeline**:
```
calculator.wat → Synth Compiler → calculator.elf → Flash to Zephyr board → Run
```

---

## 📊 Project Phases

### Phase 0: Organization & Cleanup (Week 1)
**Goal**: Clean, organized repository with clear structure

### Phase 1: Bazel Build System (Week 2-3)
**Goal**: Working Bazel build for Rust crates, OCaml extraction, and integration tests

### Phase 2: Minimal Calculator Example (Week 4-5)
**Goal**: Simple calculator WASM app running on Zephyr board

### Phase 3: Integration & Documentation (Week 6)
**Goal**: Polished, documented, reproducible demo

---

## 🏗️ Phase 0: Organization & Cleanup

### Milestone: `phase-0-cleanup`

#### Issue Group 1: Documentation Reorganization (Priority: P0)

**Issue #1: Consolidate root-level documentation**
- **Labels**: `docs`, `cleanup`, `P0`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Move all session notes to `docs/sessions/` or archive
  - [ ] Consolidate Bazel docs → `docs/build-systems/BAZEL.md`
  - [ ] Consolidate Sail docs → `docs/research/SAIL_INTEGRATION.md`
  - [ ] Consolidate validation docs → `docs/validation/STATUS.md`
  - [ ] Keep only 5 files at root: README, ARCHITECTURE, CHANGELOG, LICENSE, CONTRIBUTING
  - [ ] Update README.md as single entry point with clear navigation
- **Acceptance Criteria**:
  - ≤5 markdown files at project root
  - All docs accessible via README navigation tree
  - No duplicate/overlapping content

**Issue #2: Create documentation structure**
- **Labels**: `docs`, `enhancement`, `P0`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Create `docs/` subdirectories:
    ```
    docs/
    ├── status/           # PROJECT_STATUS.md, progress
    ├── sessions/         # Session notes (or delete)
    ├── analysis/         # Technical deep dives
    ├── planning/         # Roadmaps, todos
    ├── research/         # Literature review
    ├── build-systems/    # Cargo, Bazel, Dune
    ├── validation/       # Test reports, coverage
    └── architecture/     # System design
    ```
  - [ ] Move existing docs to appropriate directories
  - [ ] Create index.md in each directory
  - [ ] Update all cross-references
- **Acceptance Criteria**:
  - Clear directory structure
  - No orphaned documents
  - All links work

**Issue #3: Clarify Synth vs Loom relationship**
- **Labels**: `docs`, `architecture`, `P0`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Document Loom repository (github.com/pulseengine/loom)
  - [ ] Explain two-tier architecture clearly
  - [ ] Document which components live where
  - [ ] Create dependency diagram (Synth depends on Loom)
  - [ ] Update ARCHITECTURE.md with clarification
  - [ ] Add section to README about Loom integration
- **Acceptance Criteria**:
  - Clear explanation of Synth/Loom split
  - Diagram showing relationship
  - No confusion in documentation

**Issue #4: Archive or delete obsolete documentation**
- **Labels**: `docs`, `cleanup`, `P1`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Review all session notes - extract insights, then delete
  - [ ] Archive experimental docs (Sail, ASIL D plans) to `docs/archive/`
  - [ ] Delete duplicate validation reports
  - [ ] Remove "REALITY_CHECK" and "HONEST_COMPARISON" docs (too meta)
  - [ ] Keep only actionable, current documentation
- **Acceptance Criteria**:
  - No session notes at root
  - Experimental work clearly marked as archived
  - All kept docs are relevant to current work

#### Issue Group 2: Crate Structure Refactoring (Priority: P1)

**Issue #5: Audit crate boundaries and responsibilities**
- **Labels**: `architecture`, `refactor`, `P1`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Document current responsibility of each crate
  - [ ] Identify overlaps (synth-synthesis vs synth-opt)
  - [ ] Identify gaps (missing integration layer?)
  - [ ] Propose consolidation plan
  - [ ] Create crate dependency diagram
- **Acceptance Criteria**:
  - Document: `docs/architecture/CRATE_STRUCTURE.md`
  - Clear responsibility matrix
  - Dependency diagram
  - Refactoring proposal

**Issue #6: Merge synthesis and optimization crates**
- **Labels**: `refactor`, `P2`
- **Milestone**: `phase-0-cleanup`
- **Dependencies**: Issue #5
- **Tasks**:
  - [ ] Merge synth-synthesis + synth-opt → synth-optimize
  - [ ] Unify ISLE rules and E-graph optimization
  - [ ] Update all dependencies
  - [ ] Update tests
  - [ ] Update documentation
- **Acceptance Criteria**:
  - Single optimization crate
  - All tests pass
  - Clear module boundaries within crate

**Issue #7: Split backend crate into logical components**
- **Labels**: `refactor`, `P2`
- **Milestone**: `phase-0-cleanup`
- **Dependencies**: Issue #5
- **Tasks**:
  - [ ] Split synth-backend into:
    - `synth-codegen`: ARM instruction encoding
    - `synth-binary`: ELF, linker scripts
    - `synth-target`: Target-specific (MPU, startup, vector tables)
  - [ ] Update dependencies
  - [ ] Update tests
  - [ ] Update documentation
- **Acceptance Criteria**:
  - Three separate crates with clear boundaries
  - All tests pass
  - Cleaner compilation pipeline

#### Issue Group 3: Roadmap Reality Check (Priority: P1)

**Issue #8: Create realistic Phase 0-2 roadmap**
- **Labels**: `planning`, `docs`, `P1`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Archive 550-todo roadmap to `docs/planning/FUTURE_ROADMAP.md`
  - [ ] Create new `ROADMAP.md` with only Phase 0-2 tasks
  - [ ] Focus on: Cleanup → Bazel → Calculator demo
  - [ ] No SIMD, no Phase 4+ features
  - [ ] Clear milestones with dates
- **Acceptance Criteria**:
  - New roadmap with ≤50 actionable items
  - All items relevant to minimal demo
  - Clear success criteria per phase

**Issue #9: Document current vs aspirational features**
- **Labels**: `docs`, `honesty`, `P1`
- **Milestone**: `phase-0-cleanup`
- **Tasks**:
  - [ ] Create `docs/status/FEATURE_MATRIX.md`
  - [ ] Mark what works: ✅ Unit tests pass, ⚠️ Not integrated, ❌ Not implemented
  - [ ] Clarify: Coq proofs are research artifacts, not in pipeline (yet)
  - [ ] Clarify: No end-to-end CLI yet
  - [ ] Clarify: Not tested on real hardware yet
- **Acceptance Criteria**:
  - Honest feature status
  - No misleading claims
  - Clear integration status

---

## 🏗️ Phase 1: Bazel Build System

### Milestone: `phase-1-bazel`

#### Issue Group 4: Bazel Foundation (Priority: P0)

**Issue #10: Fix Bazel dependency resolution**
- **Labels**: `bazel`, `build`, `P0`
- **Milestone**: `phase-1-bazel`
- **Tasks**:
  - [ ] Remove hardcoded `/root/bazel_local_modules` paths
  - [ ] Use proper Bazel Central Registry (BCR)
  - [ ] Or: Document local module setup for offline builds
  - [ ] Test on clean machine
  - [ ] Update MODULE.bazel with working config
- **Acceptance Criteria**:
  - `bazel build //crates/...` works
  - No hardcoded paths
  - Documentation for setup

**Issue #11: Create Bazel BUILD files for all crates**
- **Labels**: `bazel`, `build`, `P0`
- **Milestone**: `phase-1-bazel`
- **Dependencies**: Issue #10
- **Tasks**:
  - [ ] Generate BUILD.bazel for each crate in `crates/`
  - [ ] Use rules_rust for Rust compilation
  - [ ] Handle inter-crate dependencies
  - [ ] Include test targets
  - [ ] Verify all tests pass via Bazel
- **Acceptance Criteria**:
  - All 14 crates buildable via Bazel
  - `bazel test //crates/...` → 376/376 passing
  - Parallel builds work

**Issue #12: Integrate Coq/OCaml extraction into Bazel**
- **Labels**: `bazel`, `coq`, `build`, `P1`
- **Milestone**: `phase-1-bazel`
- **Dependencies**: Issue #11
- **Tasks**:
  - [ ] Add rules_ocaml to MODULE.bazel
  - [ ] Create BUILD files for `coq/theories/`
  - [ ] Add Coq compilation targets
  - [ ] Add OCaml extraction targets
  - [ ] Build extracted OCaml code
  - [ ] Link extracted code into Rust crates (FFI)
- **Acceptance Criteria**:
  - Coq proofs compile in Bazel
  - OCaml extraction happens automatically
  - Rust can call extracted OCaml (or vice versa)

**Issue #13: Create Bazel WASM → ELF integration test**
- **Labels**: `bazel`, `testing`, `P1`
- **Milestone**: `phase-1-bazel`
- **Dependencies**: Issue #11, #12
- **Tasks**:
  - [ ] Create `integration_test.bzl` rule
  - [ ] Rule: WASM → Synth compiler → ELF → QEMU → Validate
  - [ ] Test with examples/wat/simple_add.wat
  - [ ] Test with examples/led_blink.wat
  - [ ] Add to CI
- **Acceptance Criteria**:
  - `bazel test //integration:all` passes
  - End-to-end compilation works
  - QEMU validation works

#### Issue Group 5: Bazel Toolchains (Priority: P1)

**Issue #14: Create ARM cross-compilation toolchain**
- **Labels**: `bazel`, `toolchain`, `P1`
- **Milestone**: `phase-1-bazel`
- **Tasks**:
  - [ ] Define ARM Cortex-M4 platform in `bazel/platforms/`
  - [ ] Configure arm-none-eabi-gcc toolchain
  - [ ] Create toolchain registration
  - [ ] Test cross-compilation
  - [ ] Document toolchain usage
- **Acceptance Criteria**:
  - Can cross-compile to ARM from Bazel
  - Platform selection works: `bazel build --platforms=//bazel/platforms:cortex_m4`
  - ELF binaries are valid ARM32

**Issue #15: Create QEMU testing infrastructure**
- **Labels**: `bazel`, `testing`, `qemu`, `P1`
- **Milestone**: `phase-1-bazel`
- **Dependencies**: Issue #14
- **Tasks**:
  - [ ] Add QEMU as external tool in MODULE.bazel
  - [ ] Create `qemu_test.bzl` rule
  - [ ] Support running ELF in QEMU
  - [ ] Capture and validate output
  - [ ] Integrate with `bazel test`
- **Acceptance Criteria**:
  - QEMU tests run via `bazel test //examples:qemu_tests`
  - Output validation works
  - Tests fail on incorrect behavior

**Issue #16: Integrate Loom dependency**
- **Labels**: `bazel`, `loom`, `integration`, `P1`
- **Milestone**: `phase-1-bazel`
- **Tasks**:
  - [ ] Add Loom as git dependency in MODULE.bazel
  - [ ] Import Loom ISLE rules
  - [ ] Import Loom optimization passes
  - [ ] Verify Synth can use Loom components
  - [ ] Document integration
- **Acceptance Criteria**:
  - Loom dependency resolves correctly
  - Synth can use Loom optimization rules
  - Build remains hermetic

---

## 🏗️ Phase 2: Minimal Calculator Example

### Milestone: `phase-2-calculator`

#### Issue Group 6: Calculator WASM Implementation (Priority: P0)

**Issue #17: Create calculator WebAssembly module**
- **Labels**: `example`, `wasm`, `P0`
- **Milestone**: `phase-2-calculator`
- **Tasks**:
  - [ ] Write `examples/calculator/calculator.wat`
  - [ ] Implement: add, subtract, multiply, divide (i32 only)
  - [ ] Export functions: `calc_add`, `calc_sub`, `calc_mul`, `calc_div`
  - [ ] Keep it minimal (<100 lines)
  - [ ] Test with wasm2wat roundtrip
  - [ ] Document expected behavior
- **Acceptance Criteria**:
  - Valid WebAssembly module
  - 4 exported functions
  - Unit tests in WASM

**Issue #18: Add calculator unit tests (WASM level)**
- **Labels**: `testing`, `wasm`, `P1`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #17
- **Tasks**:
  - [ ] Create wasm test harness
  - [ ] Test: 2 + 3 = 5
  - [ ] Test: 10 - 4 = 6
  - [ ] Test: 7 * 6 = 42
  - [ ] Test: 20 / 4 = 5
  - [ ] Test edge cases (divide by zero?)
- **Acceptance Criteria**:
  - All tests pass in WASM interpreter
  - Documented test cases

#### Issue Group 7: Synth Compiler CLI (Priority: P0)

**Issue #19: Implement working synth CLI**
- **Labels**: `cli`, `compiler`, `P0`
- **Milestone**: `phase-2-calculator`
- **Tasks**:
  - [ ] Implement `crates/synth-cli/src/main.rs`
  - [ ] Command: `synth compile input.wasm -o output.elf`
  - [ ] Options: `--target cortex-m4`, `--optimize`, `--verify`
  - [ ] Wire up full compilation pipeline
  - [ ] Add progress output
  - [ ] Handle errors gracefully
- **Acceptance Criteria**:
  - `synth compile calculator.wasm -o calculator.elf` works
  - Produces valid ELF binary
  - Error messages are helpful

**Issue #20: Integrate compilation pipeline stages**
- **Labels**: `compiler`, `integration`, `P0`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #19
- **Tasks**:
  - [ ] Wire: Frontend (parse WASM) → Analysis → Optimization → Synthesis → Backend → ELF
  - [ ] Add logging at each stage
  - [ ] Collect statistics (code size, opt time, etc)
  - [ ] Verify intermediate IRs
  - [ ] Add `--dump-ir` flag for debugging
- **Acceptance Criteria**:
  - Full pipeline executes
  - Each stage logs progress
  - Debug output available

**Issue #21: Add Z3 verification pass to pipeline**
- **Labels**: `verification`, `compiler`, `P1`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #20
- **Tasks**:
  - [ ] Integrate synth-verify into pipeline
  - [ ] Verify each WASM→ARM translation
  - [ ] Report verification status
  - [ ] Add `--skip-verify` flag (faster builds)
  - [ ] Handle verification failures gracefully
- **Acceptance Criteria**:
  - Verification runs by default
  - Can be skipped with flag
  - Failures are reported clearly

#### Issue Group 8: Zephyr Integration (Priority: P0)

**Issue #22: Create Zephyr calculator application**
- **Labels**: `zephyr`, `example`, `P0`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #17, #19
- **Tasks**:
  - [ ] Create `examples/calculator-zephyr/`
  - [ ] Copy structure from `examples/zephyr-poc/`
  - [ ] Write `src/main.c`: Menu-driven calculator
  - [ ] User inputs: operation and operands
  - [ ] Call WASM functions (compiled to ARM)
  - [ ] Display results
  - [ ] Add CMakeLists.txt
- **Acceptance Criteria**:
  - Zephyr app compiles
  - Links with Synth-compiled WASM
  - Runs on QEMU

**Issue #23: Integrate Synth into Zephyr build**
- **Labels**: `zephyr`, `build`, `P0`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #22
- **Tasks**:
  - [ ] Add custom CMake function: `add_wasm_module()`
  - [ ] Function invokes: `synth compile calculator.wasm -o calculator.s`
  - [ ] Add calculator.s to Zephyr build
  - [ ] Test build integration
  - [ ] Document usage
- **Acceptance Criteria**:
  - `west build` automatically compiles WASM
  - No manual compilation steps
  - Rebuilds when WASM changes

**Issue #24: Test calculator on QEMU**
- **Labels**: `testing`, `qemu`, `P0`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #23
- **Tasks**:
  - [ ] Build for `qemu_cortex_m3` or `qemu_cortex_m4`
  - [ ] Run: `west build -t run`
  - [ ] Verify output: "Calculator Ready"
  - [ ] Test all 4 operations via serial input
  - [ ] Automate test inputs (expect-like tool?)
- **Acceptance Criteria**:
  - Runs in QEMU
  - All operations work correctly
  - Output matches expectations

**Issue #25: Test calculator on real hardware**
- **Labels**: `testing`, `hardware`, `P1`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #24
- **Tasks**:
  - [ ] Choose board: STM32F4 Discovery, nRF52, or RP2040
  - [ ] Build for target: `west build -b stm32f4_disco`
  - [ ] Flash: `west flash`
  - [ ] Connect serial console
  - [ ] Test interactively
  - [ ] Document hardware setup
- **Acceptance Criteria**:
  - Runs on real hardware
  - All operations work
  - Photos/video of demo

#### Issue Group 9: Documentation & Demos (Priority: P1)

**Issue #26: Write calculator demo documentation**
- **Labels**: `docs`, `example`, `P1`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #24, #25
- **Tasks**:
  - [ ] Create `examples/calculator-zephyr/README.md`
  - [ ] Quick start guide
  - [ ] Prerequisites (Zephyr SDK, etc)
  - [ ] Build instructions
  - [ ] Usage instructions
  - [ ] Screenshots/terminal output
  - [ ] Troubleshooting section
- **Acceptance Criteria**:
  - Complete, clear README
  - Someone can follow it and reproduce

**Issue #27: Create demo video/GIF**
- **Labels**: `demo`, `marketing`, `P2`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #25
- **Tasks**:
  - [ ] Record video: Calculator running on hardware
  - [ ] Show: Compilation, flashing, execution
  - [ ] Keep it under 2 minutes
  - [ ] Add to README and project homepage
  - [ ] Optional: Upload to YouTube
- **Acceptance Criteria**:
  - Professional demo video
  - Shows full workflow
  - Embedded in documentation

**Issue #28: Update project README with calculator example**
- **Labels**: `docs`, `P1`
- **Milestone**: `phase-2-calculator`
- **Dependencies**: Issue #26
- **Tasks**:
  - [ ] Add "Quick Start" section to root README
  - [ ] Link to calculator example
  - [ ] Add "Features" section: What works now
  - [ ] Add "Architecture" section: High-level overview
  - [ ] Add badges: Build status, test coverage
- **Acceptance Criteria**:
  - README is compelling and clear
  - Calculator is front and center
  - Easy to get started

---

## 🏗️ Phase 3: Integration & Documentation

### Milestone: `phase-3-polish`

#### Issue Group 10: CI/CD (Priority: P0)

**Issue #29: Setup GitHub Actions for Rust tests**
- **Labels**: `ci`, `testing`, `P0`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Create `.github/workflows/rust.yml`
  - [ ] Run `cargo test` on every push
  - [ ] Cache dependencies
  - [ ] Matrix: Linux, macOS
  - [ ] Report results in PR
- **Acceptance Criteria**:
  - CI runs automatically
  - Tests must pass to merge
  - Fast feedback (<10 min)

**Issue #30: Setup GitHub Actions for Bazel builds**
- **Labels**: `ci`, `bazel`, `P0`
- **Milestone**: `phase-3-polish`
- **Dependencies**: Issue #11
- **Tasks**:
  - [ ] Create `.github/workflows/bazel.yml`
  - [ ] Run `bazel test //...` on every push
  - [ ] Use remote caching (Bazel Cloud?)
  - [ ] Test ARM cross-compilation
  - [ ] Test integration tests
- **Acceptance Criteria**:
  - Bazel CI works
  - Catches build breakages
  - Reasonable speed

**Issue #31: Add code coverage reporting**
- **Labels**: `ci`, `testing`, `P1`
- **Milestone**: `phase-3-polish`
- **Dependencies**: Issue #29
- **Tasks**:
  - [ ] Integrate with codecov.io or coveralls
  - [ ] Generate coverage reports in CI
  - [ ] Add coverage badge to README
  - [ ] Set minimum coverage threshold (70%?)
  - [ ] Track coverage trends
- **Acceptance Criteria**:
  - Coverage reports on every PR
  - Badge shows current coverage
  - Coverage doesn't regress

#### Issue Group 11: Developer Experience (Priority: P1)

**Issue #32: Create development setup guide**
- **Labels**: `docs`, `developer-experience`, `P1`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Create `docs/DEVELOPMENT.md`
  - [ ] Prerequisites: Rust, Bazel, QEMU, Zephyr
  - [ ] Setup instructions for Linux/macOS
  - [ ] Running tests
  - [ ] Debugging tips
  - [ ] Contribution workflow
- **Acceptance Criteria**:
  - New developer can set up in <30 min
  - All steps documented
  - Tested on clean machine

**Issue #33: Add pre-commit hooks**
- **Labels**: `developer-experience`, `P1`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Install pre-commit framework
  - [ ] Add: `cargo fmt --check`
  - [ ] Add: `cargo clippy`
  - [ ] Add: `bazel test //crates/synth-verify/...` (fast subset)
  - [ ] Document in CONTRIBUTING.md
- **Acceptance Criteria**:
  - Hooks catch issues before commit
  - Fast (<30 seconds)
  - Easy to install

**Issue #34: Create debugging guide**
- **Labels**: `docs`, `developer-experience`, `P1`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Create `docs/DEBUGGING.md`
  - [ ] How to debug WASM input
  - [ ] How to inspect IR at each stage
  - [ ] How to debug ARM output
  - [ ] How to use QEMU with GDB
  - [ ] How to debug on real hardware
  - [ ] Common issues and solutions
- **Acceptance Criteria**:
  - Covers full debugging workflow
  - Screenshots/examples
  - Tested procedures

#### Issue Group 12: Final Documentation (Priority: P1)

**Issue #35: Write architecture documentation**
- **Labels**: `docs`, `architecture`, `P1`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Update `ARCHITECTURE.md` to reflect current reality
  - [ ] Compilation pipeline diagram
  - [ ] Crate dependency diagram
  - [ ] Data flow through pipeline
  - [ ] Verification approach
  - [ ] Integration with Loom
  - [ ] Keep it concise (<5 pages)
- **Acceptance Criteria**:
  - Accurate, up-to-date architecture
  - Clear diagrams
  - Matches implementation

**Issue #36: Create API documentation**
- **Labels**: `docs`, `api`, `P1`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Add rustdoc comments to all public APIs
  - [ ] Include examples in doc comments
  - [ ] Generate docs: `cargo doc --no-deps --open`
  - [ ] Publish to docs.rs (or GitHub Pages)
  - [ ] Link from README
- **Acceptance Criteria**:
  - All public APIs documented
  - Examples provided
  - Docs published online

**Issue #37: Write user guide**
- **Labels**: `docs`, `P1`
- **Milestone**: `phase-3-polish`
- **Tasks**:
  - [ ] Create `docs/USER_GUIDE.md`
  - [ ] Introduction: What is Synth?
  - [ ] Installation
  - [ ] Your first WASM app
  - [ ] Compilation options
  - [ ] Target platforms
  - [ ] Troubleshooting
  - [ ] FAQ
- **Acceptance Criteria**:
  - Complete user guide
  - Clear for beginners
  - Covers common use cases

**Issue #38: Prepare release v0.1.0**
- **Labels**: `release`, `P1`
- **Milestone**: `phase-3-polish`
- **Dependencies**: All Phase 3 issues
- **Tasks**:
  - [ ] Tag: `v0.1.0`
  - [ ] Write CHANGELOG.md
  - [ ] Create GitHub Release
  - [ ] Include: Calculator demo, docs, binaries
  - [ ] Announcement blog post
  - [ ] Share on Hacker News / Reddit
- **Acceptance Criteria**:
  - Tagged release
  - Downloadable artifacts
  - Announcement published

---

## 📋 GitHub Labels

### Priority Labels
- `P0` - Critical, blocking
- `P1` - High priority
- `P2` - Medium priority
- `P3` - Low priority

### Type Labels
- `bug` - Something is broken
- `enhancement` - New feature
- `refactor` - Code restructuring
- `docs` - Documentation
- `testing` - Test infrastructure
- `ci` - Continuous integration
- `build` - Build system

### Component Labels
- `bazel` - Bazel build system
- `cargo` - Cargo/Rust build
- `compiler` - Core compiler
- `cli` - Command-line interface
- `verification` - Formal verification
- `coq` - Coq proofs
- `zephyr` - Zephyr integration
- `qemu` - QEMU testing
- `hardware` - Real hardware
- `loom` - Loom integration

### Area Labels
- `architecture` - System architecture
- `developer-experience` - Dev tools and workflow
- `example` - Example code
- `integration` - Component integration
- `cleanup` - Code/doc cleanup

---

## 📊 GitHub Milestones

1. **phase-0-cleanup** (Week 1)
   - Due: 2025-11-28
   - 9 issues
   - Goal: Clean, organized repository

2. **phase-1-bazel** (Week 2-3)
   - Due: 2025-12-12
   - 7 issues
   - Goal: Working Bazel build

3. **phase-2-calculator** (Week 4-5)
   - Due: 2025-12-26
   - 12 issues
   - Goal: Calculator demo on Zephyr

4. **phase-3-polish** (Week 6)
   - Due: 2026-01-02
   - 10 issues
   - Goal: Release v0.1.0

**Total: 38 issues across 4 milestones**

---

## 🚀 Success Metrics

### Phase 0 Complete
- ✅ ≤5 markdown files at root
- ✅ Clear documentation structure
- ✅ Synth/Loom relationship documented
- ✅ Realistic roadmap

### Phase 1 Complete
- ✅ `bazel build //...` works
- ✅ `bazel test //...` → 376/376 passing
- ✅ Coq extraction integrated
- ✅ Integration tests pass

### Phase 2 Complete
- ✅ `synth compile calculator.wasm -o calculator.elf` works
- ✅ Calculator runs in QEMU
- ✅ Calculator runs on real hardware
- ✅ Demo video created

### Phase 3 Complete
- ✅ CI/CD fully operational
- ✅ All documentation complete
- ✅ v0.1.0 released
- ✅ Public announcement made

---

## 📝 Next Steps

1. Review this plan
2. Create GitHub labels: `gh label create ...`
3. Create GitHub milestones: `gh milestone create ...`
4. Create GitHub issues: `gh issue create ...`
5. Create GitHub project board
6. Start with Phase 0, Issue #1

---

**Let's build this systematically, one issue at a time!**
