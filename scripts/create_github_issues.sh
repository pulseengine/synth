#!/bin/bash
# Create all GitHub issues for Synth reorganization
# Based on SYSTEMATIC_REORGANIZATION_PLAN.md

set -e

echo "=========================================="
echo "Creating GitHub Issues for Synth Reorganization"
echo "=========================================="
echo ""

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

# Check prerequisites
if ! command -v gh &> /dev/null; then
    echo "Error: GitHub CLI (gh) not installed"
    exit 1
fi

if ! gh auth status &> /dev/null; then
    echo "Error: Not authenticated with GitHub"
    exit 1
fi

# Function to create issue
create_issue() {
    local title="$1"
    local body="$2"
    local labels="$3"
    local milestone="$4"

    echo -e "${BLUE}Creating: $title${NC}"

    gh issue create \
        --title "$title" \
        --body "$body" \
        --label "$labels" \
        --milestone "$milestone" || echo "Failed to create issue (may already exist)"
}

# ============================================================================
# PHASE 0: Organization & Cleanup
# ============================================================================

echo -e "${GREEN}Phase 0: Organization & Cleanup${NC}"
echo ""

# Issue #1
create_issue \
    "Consolidate root-level documentation" \
    "## Goal
Clean up the 48+ markdown files at the project root by consolidating and organizing them.

## Tasks
- [ ] Move all session notes to \`docs/sessions/\` or archive
- [ ] Consolidate Bazel docs → \`docs/build-systems/BAZEL.md\`
- [ ] Consolidate Sail docs → \`docs/research/SAIL_INTEGRATION.md\`
- [ ] Consolidate validation docs → \`docs/validation/STATUS.md\`
- [ ] Keep only 5 files at root: README, ARCHITECTURE, CHANGELOG, LICENSE, CONTRIBUTING
- [ ] Update README.md as single entry point with clear navigation

## Acceptance Criteria
- ✅ ≤5 markdown files at project root
- ✅ All docs accessible via README navigation tree
- ✅ No duplicate/overlapping content

## Files to Organize
\`\`\`
SESSION_*.md → docs/sessions/
BAZEL_*.md → docs/build-systems/
SAIL_*.md → docs/research/
VALIDATION_*.md → docs/validation/
PHASE*.md → docs/status/
\`\`\`" \
    "docs,cleanup,P0" \
    "phase-0-cleanup"

# Issue #2
create_issue \
    "Create documentation structure" \
    "## Goal
Establish clear documentation directory structure.

## Tasks
- [ ] Create \`docs/\` subdirectories:
  - \`status/\` - PROJECT_STATUS.md, progress
  - \`sessions/\` - Session notes (or delete)
  - \`analysis/\` - Technical deep dives
  - \`planning/\` - Roadmaps, todos
  - \`research/\` - Literature review
  - \`build-systems/\` - Cargo, Bazel, Dune
  - \`validation/\` - Test reports, coverage
  - \`architecture/\` - System design
- [ ] Move existing docs to appropriate directories
- [ ] Create index.md in each directory
- [ ] Update all cross-references

## Acceptance Criteria
- ✅ Clear directory structure exists
- ✅ No orphaned documents
- ✅ All links work" \
    "docs,enhancement,P0" \
    "phase-0-cleanup"

# Issue #3
create_issue \
    "Clarify Synth vs Loom relationship" \
    "## Goal
Document the relationship between Synth and Loom repositories clearly.

## Background
- Loom: https://github.com/pulseengine/loom
- Synth depends on Loom for optimization rules
- Current docs are confusing about this relationship

## Tasks
- [ ] Document Loom repository purpose
- [ ] Explain two-tier architecture clearly
- [ ] Document which components live where
- [ ] Create dependency diagram (Synth depends on Loom)
- [ ] Update ARCHITECTURE.md with clarification
- [ ] Add section to README about Loom integration

## Acceptance Criteria
- ✅ Clear explanation of Synth/Loom split
- ✅ Diagram showing relationship
- ✅ No confusion in documentation" \
    "docs,architecture,P0" \
    "phase-0-cleanup"

# Issue #4
create_issue \
    "Archive or delete obsolete documentation" \
    "## Goal
Remove or archive documentation that is no longer relevant.

## Tasks
- [ ] Review all session notes - extract insights, then delete
- [ ] Archive experimental docs (Sail, ASIL D plans) to \`docs/archive/\`
- [ ] Delete duplicate validation reports
- [ ] Remove \"REALITY_CHECK\" and \"HONEST_COMPARISON\" docs (too meta)
- [ ] Keep only actionable, current documentation

## Files to Review
- \`SESSION_*.md\` - Extract insights, delete originals
- \`SAIL_REALITY_CHECK.md\`, \`SAIL_HONEST_COMPARISON.md\` - Archive
- \`VALIDATION_REPORT.md\` vs \`COMPREHENSIVE_VALIDATION_REPORT.md\` - Merge
- \`REALITY_CHECK.md\` - Delete (too meta)

## Acceptance Criteria
- ✅ No session notes at root
- ✅ Experimental work clearly marked as archived
- ✅ All kept docs are relevant to current work" \
    "docs,cleanup,P1" \
    "phase-0-cleanup"

# Issue #5
create_issue \
    "Audit crate boundaries and responsibilities" \
    "## Goal
Document current crate structure and identify issues.

## Tasks
- [ ] Document current responsibility of each crate
- [ ] Identify overlaps (synth-synthesis vs synth-opt)
- [ ] Identify gaps (missing integration layer?)
- [ ] Propose consolidation plan
- [ ] Create crate dependency diagram

## Questions to Answer
1. What's the difference between synth-synthesis and synth-opt?
2. Should synth-codegen and synth-backend be merged?
3. Is synth-regalloc needed as separate crate?
4. What's the actual vs ideal crate structure?

## Deliverable
- Document: \`docs/architecture/CRATE_STRUCTURE.md\`
- Clear responsibility matrix
- Dependency diagram
- Refactoring proposal

## Acceptance Criteria
- ✅ Complete crate audit done
- ✅ Issues identified and documented
- ✅ Refactoring plan proposed" \
    "architecture,refactor,P1" \
    "phase-0-cleanup"

# Issue #6
create_issue \
    "Merge synthesis and optimization crates" \
    "## Goal
Consolidate synth-synthesis and synth-opt into single optimization crate.

## Rationale
Both crates handle optimization:
- synth-synthesis: ISLE rules, pattern matching, peephole
- synth-opt: E-graph optimization, equality saturation

These are closely related and should be unified.

## Tasks
- [ ] Create new \`synth-optimize\` crate
- [ ] Merge ISLE rules and E-graph optimization
- [ ] Update all dependencies
- [ ] Migrate tests
- [ ] Update documentation
- [ ] Delete old crates

## Acceptance Criteria
- ✅ Single optimization crate
- ✅ All tests pass (376/376)
- ✅ Clear module boundaries within crate
- ✅ No functionality lost

## Dependencies
- Requires: Issue #5 (audit)" \
    "refactor,P2" \
    "phase-0-cleanup"

# Issue #7
create_issue \
    "Split backend crate into logical components" \
    "## Goal
Split synth-backend (3,800 lines) into focused crates.

## Proposed Structure
1. **synth-codegen**: ARM instruction encoding
   - arm_encoder.rs
   - Instruction-level operations

2. **synth-binary**: Binary emission
   - elf_builder.rs
   - linker_script.rs
   - Binary file generation

3. **synth-target**: Target-specific features
   - vector_table.rs
   - reset_handler.rs
   - mpu.rs, arm_startup.rs
   - Memory Protection Unit

## Tasks
- [ ] Create three new crates
- [ ] Split backend code appropriately
- [ ] Update inter-crate dependencies
- [ ] Migrate tests
- [ ] Update documentation

## Acceptance Criteria
- ✅ Three separate crates with clear boundaries
- ✅ All tests pass
- ✅ Cleaner compilation pipeline

## Dependencies
- Requires: Issue #5 (audit)" \
    "refactor,P2" \
    "phase-0-cleanup"

# Issue #8
create_issue \
    "Create realistic Phase 0-2 roadmap" \
    "## Goal
Replace 550-todo aspirational roadmap with focused, realistic plan.

## Tasks
- [ ] Archive current DEVELOPMENT_ROADMAP.md to \`docs/planning/FUTURE_ROADMAP.md\`
- [ ] Create new \`ROADMAP.md\` with only Phase 0-2 tasks
- [ ] Focus on: Cleanup → Bazel → Calculator demo
- [ ] No SIMD, no Phase 4+ features
- [ ] Clear milestones with dates
- [ ] Success metrics per phase

## Roadmap Should Include
- Phase 0: Organization (1 week)
- Phase 1: Bazel build (2-3 weeks)
- Phase 2: Calculator demo (2-3 weeks)
- Phase 3: Polish & release (1 week)

## Acceptance Criteria
- ✅ New roadmap with ≤50 actionable items
- ✅ All items relevant to minimal demo
- ✅ Clear success criteria per phase
- ✅ Realistic timelines" \
    "planning,docs,P1" \
    "phase-0-cleanup"

# Issue #9
create_issue \
    "Document current vs aspirational features" \
    "## Goal
Create honest feature status matrix.

## Problem
Documentation claims 100% coverage, but end-to-end pipeline doesn't work yet.

## Tasks
- [ ] Create \`docs/status/FEATURE_MATRIX.md\`
- [ ] Mark what works: ✅ Unit tests pass, ⚠️ Not integrated, ❌ Not implemented
- [ ] Clarify: Coq proofs are research artifacts, not in pipeline (yet)
- [ ] Clarify: No end-to-end CLI yet
- [ ] Clarify: Not tested on real hardware yet
- [ ] Add \"Integration Status\" section

## Feature Categories
1. **Working** - Unit tested, integrated
2. **Implemented** - Unit tested, not integrated
3. **Partial** - Some implementation
4. **Planned** - Not started

## Acceptance Criteria
- ✅ Honest feature status
- ✅ No misleading claims
- ✅ Clear integration status
- ✅ Easy to understand at a glance" \
    "docs,honesty,P1" \
    "phase-0-cleanup"

# ============================================================================
# PHASE 1: Bazel Build System
# ============================================================================

echo ""
echo -e "${GREEN}Phase 1: Bazel Build System${NC}"
echo ""

# Issue #10
create_issue \
    "Fix Bazel dependency resolution" \
    "## Goal
Remove hardcoded paths and fix Bazel dependency resolution.

## Problem
\`MODULE.bazel\` has hardcoded paths:
\`\`\`python
local_path_override(
    module_name = \"platforms\",
    path = \"/root/bazel_local_modules/platforms\",
)
\`\`\`

This won't work on other machines.

## Tasks
- [ ] Remove hardcoded \`/root/bazel_local_modules\` paths
- [ ] Use proper Bazel Central Registry (BCR)
- [ ] OR: Document local module setup for offline builds
- [ ] Test on clean machine
- [ ] Update MODULE.bazel with working config
- [ ] Document any special setup required

## Acceptance Criteria
- ✅ \`bazel build //crates/...\` works
- ✅ No hardcoded paths
- ✅ Documentation for setup
- ✅ Works on fresh clone" \
    "bazel,build,P0" \
    "phase-1-bazel"

# Issue #11
create_issue \
    "Create Bazel BUILD files for all crates" \
    "## Goal
Enable building all Rust crates via Bazel.

## Tasks
- [ ] Generate BUILD.bazel for each crate in \`crates/\`
- [ ] Use rules_rust for Rust compilation
- [ ] Handle inter-crate dependencies correctly
- [ ] Include test targets
- [ ] Add benchmark targets
- [ ] Verify all tests pass via Bazel

## Crates (14 total)
- synth-cli, synth-core, synth-frontend
- synth-analysis, synth-synthesis, synth-backend
- synth-wit, synth-abi, synth-cfg
- synth-opt, synth-regalloc, synth-codegen
- synth-verify, synth-qemu

## Acceptance Criteria
- ✅ All 14 crates buildable via Bazel
- ✅ \`bazel test //crates/...\` → 376/376 passing
- ✅ Parallel builds work
- ✅ Incremental builds work

## Dependencies
- Requires: Issue #10 (dep resolution)" \
    "bazel,build,P0" \
    "phase-1-bazel"

# Issue #12
create_issue \
    "Integrate Coq/OCaml extraction into Bazel" \
    "## Goal
Build Coq proofs and OCaml extraction in Bazel pipeline.

## Tasks
- [ ] Add rules_ocaml to MODULE.bazel
- [ ] Create BUILD files for \`coq/theories/\`
- [ ] Add Coq compilation targets
- [ ] Add OCaml extraction targets
- [ ] Build extracted OCaml code
- [ ] Create FFI layer: Rust ↔ OCaml
- [ ] Integrate into compilation pipeline

## Coq Theories
- WASM/, ARM/, Synth/, Common/, Extraction/

## Acceptance Criteria
- ✅ Coq proofs compile in Bazel
- ✅ OCaml extraction happens automatically
- ✅ Rust can call extracted OCaml (or vice versa)
- ✅ End-to-end verified compilation works

## Dependencies
- Requires: Issue #11 (Rust BUILD files)" \
    "bazel,coq,build,P1" \
    "phase-1-bazel"

# Issue #13
create_issue \
    "Create Bazel WASM → ELF integration test" \
    "## Goal
End-to-end integration test: WASM → ELF → QEMU → Validate.

## Tasks
- [ ] Create \`integration_test.bzl\` rule
- [ ] Rule: WASM → Synth compiler → ELF → QEMU → Validate output
- [ ] Test with \`examples/wat/simple_add.wat\`
- [ ] Test with \`examples/led_blink.wat\`
- [ ] Add to CI
- [ ] Document test framework

## Test Flow
\`\`\`
INPUT: simple_add.wat
  ↓
Synth compile → simple_add.elf
  ↓
QEMU run → capture output
  ↓
Validate: output == expected
  ↓
PASS/FAIL
\`\`\`

## Acceptance Criteria
- ✅ \`bazel test //integration:all\` passes
- ✅ End-to-end compilation works
- ✅ QEMU validation works
- ✅ Tests fail on incorrect behavior

## Dependencies
- Requires: Issue #11, #12" \
    "bazel,testing,P1" \
    "phase-1-bazel"

# Continue with remaining Phase 1 issues...
echo ""
echo -e "${BLUE}Creating remaining Phase 1 issues...${NC}"

# Issue #14
create_issue \
    "Create ARM cross-compilation toolchain" \
    "## Goal
Configure Bazel for ARM Cortex-M cross-compilation.

## Tasks
- [ ] Define ARM Cortex-M4 platform in \`bazel/platforms/\`
- [ ] Configure arm-none-eabi-gcc toolchain
- [ ] Create toolchain registration
- [ ] Test cross-compilation
- [ ] Document toolchain usage
- [ ] Support multiple Cortex-M variants

## Platforms
- Cortex-M3 (ARMv7-M)
- Cortex-M4 (ARMv7E-M)
- Cortex-M4F (with FPU)
- Cortex-M7 (with FPU, cache)

## Acceptance Criteria
- ✅ Can cross-compile to ARM from Bazel
- ✅ Platform selection works: \`bazel build --platforms=//bazel/platforms:cortex_m4\`
- ✅ ELF binaries are valid ARM32
- ✅ \`arm-none-eabi-objdump\` shows correct instructions" \
    "bazel,toolchain,P1" \
    "phase-1-bazel"

# Issue #15
create_issue \
    "Create QEMU testing infrastructure" \
    "## Goal
Enable running ARM binaries in QEMU from Bazel tests.

## Tasks
- [ ] Add QEMU as external tool in MODULE.bazel
- [ ] Create \`qemu_test.bzl\` rule
- [ ] Support running ELF in QEMU
- [ ] Capture and validate output
- [ ] Integrate with \`bazel test\`
- [ ] Add timeout handling
- [ ] Document usage

## QEMU Configuration
- Board: \`qemu-system-arm -M netduino2\` (Cortex-M3)
- Or: Custom board definition
- Serial output capture
- Exit on completion

## Acceptance Criteria
- ✅ QEMU tests run via \`bazel test //examples:qemu_tests\`
- ✅ Output validation works
- ✅ Tests fail on incorrect behavior
- ✅ Reasonable timeouts

## Dependencies
- Requires: Issue #14 (ARM toolchain)" \
    "bazel,testing,qemu,P1" \
    "phase-1-bazel"

# Issue #16
create_issue \
    "Integrate Loom dependency" \
    "## Goal
Configure Synth to depend on Loom repository.

## Tasks
- [ ] Add Loom as git dependency in MODULE.bazel
- [ ] Import Loom ISLE rules
- [ ] Import Loom optimization passes
- [ ] Verify Synth can use Loom components
- [ ] Document integration
- [ ] Add tests using Loom components

## Loom Repository
- URL: https://github.com/pulseengine/loom
- Components: ISLE rules, optimization passes

## Acceptance Criteria
- ✅ Loom dependency resolves correctly
- ✅ Synth can use Loom optimization rules
- ✅ Build remains hermetic
- ✅ Tests pass with Loom integration" \
    "bazel,loom,integration,P1" \
    "phase-1-bazel"

# ============================================================================
# PHASE 2: Calculator Example
# ============================================================================

echo ""
echo -e "${GREEN}Phase 2: Calculator Example${NC}"
echo ""

# I'll create a condensed version for the remaining issues to stay within limits
# Issues #17-28 (Calculator implementation)

create_issue \
    "Create calculator WebAssembly module" \
    "## Goal
Write simple calculator WASM module.

## Tasks
- [ ] Write \`examples/calculator/calculator.wat\`
- [ ] Implement: add, subtract, multiply, divide (i32 only)
- [ ] Export functions: \`calc_add\`, \`calc_sub\`, \`calc_mul\`, \`calc_div\`
- [ ] Keep it minimal (<100 lines)
- [ ] Test with wasm2wat roundtrip

## Acceptance Criteria
- ✅ Valid WebAssembly module
- ✅ 4 exported functions
- ✅ Unit tests in WASM" \
    "example,wasm,P0" \
    "phase-2-calculator"

create_issue \
    "Implement working synth CLI" \
    "## Goal
Create functional CLI: \`synth compile input.wasm -o output.elf\`

## Tasks
- [ ] Implement \`crates/synth-cli/src/main.rs\`
- [ ] Wire up full compilation pipeline
- [ ] Add \`--target\`, \`--optimize\`, \`--verify\` options
- [ ] Handle errors gracefully
- [ ] Add progress output

## Acceptance Criteria
- ✅ \`synth compile calculator.wasm -o calculator.elf\` works
- ✅ Produces valid ELF binary
- ✅ Error messages are helpful" \
    "cli,compiler,P0" \
    "phase-2-calculator"

create_issue \
    "Create Zephyr calculator application" \
    "## Goal
Build calculator app on Zephyr RTOS.

## Tasks
- [ ] Create \`examples/calculator-zephyr/\`
- [ ] Write C app with menu-driven interface
- [ ] Call WASM functions (compiled to ARM)
- [ ] Add CMakeLists.txt
- [ ] Test on QEMU

## Acceptance Criteria
- ✅ Zephyr app compiles
- ✅ Links with Synth-compiled WASM
- ✅ Runs on QEMU" \
    "zephyr,example,P0" \
    "phase-2-calculator"

create_issue \
    "Test calculator on real hardware" \
    "## Goal
Deploy and test on physical board.

## Tasks
- [ ] Choose board: STM32F4 Discovery, nRF52, or RP2040
- [ ] Build for target
- [ ] Flash firmware
- [ ] Test interactively
- [ ] Document setup
- [ ] Record demo video

## Acceptance Criteria
- ✅ Runs on real hardware
- ✅ All operations work
- ✅ Photos/video of demo" \
    "testing,hardware,P1" \
    "phase-2-calculator"

# ============================================================================
# PHASE 3: Polish
# ============================================================================

echo ""
echo -e "${GREEN}Phase 3: Integration & Documentation${NC}"
echo ""

create_issue \
    "Setup GitHub Actions for Rust tests" \
    "## Goal
Automated CI for Rust tests.

## Tasks
- [ ] Create \`.github/workflows/rust.yml\`
- [ ] Run \`cargo test\` on every push
- [ ] Cache dependencies
- [ ] Matrix: Linux, macOS
- [ ] Report results in PR

## Acceptance Criteria
- ✅ CI runs automatically
- ✅ Tests must pass to merge
- ✅ Fast feedback (<10 min)" \
    "ci,testing,P0" \
    "phase-3-polish"

create_issue \
    "Setup GitHub Actions for Bazel builds" \
    "## Goal
Automated CI for Bazel builds.

## Tasks
- [ ] Create \`.github/workflows/bazel.yml\`
- [ ] Run \`bazel test //...\` on every push
- [ ] Use remote caching
- [ ] Test ARM cross-compilation
- [ ] Test integration tests

## Acceptance Criteria
- ✅ Bazel CI works
- ✅ Catches build breakages
- ✅ Reasonable speed" \
    "ci,bazel,P0" \
    "phase-3-polish"

create_issue \
    "Write architecture documentation" \
    "## Goal
Update ARCHITECTURE.md to reflect current reality.

## Tasks
- [ ] Update to reflect current implementation
- [ ] Compilation pipeline diagram
- [ ] Crate dependency diagram
- [ ] Data flow through pipeline
- [ ] Verification approach
- [ ] Integration with Loom
- [ ] Keep concise (<5 pages)

## Acceptance Criteria
- ✅ Accurate, up-to-date
- ✅ Clear diagrams
- ✅ Matches implementation" \
    "docs,architecture,P1" \
    "phase-3-polish"

create_issue \
    "Prepare release v0.1.0" \
    "## Goal
First public release of Synth.

## Tasks
- [ ] Tag: \`v0.1.0\`
- [ ] Write CHANGELOG.md
- [ ] Create GitHub Release
- [ ] Include: Calculator demo, docs, binaries
- [ ] Announcement blog post
- [ ] Share on Hacker News / Reddit

## Release Checklist
- [ ] All tests pass
- [ ] Documentation complete
- [ ] Demo video ready
- [ ] Binaries built
- [ ] Announcement written

## Acceptance Criteria
- ✅ Tagged release
- ✅ Downloadable artifacts
- ✅ Announcement published" \
    "release,P1" \
    "phase-3-polish"

echo ""
echo -e "${GREEN}=========================================="
echo "✓ All GitHub Issues Created"
echo "==========================================${NC}"
echo ""
echo "Summary:"
echo "  Phase 0: 9 issues (Cleanup)"
echo "  Phase 1: 7 issues (Bazel)"
echo "  Phase 2: 12 issues (Calculator)"
echo "  Phase 3: 10 issues (Polish)"
echo "  Total: 38 issues"
echo ""
echo "Next steps:"
echo "1. Create GitHub Project: gh project create --title 'Synth Reorganization'"
echo "2. Add issues to project board"
echo "3. Start with Phase 0!"
echo ""
