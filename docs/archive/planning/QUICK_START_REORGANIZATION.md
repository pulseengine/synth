# Quick Start: Synth Reorganization

This guide will help you set up the systematic reorganization of Synth.

## Overview

We're transforming Synth from a research prototype into a production-ready WebAssembly compiler for embedded systems, following a systematic 4-phase approach:

1. **Phase 0**: Organization & Cleanup (1 week)
2. **Phase 1**: Bazel Build System (2-3 weeks)
3. **Phase 2**: Calculator Demo on Zephyr (2-3 weeks)
4. **Phase 3**: Polish & Release v0.1.0 (1 week)

---

## Step 1: Review the Plan

Read the comprehensive plan:
```bash
cat SYSTEMATIC_REORGANIZATION_PLAN.md
```

This document contains:
- Detailed breakdown of all 4 phases
- 38 issues across 4 milestones
- Labels, acceptance criteria, dependencies
- Success metrics for each phase

---

## Step 2: Set Up GitHub Infrastructure

### A. Create Labels

Labels help organize and prioritize issues:

```bash
./scripts/setup_github_project.sh
```

This creates:
- **Priority labels**: P0 (critical), P1 (high), P2 (medium), P3 (low)
- **Type labels**: bug, enhancement, refactor, docs, testing, ci, build
- **Component labels**: bazel, compiler, cli, verification, coq, zephyr, qemu, hardware
- **Area labels**: architecture, developer-experience, example, integration, cleanup

### B. Create Milestones

The script also creates 4 milestones with due dates:
- `phase-0-cleanup` (due in 1 week)
- `phase-1-bazel` (due in 3 weeks)
- `phase-2-calculator` (due in 5 weeks)
- `phase-3-polish` (due in 6 weeks)

### C. Create Issues

Create all 38 issues:

```bash
./scripts/create_github_issues.sh
```

This creates structured issues for:
- **Phase 0**: 9 issues (documentation cleanup, crate refactoring, roadmap)
- **Phase 1**: 7 issues (Bazel build system, toolchains, integration)
- **Phase 2**: 12 issues (calculator WASM, CLI, Zephyr integration)
- **Phase 3**: 10 issues (CI/CD, documentation, release prep)

---

## Step 3: Create GitHub Project Board

Create a project board to track progress:

```bash
gh project create \
  --title "Synth Reorganization" \
  --owner @me
```

Then add issues to the project:

1. Go to: https://github.com/pulseengine/Synth/projects
2. Open "Synth Reorganization" project
3. Click "Add items from repository"
4. Add all issues with milestone `phase-0-cleanup`, `phase-1-bazel`, etc.

Or via CLI:
```bash
# Get project number (e.g., 1)
gh project list --owner @me

# Add issues to project
gh project item-add <project-number> --owner @me --url <issue-url>
```

### Organize the Board

Create columns:
- **Backlog** - Not started
- **In Progress** - Currently working on
- **Review** - Needs review
- **Done** - Completed

---

## Step 4: Start with Phase 0

Begin with Issue #1:

```bash
gh issue list --milestone "phase-0-cleanup" --label "P0"
```

### Issue #1: Consolidate root-level documentation

**Goal**: Reduce 48+ markdown files at root to ≤5 files.

**Action plan**:
1. Create docs directory structure
2. Move session notes to `docs/sessions/` (or delete after extracting insights)
3. Consolidate Bazel docs to `docs/build-systems/BAZEL.md`
4. Consolidate Sail docs to `docs/research/SAIL_INTEGRATION.md`
5. Keep only: README, ARCHITECTURE, CHANGELOG, LICENSE, CONTRIBUTING at root
6. Update README with navigation

**Estimate**: 2-3 hours

---

## Step 5: Track Progress

### View Current Status

```bash
# View all issues
gh issue list

# View by milestone
gh issue list --milestone "phase-0-cleanup"

# View by label
gh issue list --label "P0"

# View assigned to you
gh issue list --assignee @me
```

### Update Issue Status

```bash
# Start working on an issue
gh issue edit <issue-number> --add-label "in-progress"

# Mark as done
gh issue close <issue-number> --comment "Completed! Summary: ..."
```

### Check Milestone Progress

```bash
gh api repos/:owner/:repo/milestones | jq '.[] | {title, open_issues, closed_issues}'
```

---

## Step 6: Phase-by-Phase Workflow

### Phase 0: Cleanup (Week 1)

**Goal**: Clean, organized repository

**Daily workflow**:
1. Pick highest priority P0 issue
2. Create feature branch: `git checkout -b phase0/issue-1-consolidate-docs`
3. Make changes
4. Commit with clear message: `feat(docs): Consolidate root-level documentation (#1)`
5. Push and create PR
6. Review, merge, close issue
7. Move to next issue

**Success metrics**:
- ✅ ≤5 markdown files at root
- ✅ Clear documentation structure
- ✅ Synth/Loom relationship documented
- ✅ Realistic roadmap

### Phase 1: Bazel (Week 2-3)

**Goal**: Working Bazel build

**Key issues**:
1. Fix dependency resolution
2. Create BUILD files
3. Integrate Coq/OCaml
4. Integration tests
5. ARM toolchain
6. QEMU infrastructure

**Success metrics**:
- ✅ `bazel build //...` works
- ✅ `bazel test //...` → 376/376 passing
- ✅ Integration tests pass

### Phase 2: Calculator (Week 4-5)

**Goal**: Demo running on Zephyr

**Key issues**:
1. Create calculator.wat
2. Implement CLI
3. Zephyr integration
4. QEMU testing
5. Real hardware testing
6. Documentation

**Success metrics**:
- ✅ `synth compile calculator.wasm -o calculator.elf` works
- ✅ Runs in QEMU
- ✅ Runs on real hardware
- ✅ Demo video created

### Phase 3: Polish (Week 6)

**Goal**: Release v0.1.0

**Key issues**:
1. CI/CD setup
2. Documentation
3. API docs
4. User guide
5. Release prep

**Success metrics**:
- ✅ CI/CD operational
- ✅ All docs complete
- ✅ v0.1.0 released
- ✅ Public announcement

---

## Tips for Success

### 1. **One Issue at a Time**
Focus on completing one issue fully before moving to the next.

### 2. **Follow Dependencies**
Some issues depend on others. Check the "Dependencies" section in each issue.

### 3. **Small Commits**
Make small, focused commits with clear messages.

### 4. **Document as You Go**
Update documentation when you make changes, not later.

### 5. **Test Continuously**
Run `cargo test` frequently. Don't break existing tests.

### 6. **Ask for Help**
If stuck, comment on the issue or ask in discussions.

### 7. **Celebrate Progress**
Each closed issue is progress! Update the project board and track your velocity.

---

## Troubleshooting

### GitHub CLI Not Working

```bash
# Check authentication
gh auth status

# Re-authenticate if needed
gh auth login
```

### Script Errors

```bash
# Make scripts executable
chmod +x scripts/*.sh

# Check for dependencies
which gh  # GitHub CLI
which bazel  # Bazel build system
```

### Bazel Issues

```bash
# Clean Bazel cache
bazel clean --expunge

# Check Bazel version
bazel version  # Should be 7.0+
```

---

## Communication

### Daily Updates

Post brief updates in GitHub Discussions:
- What you worked on
- What's next
- Any blockers

### Weekly Summary

At end of each week:
1. Review completed issues
2. Update project board
3. Adjust timeline if needed
4. Post summary in Discussions

---

## Questions?

- **Issues**: https://github.com/pulseengine/Synth/issues
- **Discussions**: https://github.com/pulseengine/Synth/discussions
- **Loom**: https://github.com/pulseengine/loom

---

## Ready?

Let's start! 🚀

```bash
# Step 1: Set up GitHub infrastructure
./scripts/setup_github_project.sh

# Step 2: Create all issues
./scripts/create_github_issues.sh

# Step 3: Start Phase 0, Issue #1
gh issue view 1
```

**First task**: Consolidate root-level documentation (Issue #1)

Good luck! Let's build something great, systematically. 💪
