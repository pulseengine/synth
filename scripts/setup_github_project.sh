#!/bin/bash
# Setup GitHub Project Infrastructure for Synth Reorganization
# This script creates labels, milestones, and issues for the systematic reorganization plan

set -e  # Exit on error

echo "=========================================="
echo "Synth GitHub Project Setup"
echo "=========================================="
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Check if gh CLI is installed
if ! command -v gh &> /dev/null; then
    echo -e "${RED}Error: GitHub CLI (gh) is not installed${NC}"
    echo "Install from: https://cli.github.com/"
    exit 1
fi

# Check if authenticated
if ! gh auth status &> /dev/null; then
    echo -e "${RED}Error: Not authenticated with GitHub${NC}"
    echo "Run: gh auth login"
    exit 1
fi

echo -e "${GREEN}✓ GitHub CLI is ready${NC}"
echo ""

# ============================================================================
# Step 1: Create Labels
# ============================================================================

echo -e "${BLUE}Step 1: Creating Labels${NC}"
echo "----------------------------------------"

# Priority labels
gh label create "P0" --description "Critical, blocking" --color "d73a4a" --force || true
gh label create "P1" --description "High priority" --color "e99695" --force || true
gh label create "P2" --description "Medium priority" --color "f9d0c4" --force || true
gh label create "P3" --description "Low priority" --color "fef2c0" --force || true

# Type labels
gh label create "bug" --description "Something is broken" --color "d73a4a" --force || true
gh label create "enhancement" --description "New feature" --color "a2eeef" --force || true
gh label create "refactor" --description "Code restructuring" --color "fbca04" --force || true
gh label create "docs" --description "Documentation" --color "0075ca" --force || true
gh label create "testing" --description "Test infrastructure" --color "1d76db" --force || true
gh label create "ci" --description "Continuous integration" --color "0e8a16" --force || true
gh label create "build" --description "Build system" --color "c5def5" --force || true

# Component labels
gh label create "bazel" --description "Bazel build system" --color "bfd4f2" --force || true
gh label create "cargo" --description "Cargo/Rust build" --color "d4c5f9" --force || true
gh label create "compiler" --description "Core compiler" --color "5319e7" --force || true
gh label create "cli" --description "Command-line interface" --color "c2e0c6" --force || true
gh label create "verification" --description "Formal verification" --color "006b75" --force || true
gh label create "coq" --description "Coq proofs" --color "0052cc" --force || true
gh label create "zephyr" --description "Zephyr integration" --color "1f70c1" --force || true
gh label create "qemu" --description "QEMU testing" --color "b60205" --force || true
gh label create "hardware" --description "Real hardware" --color "d93f0b" --force || true
gh label create "loom" --description "Loom integration" --color "0e8a16" --force || true

# Area labels
gh label create "architecture" --description "System architecture" --color "5319e7" --force || true
gh label create "developer-experience" --description "Dev tools and workflow" --color "d4c5f9" --force || true
gh label create "example" --description "Example code" --color "c2e0c6" --force || true
gh label create "integration" --description "Component integration" --color "1d76db" --force || true
gh label create "cleanup" --description "Code/doc cleanup" --color "fef2c0" --force || true

# Special labels
gh label create "honesty" --description "Reality check needed" --color "fbca04" --force || true
gh label create "planning" --description "Planning and roadmap" --color "bfdadc" --force || true
gh label create "demo" --description "Demo and showcase" --color "f9d0c4" --force || true
gh label create "marketing" --description "Marketing and outreach" --color "e99695" --force || true
gh label create "release" --description "Release preparation" --color "0e8a16" --force || true

echo -e "${GREEN}✓ Labels created${NC}"
echo ""

# ============================================================================
# Step 2: Create Milestones
# ============================================================================

echo -e "${BLUE}Step 2: Creating Milestones${NC}"
echo "----------------------------------------"

# Calculate due dates (relative to today)
PHASE0_DUE=$(date -v+7d +%Y-%m-%d 2>/dev/null || date -d "+7 days" +%Y-%m-%d)
PHASE1_DUE=$(date -v+21d +%Y-%m-%d 2>/dev/null || date -d "+21 days" +%Y-%m-%d)
PHASE2_DUE=$(date -v+35d +%Y-%m-%d 2>/dev/null || date -d "+35 days" +%Y-%m-%d)
PHASE3_DUE=$(date -v+42d +%Y-%m-%d 2>/dev/null || date -d "+42 days" +%Y-%m-%d)

gh api repos/:owner/:repo/milestones -f title="phase-0-cleanup" -f state="open" \
  -f description="Clean, organized repository with clear structure" -f due_on="${PHASE0_DUE}T23:59:59Z" || true

gh api repos/:owner/:repo/milestones -f title="phase-1-bazel" -f state="open" \
  -f description="Working Bazel build for Rust crates, OCaml extraction, and integration tests" -f due_on="${PHASE1_DUE}T23:59:59Z" || true

gh api repos/:owner/:repo/milestones -f title="phase-2-calculator" -f state="open" \
  -f description="Simple calculator WASM app running on Zephyr board" -f due_on="${PHASE2_DUE}T23:59:59Z" || true

gh api repos/:owner/:repo/milestones -f title="phase-3-polish" -f state="open" \
  -f description="Polished, documented, reproducible demo ready for v0.1.0 release" -f due_on="${PHASE3_DUE}T23:59:59Z" || true

echo -e "${GREEN}✓ Milestones created${NC}"
echo ""

# ============================================================================
# Step 3: Confirmation
# ============================================================================

echo -e "${GREEN}=========================================="
echo "✓ GitHub Infrastructure Setup Complete"
echo "==========================================${NC}"
echo ""
echo "Next steps:"
echo "1. Run: ./scripts/create_github_issues.sh   (to create all 38 issues)"
echo "2. Run: gh project create --title 'Synth Reorganization' --owner @me"
echo "3. Add issues to project board"
echo "4. Start with Phase 0, Issue #1"
echo ""
echo "To view:"
echo "  Labels:     gh label list"
echo "  Milestones: gh api repos/:owner/:repo/milestones"
echo ""
