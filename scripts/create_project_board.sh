#!/bin/bash
# Create and configure GitHub Project Board for Synth Reorganization

set -e

echo "=========================================="
echo "Creating GitHub Project Board"
echo "=========================================="
echo ""

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
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

# Check if jq is installed (for JSON processing)
if ! command -v jq &> /dev/null; then
    echo -e "${YELLOW}Warning: jq not installed. Install for better JSON handling.${NC}"
    echo "Install: brew install jq (macOS) or apt install jq (Linux)"
    echo ""
fi

echo -e "${BLUE}Step 1: Creating Project${NC}"
echo "----------------------------------------"

# Create project (Projects v2)
PROJECT_ID=$(gh api graphql -f query='
  mutation {
    createProjectV2(input: {
      ownerId: "USER_ID_PLACEHOLDER"
      title: "Synth Reorganization"
      repositoryId: "REPO_ID_PLACEHOLDER"
    }) {
      projectV2 {
        id
        number
        url
      }
    }
  }
' 2>&1)

# Fallback: Create via CLI (simpler but less control)
echo "Creating project via CLI..."
gh project create \
  --title "Synth Reorganization" \
  --owner @me \
  --body "Systematic reorganization of Synth: Cleanup → Bazel → Calculator Demo → Release v0.1.0" \
  || echo "Project may already exist"

echo ""
echo -e "${GREEN}✓ Project created${NC}"
echo ""

# Get project number
echo -e "${BLUE}Step 2: Getting Project Number${NC}"
echo "----------------------------------------"

PROJECT_NUMBER=$(gh project list --owner @me --format json | grep -o '"number":[0-9]*' | head -1 | grep -o '[0-9]*')

if [ -z "$PROJECT_NUMBER" ]; then
    echo "Could not determine project number. Please check manually:"
    echo "  gh project list --owner @me"
    exit 1
fi

echo "Project number: $PROJECT_NUMBER"
echo ""

echo -e "${BLUE}Step 3: Adding Issues to Project${NC}"
echo "----------------------------------------"

# Get all issues grouped by milestone
echo "Adding Phase 0 issues..."
gh issue list --milestone "phase-0-cleanup" --limit 100 --json number | \
  jq -r '.[].number' | while read issue_num; do
    echo "  Adding issue #$issue_num"
    gh project item-add $PROJECT_NUMBER --owner @me --url "https://github.com/pulseengine/Synth/issues/$issue_num" || true
done

echo ""
echo "Adding Phase 1 issues..."
gh issue list --milestone "phase-1-bazel" --limit 100 --json number | \
  jq -r '.[].number' | while read issue_num; do
    echo "  Adding issue #$issue_num"
    gh project item-add $PROJECT_NUMBER --owner @me --url "https://github.com/pulseengine/Synth/issues/$issue_num" || true
done

echo ""
echo "Adding Phase 2 issues..."
gh issue list --milestone "phase-2-calculator" --limit 100 --json number | \
  jq -r '.[].number' | while read issue_num; do
    echo "  Adding issue #$issue_num"
    gh project item-add $PROJECT_NUMBER --owner @me --url "https://github.com/pulseengine/Synth/issues/$issue_num" || true
done

echo ""
echo "Adding Phase 3 issues..."
gh issue list --milestone "phase-3-polish" --limit 100 --json number | \
  jq -r '.[].number' | while read issue_num; do
    echo "  Adding issue #$issue_num"
    gh project item-add $PROJECT_NUMBER --owner @me --url "https://github.com/pulseengine/Synth/issues/$issue_num" || true
done

echo ""
echo -e "${GREEN}✓ Issues added to project${NC}"
echo ""

echo -e "${BLUE}Step 4: Project Views${NC}"
echo "----------------------------------------"

echo "Creating custom views..."
echo ""
echo "Note: Custom fields and views must be configured manually in the GitHub UI:"
echo ""
echo "Recommended views:"
echo "  1. By Phase (group by Milestone)"
echo "  2. By Priority (group by P0/P1/P2/P3 labels)"
echo "  3. By Status (Todo, In Progress, Review, Done)"
echo "  4. Gantt Chart (timeline view by Due Date)"
echo ""
echo "To configure:"
echo "  1. Go to: https://github.com/users/$(gh api user -q .login)/projects/$PROJECT_NUMBER"
echo "  2. Click '+' to add new view"
echo "  3. Choose layout: Board, Table, or Gantt"
echo "  4. Configure grouping and sorting"
echo ""

echo -e "${GREEN}=========================================="
echo "✓ Project Board Setup Complete"
echo "==========================================${NC}"
echo ""
echo "Your project is ready!"
echo ""
echo "View it at:"
echo "  gh project view $PROJECT_NUMBER --owner @me --web"
echo ""
echo "Or visit:"
echo "  https://github.com/users/$(gh api user -q .login)/projects/$PROJECT_NUMBER"
echo ""
echo "Next steps:"
echo "1. Configure custom views in the GitHub UI"
echo "2. Start with Phase 0, Issue #1"
echo "3. Move issues across board as you work"
echo ""
