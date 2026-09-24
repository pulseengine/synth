#!/bin/bash
# RQ-72-RITUAL (#1269): THE FOUR-CHECK MERGE RITUAL, committed.
#
# Until v0.72 this lived in a session scratchpad. Measured on 87fb06d7:
# `git grep -lIE 'merge --squash' -- scripts .github` returned NOTHING. It had
# already been lost once with a deleted volume and rebuilt from memory, and the
# rebuild is what introduced the squash-subject defect that reddened main
# during v0.71. A ritual that gates every merge and every tag belongs in the
# repository it gates.
#
# The decidable half lives in `scripts/merge_gate.py`, which CI exercises via
# `--self-test`. This file is the orchestration the network half needs.
#
#   CHECK1  all 9 required contexts SUCCESS, verified BY NAME from the API
#   CHECK2  the BRANCH is CURRENT — `git merge-base --is-ancestor` plus
#           `rev-list --count` = 0. NOT `baseRefOid == origin/main`, which is
#           the PR's recorded BASE TIP and passed on #1268's stale branch
#           (#1269a).
#   CHECK3  zero non-advisory RED
#   CHECK3b zero non-advisory PENDING — a monitor reporting "9/9" is not
#           permission; v0.66 measured a READY firing with 33 oracles pending.
#   CHECK4  `status_evidence_check.py` rc=0 on a SQUASH SIMULATION built off
#           origin/main and committed under the EXACT subject the merge pins.
#
# THE SUBJECT IS PINNED, NOT PREDICTED. `gh pr merge --squash` uses the PR
# TITLE only when the branch has MORE THAN ONE commit; with exactly one it uses
# THAT COMMIT'S subject. v0.71 simulated the title, merged the other, and main
# went red on R10 with CI green on the same head — a gate passing on a tree
# that was never created.
set -uo pipefail
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Library/Developer/CommandLineTools}
PR="${1:?usage: merge_ritual.sh <pr-number>}"
REPO="${REPO:-pulseengine/synth}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SIM="${SIM:-${ROOT}-squash-sim}"
SCR="$(mktemp -d)"
cd "$ROOT" || exit 1

git fetch -q origin main
HEADREF=$(gh pr view "$PR" --repo "$REPO" --json headRefName --jq .headRefName)
TITLE=$(gh pr view "$PR" --repo "$REPO" --json title --jq .title)
git fetch -q origin "$HEADREF"

# Wait for every NON-ADVISORY check to reach a conclusion (CHECK3b).
while :; do
  P=$(gh pr view "$PR" --repo "$REPO" --json statusCheckRollup --jq '
    [.statusCheckRollup[] | select(((.name // .context // "")|test("codecov|advisory";"i")) | not)
     | select(((.conclusion // .state // "") == ""))] | length')
  [ "$P" = "0" ] && break
  sleep 60
done
echo "  settled at $(date -u '+%H:%MZ')"

# CHECK4 — the squash simulation, under the subject the merge will pin.
git worktree remove --force "$SIM" 2>/dev/null
git branch -D "sim/squash-$PR" >/dev/null 2>&1
git worktree prune
CHECK4=1
if git worktree add -q "$SIM" -b "sim/squash-$PR" origin/main \
   && git -C "$SIM" merge --squash "origin/$HEADREF" >/dev/null 2>&1 \
   && git -C "$SIM" -c commit.gpgsign=false commit -q -m "$TITLE (#$PR)"; then
  ( cd "$SIM" && python3 scripts/status_evidence_check.py > "$SCR/c4.log" 2>&1 )
  CHECK4=$?
fi
echo "  CHECK4 (squash simulation) rc=$CHECK4"
[ "$CHECK4" != "0" ] && grep -E '^FAIL' "$SCR/c4.log" | head -4

python3 scripts/merge_gate.py --pr "$PR" --repo "$REPO" | tee "$SCR/gate.txt"

# THE MERGE IS THE LAST LINK OF THE CHAIN, never a line of its own.
grep -q '^GATEOK$' "$SCR/gate.txt" && [ "$CHECK4" = "0" ] \
  && gh pr merge "$PR" --repo "$REPO" --squash --delete-branch \
       --subject "$TITLE (#$PR)" 2>&1 | tail -2
# `gh pr merge` returns non-zero on SUCCESS (#1064 measured it); confirm by STATE.
sleep 5
STATE=$(gh pr view "$PR" --repo "$REPO" --json state --jq .state)
echo "  #$PR state=$STATE"

# RQ-73-STEP8 (#1269 ask 2): call merge_gate.py's `squash_fidelity` and
# RECORD the post-merge diff instead of producing
# it by hand. v0.72 attested all eleven merges manually — evidence, but not
# the mechanism the issue asks for, and a number a human produces is a number
# a human can forget. Runs only once the merge is confirmed, because the merge
# commit does not exist before then. Advisory by design: the merge has already
# happened, so this REPORTS rather than gates, and a non-FAITHFUL verdict is
# printed loudly for the operator to act on.
if [ "$STATE" = "MERGED" ]; then
  # (v0.73 cold review round 2, finding 4) The squash commit is created by the
  # merge above and is NOT in the local object store — every fetch happens
  # before the merge. Without this, `git diff <head> <merged>` fatals and the
  # attestation reported FAITHFUL unconditionally: the same shape #1269
  # describes, where 45 merges read 0 because the number answered a different
  # question.
  git fetch -q origin main
  python3 scripts/merge_gate.py --pr "$PR" --repo "$REPO" --squash-fidelity \
    || echo "  !! squash fidelity NOT confirmed for #$PR — read the verdict above"
fi
git worktree remove --force "$SIM" 2>/dev/null
git branch -D "sim/squash-$PR" >/dev/null 2>&1
git worktree prune
rm -rf "$SCR"
[ "$STATE" = "MERGED" ] || exit 1
