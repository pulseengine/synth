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

# THE SUBJECT OF THE WAIT (RQ-77-SUBJECT, #1418). The branch ref is what was
# PUSHED; the PR object is what GitHub currently serves, and the two can
# disagree. Measured on #1410 at the v0.76 cut: `git ls-remote` showed
# c84de062 while the PR still reported head 272e78b1 WITH 72 GREEN CONTEXTS and
# zero check-runs registered for the pushed SHA. So the expectation is derived
# from the ref, and `merge_gate.py --expect-head` REFUSES (exit 2, never
# GATEOK) if the verdict would be about the other commit.
EXPECT=$(git rev-parse "origin/$HEADREF")
echo "  subject: origin/$HEADREF = ${EXPECT:0:8}"

# Wait for every NON-ADVISORY check to reach a conclusion (CHECK3b).
#
# WITH A POPULATION FLOOR, because "nothing is pending" is also true of a PR
# whose checks have not registered yet. The old form broke immediately on an
# EMPTY rollup — `P` counts checks with an empty conclusion, and an empty
# rollup has none of those. Observed on #1407 at the v0.75 cut
# ("TERMINAL: 0 non-adv"). CHECK1 did catch it downstream by reporting all nine
# required contexts missing, so nothing was ever merged wrongly; but a wait that
# does not wait, rescued by a later check, is precisely this release's theme —
# and "9 missing" reads as a verdict about the PR when it means "CI has not
# started". The floor is the count of REQUIRED contexts, derived from branch
# protection rather than hardcoded, so it tracks the contract instead of a
# number someone has to remember to update.
FLOOR=$(gh api "repos/$REPO/branches/main/protection/required_status_checks/contexts" --jq 'length')
[ -n "$FLOOR" ] && [ "$FLOOR" -gt 0 ] || { echo "REFUSE: could not derive the required-context count; the wait would be unbounded"; exit 2; }
echo "  wait floor: $FLOOR required contexts must be present before a verdict"
# The wait BUDGET, in minutes (one poll per minute). Overridable because runner
# capacity is a fleet property, not a property of this script: synth holds 1-2 of
# 12 self-hosted slots and a release PR has taken ~2.5h, so a 3h default is
# generous rather than tight. The default is deliberately NOT unbounded.
MAX_WAIT_MIN=${MERGE_RITUAL_MAX_WAIT_MIN:-180}
WAITED=0
echo "  wait budget: ${MAX_WAIT_MIN} minute(s), then REFUSE rather than hang"
while :; do
  read -r N P <<EOF
$(gh pr view "$PR" --repo "$REPO" --json statusCheckRollup --jq '
  [.statusCheckRollup[] | select(((.name // .context // "")|test("codecov|advisory";"i")) | not)] as $n
  | [$n | length, ([$n[] | select(((.conclusion // .state // "") == ""))] | length)]
  | @tsv')
EOF
  if [ "${N:-0}" -ge "$FLOOR" ] && [ "${P:-1}" = "0" ]; then break; fi
  # A WAIT THAT EXHAUSTS ITS BUDGET MUST SAY SO, not hang. Before this cap the
  # loop was `while :; do ... sleep 60; done` with no bound at all, so its
  # failure mode was a HANG — an operator staring at a silent terminal with no
  # verdict, which is worse to diagnose than a refusal because there is nothing
  # to read. It is a REFUSAL (exit 2: could not judge), never a fall-through to
  # a verdict: timing out tells you nothing about whether the PR is mergeable.
  WAITED=$((WAITED + 1))
  if [ "$WAITED" -ge "$MAX_WAIT_MIN" ]; then
    echo "REFUSE: TIMEOUT after ${WAITED} minutes waiting for CHECK3b."
    echo "  $N non-advisory checks present (floor $FLOOR), $P still without a conclusion."
    echo "  This is NOT a verdict about the PR — the wait ran out, so nothing is known."
    echo "  Raise MERGE_RITUAL_MAX_WAIT_MIN and re-run, or investigate runner capacity."
    exit 2
  fi
  sleep 60
done
echo "  settled at $(date -u '+%H:%MZ') with $N non-advisory checks present"

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

# READ THE EXIT CODE, not only the string. RQ-77-SUBJECT built exit 2 so a
# caller could tell "the gate ran and the answer is no" (1) from "the gate could
# not judge" (2) — and v0.77's round-1 review found that this, the ONLY caller,
# discarded it: `| tee` makes $? tail's, so GATEREFUSED and GATEFAIL were
# indistinguishable here and the artifact's claim was false about its own
# consumer. Redirect, capture rc, then read the file.
python3 scripts/merge_gate.py --pr "$PR" --repo "$REPO" \
  --expect-head "$EXPECT" > "$SCR/gate.txt" 2>&1
GATERC=$?
cat "$SCR/gate.txt"
if [ "$GATERC" = "2" ]; then
  echo "  REFUSED: the gate could not JUDGE (exit 2) — this is not a red verdict,"
  echo "  it is an unusable one. Not merging."
  exit 2
fi

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
