#!/bin/bash
# RQ-72-RITUAL (#1269): THE RELEASE TAG RITUAL, committed.
#
# GATE ON **PRETAG** CONFORMANCE. v0.70's version demanded RETRO CONFORMS before
# pushing the tag — and once the tag exists locally the checker flips PRETAG ->
# RETRO, where it demands a Signing E2E run and live crates. Both are triggered
# BY THE PUSH this gate precedes, so it could never pass. A gate that cannot
# pass is the same defect class as one that cannot fail, and this repo has
# shipped both.
#
# So: gate the push on PRETAG CONFORMS plus the tag's own shape; assert RETRO
# CONFORMS AFTER publishing.
set -uo pipefail
export DEVELOPER_DIR=${DEVELOPER_DIR:-/Library/Developer/CommandLineTools}
VER="${1:?usage: tag_release.sh v0.72.0}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCR="$(mktemp -d)"
cd "$ROOT" || exit 1

command -v ssh-add >/dev/null && ssh-add -l >/dev/null 2>&1 || echo "  WARN: no ssh key loaded"
# W1 (#1440) — THE FETCH'S EXIT CODE IS CHECKED. It was not, and an unchecked
# fetch makes every later "HEAD == origin/main" statement true about a STALE
# tree: the comparison succeeds because both sides are the old value.
git fetch -q origin main || { echo "  REFUSE: git fetch origin main FAILED — every"; \
  echo "          later HEAD==origin/main assertion would be true about a stale tree"; exit 1; }

# W1b (#1440) — THE FAST-FORWARD'S EXIT CODE IS CHECKED TOO, and HEAD is then
# ASSERTED equal to origin/main. Guarding the fetch alone is insufficient: a
# refused ff-merge left main behind with its rc discarded into /dev/null.
git checkout -q main || { echo "  REFUSE: cannot check out main"; exit 1; }
git merge --ff-only origin/main >/dev/null 2>&1 \
  || { echo "  REFUSE: main is not fast-forwardable to origin/main — diverged or behind"; exit 1; }
HEAD_SHA="$(git rev-parse HEAD)"
ORIGIN_SHA="$(git rev-parse origin/main)"
[ "$HEAD_SHA" = "$ORIGIN_SHA" ] \
  || { echo "  REFUSE: HEAD $HEAD_SHA != origin/main $ORIGIN_SHA"; exit 1; }
echo "  main: $(git rev-parse --short HEAD) (== origin/main, both asserted)"
[ -n "$(git status --porcelain)" ] && { echo "  REFUSE: main checkout is dirty"; git status --short; exit 1; }

# W2b (#1440) — A LEFTOVER TAG FROM A PREVIOUS ATTEMPT MUST POINT AT HEAD.
# This is the consequence that made W2 worth more than "leaves residue": the old
# flow created the tag BEFORE its decision, so a refused attempt left the tag
# behind; the next run then found it, checked only its SHAPE, and pushed it —
# AT THE PRE-FIX COMMIT. Nothing compared the tag's commit to HEAD.
#
# `git rev-parse <unknown-ref>` ECHOES its argument on stdout and errors only on
# stderr, so the test must be `--verify --quiet` plus the rc, never the output.
TAG_PREEXISTING=0
if git rev-parse --verify --quiet "$VER" >/dev/null; then
  TAG_COMMIT="$(git rev-parse "$VER^{commit}")"
  if [ "$TAG_COMMIT" != "$HEAD_SHA" ]; then
    echo "  REFUSE: tag $VER already exists at $(git rev-parse --short "$VER^{commit}")," \
         "not HEAD $(git rev-parse --short HEAD)."
    echo "          Pushing it would publish a PRE-FIX commit. Delete it first, and"
    echo "          gate the delete on \`git ls-remote --tags origin\` rather than on an exit code."
    exit 1
  fi
  echo "  tag $VER already exists and points AT HEAD — reusing it"
  TAG_PREEXISTING=1
fi

# GATE 1 — PRETAG conformance, on main, BEFORE the tag object exists.
python3 scripts/loop_conformance_check.py "$VER" > "$SCR/pretag.log" 2>&1
G1=$?
echo "  GATE1 pretag conformance rc=$G1"
tail -1 "$SCR/pretag.log" | sed 's/^/    /'
[ "$G1" = "0" ] || grep -E 'DERIVED-FAIL|NOT-DERIVED' "$SCR/pretag.log" | head -6 | sed 's/^/    /'

# GATE 2 — the pre-push battery every lane runs. One invocation per line: zsh
# does not word-split "$var", and a loop over "script.py arg" pairs looks for a
# file literally named `script.py arg` (measured five times in this programme).
G2=0
python3 scripts/claim_check.py claims.yaml      > "$SCR/g_claim.log"  2>&1 || { echo "    FAIL claim_check";      G2=1; }
python3 scripts/status_evidence_check.py        > "$SCR/g_status.log" 2>&1 || { echo "    FAIL status_evidence";  G2=1; }
python3 scripts/check_version_pins.py           > "$SCR/g_pins.log"   2>&1 || { echo "    FAIL version_pins";     G2=1; }
python3 scripts/oracle_wiring_check.py          > "$SCR/g_wire.log"   2>&1 || { echo "    FAIL oracle_wiring";    G2=1; }
python3 scripts/artifact_citation_check.py      > "$SCR/g_cite.log"   2>&1 || { echo "    FAIL artifact_citation";G2=1; }
python3 scripts/ci_pool_tripwire.py             > "$SCR/g_pool.log"   2>&1 || { echo "    FAIL ci_pool_tripwire"; G2=1; }
echo "  GATE2 pre-push battery rc=$G2"

# GATE 2b (RQ-83-CANCELGAP, #1484) — NO UNVERIFIED CHECK-RUN ON THE COMMIT BEING
# TAGGED. A `cancelled` or `timed_out` check is neither a failure nor pending, so
# until v0.83 it answered NO to every question this programme's gates asked and
# read as a pass. MEASURED on v0.82's own release commit: the REQUIRED context
# `Claim Check` reported `cancelled` with no runner and `steps=0` — a runner
# no-show — and nothing in this script or in merge_ritual.sh looked for it
# (`grep -i -E 'cancel|timed_out'` returned rc=1 with ZERO hits in both). Only a
# hand-run guard outside the repo refused it.
#
# The classification is NOT duplicated here. It lives in `merge_gate.py`, which
# the merge path already uses, and this calls the same module — a second
# hand-written list of bad states is the drift the North Star forbids, and v0.72
# measured that cost when a literal `9` turned out to be a FOURTH copy of the
# required-context contract.
#
# Exit codes are distinguishable, verified against real commits: 0 clean, 1 an
# unverified check present, 2 the scan could not JUDGE (bad sha, API failure, or
# a ZERO population — which is a refusal, not a pass).
python3 scripts/merge_gate.py --unverified-on "$HEAD_SHA" > "$SCR/g_unver.log" 2>&1
G2B=$?
sed 's/^/    /' "$SCR/g_unver.log"
if [ "$G2B" = "2" ]; then
  echo "  GATE2b REFUSED: the unverified-check scan could not JUDGE (exit 2)."
  echo "          That is not a clean result — do not tag past it."
  G2=1
elif [ "$G2B" != "0" ]; then
  echo "  GATE2b REFUSE: an UNVERIFIED check-run is present on $HEAD_SHA."
  echo "          A NO-SHOW (steps=0, no runner) is remedied by"
  echo "          'gh run rerun <id> --failed' once the run reports completed —"
  echo "          re-run rather than tag past it. A genuine cancellation needs a"
  echo "          reason before this gate is waived."
  G2=1
fi
echo "  GATE2b unverified-check scan rc=$G2B"

# GATE 4 — the tagged commit must carry SOME signature, never `G`. GitHub
# re-signs squash merges with web-flow key B5690EEEBB952194, which is not in
# this keyring, so every correct release commit reports E. A gate demanding G
# would refuse every correct release.
# Read off HEAD, not "$VER^{commit}": this now runs BEFORE the tag exists, and
# HEAD is the commit the tag will point at (asserted above).
GQ=$(git log -1 --format='%G?' HEAD)
GK=$(git log -1 --format='%GK' HEAD)
G4=0
[ "$GQ" != "N" ] && [ -n "$GK" ] || { echo "    FAIL: tagged commit unsigned (%G?=$GQ %GK=$GK)"; G4=1; }
echo "  GATE4 tagged commit signature: %G?=$GQ %GK=$GK rc=$G4"

# W2 (#1440) — THE TAG IS CREATED ONLY AFTER THE DECISION.
# It used to be created 21 lines ABOVE this point, so a REFUSAL left the tag
# behind for the next run to find and (per W2b) push at the wrong commit. A
# refusal here creates nothing, so there is no residue to clean up by hand.
[ "$G1" = "0" ] && [ "$G2" = "0" ] && [ "$G4" = "0" ] \
  || { echo "  REFUSED — not tagging $VER (no tag was created)"; rm -rf "$SCR"; exit 1; }

if [ "$TAG_PREEXISTING" = "0" ]; then
  git tag -a "$VER" -m "release $VER" || { echo "  REFUSE: git tag failed"; rm -rf "$SCR"; exit 1; }
  echo "  created annotated tag $VER (AFTER the gates, not before)"
fi

# GATE 3 — annotated and UNSIGNED, verified by COUNTING signature BLOCKS in the
# tag object. Never by grepping `git tag -v` for the word "signature", which
# appears in its own diagnostics. The unsigned shape is DELIBERATE: tag.gpgsign
# is unset at every scope and the three previous tags carry zero blocks.
SIGBLOCKS=$(git cat-file -p "$VER" | grep -c -- '-----BEGIN .*SIGNATURE-----')
TYPE=$(git cat-file -t "$VER")
G3=0
[ "$TYPE" = "tag" ] || { echo "    FAIL: $VER is a $TYPE, not an annotated tag"; G3=1; }
[ "$SIGBLOCKS" = "0" ] || { echo "    FAIL: tag carries $SIGBLOCKS signature block(s); want 0"; G3=1; }
echo "  GATE3 tag shape: type=$TYPE signature_blocks=$SIGBLOCKS rc=$G3"

# A G3 failure must leave NO residue either. The delete is gated on the tag not
# being present on the remote — never on an exit code alone.
if [ "$G3" != "0" ]; then
  if [ "$TAG_PREEXISTING" = "0" ] && ! git ls-remote --tags origin "refs/tags/$VER" | grep -q "refs/tags/$VER"; then
    git tag -d "$VER" >/dev/null && echo "  deleted the local tag — the refusal leaves no residue"
  else
    echo "  NOT deleting $VER: it pre-existed this run or is already on the remote"
  fi
  echo "  REFUSED — not pushing $VER"; rm -rf "$SCR"; exit 1
fi

# THE PUSH IS THE LAST LINK OF THE CHAIN.
git push origin "$VER" \
  && echo "  PUSHED $VER" \
  || { echo "  REFUSED — push failed for $VER"; rm -rf "$SCR"; exit 1; }
rm -rf "$SCR"

# GATE5 — THE CLOSURE GATE IS ASKED, not echoed.
#
# v0.72's gate-potency cold review found that RQ-72-ISSUEGATE, the lane titled
# "the closure gate now gets asked", left `issue_closure_check.py` with no
# automated invocation at all: a doc section, a human checklist, and the two
# lines BELOW — which printed the command instead of running it. The script was
# fully potent; nothing ran it. That is the lane's own subject, one release
# late, and the same release had already committed this file, so the gate was
# one line from being asked.
#
# It runs AFTER the push on purpose. Before the tag exists there is nothing to
# compare a close-set against, and the issues are closed after the release
# workflows publish. So this is ADVISORY here — it reports, and the operator
# acts on it — while the authoritative run is the one at the closing step,
# after the issues have actually been closed.
echo "  GATE5: asking the closure gate (advisory at this point — no issue is closed yet)"
python3 "$ROOT/scripts/issue_closure_check.py" --release "$VER" --since-tag "$VER" --allow-unclosed
G5=$?
# Its exit code used to vanish into `|| echo`, so "advisory" and "we never looked"
# were indistinguishable. It stays ADVISORY — nothing is closed yet, so a red here
# is expected — but the code is now REPORTED, which is what makes the advisory
# honest rather than decorative.
echo "  GATE5 closure gate (advisory) rc=$G5"
[ "$G5" = "0" ] || echo "  GATE5 reported findings above — act on them at the closing step"

echo "  NEXT: assert RETRO CONFORMS after the release workflows publish, then"
echo "        re-run scripts/issue_closure_check.py --release $VER --since-tag $VER"
echo "        WITHOUT --allow-unclosed, once the issues it authorises are closed."
