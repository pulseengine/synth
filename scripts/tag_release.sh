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
git fetch -q origin main
git checkout -q main && git merge --ff-only origin/main >/dev/null 2>&1
echo "  main: $(git rev-parse --short HEAD)"
[ -n "$(git status --porcelain)" ] && { echo "  REFUSE: main checkout is dirty"; git status --short; exit 1; }

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

# GATE 3 — annotated and UNSIGNED, verified by COUNTING signature BLOCKS in the
# tag object. Never by grepping `git tag -v` for the word "signature", which
# appears in its own diagnostics.
if git rev-parse "$VER" >/dev/null 2>&1; then
  echo "  tag $VER already exists locally: $(git rev-parse --short "$VER")"
else
  git tag -a "$VER" -m "release $VER" || exit 1
  echo "  created annotated tag $VER"
fi
SIGBLOCKS=$(git cat-file -p "$VER" | grep -c -- '-----BEGIN .*SIGNATURE-----')
TYPE=$(git cat-file -t "$VER")
G3=0
[ "$TYPE" = "tag" ] || { echo "    FAIL: $VER is a $TYPE, not an annotated tag"; G3=1; }
[ "$SIGBLOCKS" = "0" ] || { echo "    FAIL: tag carries $SIGBLOCKS signature block(s); want 0"; G3=1; }
echo "  GATE3 tag shape: type=$TYPE signature_blocks=$SIGBLOCKS rc=$G3"

# GATE 4 — the tagged commit must carry SOME signature, never `G`. GitHub
# re-signs squash merges with web-flow key B5690EEEBB952194, which is not in
# this keyring, so every correct release commit reports E. A gate demanding G
# would refuse every correct release.
GQ=$(git log -1 --format='%G?' "$VER^{commit}")
GK=$(git log -1 --format='%GK' "$VER^{commit}")
G4=0
[ "$GQ" != "N" ] && [ -n "$GK" ] || { echo "    FAIL: tagged commit unsigned (%G?=$GQ %GK=$GK)"; G4=1; }
echo "  GATE4 tagged commit signature: %G?=$GQ %GK=$GK rc=$G4"

# THE PUSH IS THE LAST LINK OF THE CHAIN.
[ "$G1" = "0" ] && [ "$G2" = "0" ] && [ "$G3" = "0" ] && [ "$G4" = "0" ] \
  && git push origin "$VER" \
  && echo "  PUSHED $VER" \
  || { echo "  REFUSED — not pushing $VER"; rm -rf "$SCR"; exit 1; }
rm -rf "$SCR"
echo "  NEXT: assert RETRO CONFORMS after the release workflows publish, then"
echo "        run scripts/issue_closure_check.py --release $VER --since-tag $VER"
