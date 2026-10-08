#!/usr/bin/env python3
# ci-status: wired — runs in the required `claim-check` job.
"""The FIRST test for `scripts/tag_release.sh` (RQ-80-RITUAL3, #1440).

WHY IT DID NOT HAVE ONE, and why that mattered. `grep -rn tag_release` over the
tree found ZERO tests and ZERO CI references, and `docs/reviews/v0.72-cold-review.md`
recorded that same absence EIGHT releases earlier. Four weaknesses were therefore
hand-guarded by the operator at every single tag:

  W1   `git fetch -q origin main` had its exit code UNCHECKED, so a failed fetch
       made every later "HEAD == origin/main" statement true about a STALE tree —
       the comparison succeeds because both sides hold the old value.
  W1b  the `git merge --ff-only` rc was ALSO discarded (into /dev/null), and
       nothing asserted HEAD == origin/main. Guarding the fetch alone is not enough.
  W2   the tag was created ~21 lines ABOVE its own G1-G4 decision, so a REFUSAL
       left the tag behind.
  W2b  and on the next run that leftover tag was REUSED: only its SHAPE was
       checked, never its COMMIT. A tag minted before a fix was therefore pushed
       AT THE PRE-FIX COMMIT. That is why W2 is "can publish the wrong commit",
       not merely "leaves residue".

WHAT THIS FILE CAN AND CANNOT PROVE, stated because the difference is the whole
honesty of it. A real tag run needs a real remote, a real signing key and real
gates. So PART 1 EXECUTES THE SHIPPED SCRIPT against a throwaway git repo with
stub gate scripts — the lines under test are the lines that ship, nothing is
mirrored — and PART 2 asserts the remaining structure statically, each assertion
proven non-vacuous by removing the property from a COPY and checking it then fails.

Run:  python3 scripts/test_tag_release.py
"""
from __future__ import annotations

import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "tag_release.sh"

fails: list[str] = []
ran: list[str] = []


def ok(name: str, cond: bool, detail: str = "") -> None:
    ran.append(name)
    print(f"  {'ok  ' if cond else 'FAIL'} {name}" + (f" — {detail}" if not cond and detail else ""))
    if not cond:
        fails.append(name)


def git(repo, *args, check=True):
    r = subprocess.run(["git", *args], cwd=repo, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} failed in {repo}: {r.stderr}")
    return r


GATES = ["loop_conformance_check.py", "claim_check.py", "status_evidence_check.py",
         "check_version_pins.py", "oracle_wiring_check.py", "artifact_citation_check.py",
         "ci_pool_tripwire.py", "issue_closure_check.py",
         # RQ-83-CANCELGAP (#1484): GATE2b calls `merge_gate.py --unverified-on`
         # so the TAG path and the MERGE path share ONE state classification
         # rather than two hand-written copies. Without a stub here the sandbox
         # has no such file, GATE2b correctly reports rc=2 ("could not JUDGE"),
         # and the happy path reds — which is how this entry was found rather
         # than assumed.
         "merge_gate.py"]


def make_repo(tmp, *, gate_rc=0, conformance_rc=0):
    """A throwaway origin + clone carrying the SHIPPED script and stub gates."""
    origin, work = tmp / "origin.git", tmp / "work"
    subprocess.run(["git", "init", "-q", "--bare", str(origin)], check=True)
    subprocess.run(["git", "init", "-q", "-b", "main", str(work)], check=True)
    env = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
           "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
    for k, v in env.items():
        os.environ[k] = v
    (work / "scripts").mkdir()
    shutil.copy(SCRIPT, work / "scripts" / "tag_release.sh")
    for g in GATES:
        rc = conformance_rc if g == "loop_conformance_check.py" else gate_rc
        if g == "issue_closure_check.py":
            rc = 0
        (work / "scripts" / g).write_text(
            f"import sys\nprint('stub {g}')\nsys.exit({rc})\n")
    (work / "README").write_text("x\n")
    git(work, "add", "-A")
    # commit.gpgsign may be on globally; this repo must not require a key
    git(work, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "base")
    git(work, "remote", "add", "origin", str(origin))
    git(work, "push", "-q", "origin", "main")
    git(work, "fetch", "-q", "origin", "main")
    return origin, work


def run_tag(work, ver="v9.9.9"):
    return subprocess.run(["bash", "scripts/tag_release.sh", ver],
                          cwd=work, capture_output=True, text=True)


def tag_exists(repo, ver="v9.9.9"):
    return subprocess.run(["git", "rev-parse", "--verify", "--quiet", ver],
                          cwd=repo, capture_output=True, text=True).returncode == 0


print("PART 1 — EXECUTION of the shipped script against a throwaway repo")

# W2: a REFUSAL must create NO tag.
with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    _origin, work = make_repo(tmp, conformance_rc=1)      # GATE1 fails
    r = run_tag(work)
    ok("W2: a refused run exits non-zero", r.returncode != 0, f"rc={r.returncode}")
    ok("W2: a refused run creates NO tag", not tag_exists(work),
       "the tag was left behind — this is the residue W2 names")
    ok("W2: ...and says so", "no tag was created" in r.stdout, r.stdout[-200:])

# W2b: a pre-existing tag NOT pointing at HEAD must be REFUSED, not reused.
with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    _origin, work = make_repo(tmp)
    git(work, "tag", "-a", "v9.9.9", "-m", "stale")        # tag the base commit
    (work / "README").write_text("fixed\n")               # then "fix" something
    git(work, "add", "-A")
    git(work, "-c", "commit.gpgsign=false", "commit", "-q", "-m", "the fix")
    git(work, "push", "-q", "origin", "main")
    git(work, "fetch", "-q", "origin", "main")
    r = run_tag(work)
    ok("W2b: a leftover tag not at HEAD is REFUSED", r.returncode != 0, f"rc={r.returncode}")
    ok("W2b: ...naming the pre-fix hazard",
       "PRE-FIX" in r.stdout.upper(), r.stdout[-300:])
    pushed = subprocess.run(["git", "ls-remote", "--tags", "origin"], cwd=work,
                            capture_output=True, text=True).stdout
    ok("W2b: ...and the stale tag was NOT pushed", "v9.9.9" not in pushed, pushed)

# W1: a failing fetch must REFUSE rather than compare a stale tree to itself.
with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    _origin, work = make_repo(tmp)
    git(work, "remote", "set-url", "origin", str(tmp / "does-not-exist.git"))
    r = run_tag(work)
    ok("W1: a failed fetch REFUSES", r.returncode != 0, f"rc={r.returncode}")
    ok("W1: ...and names the stale-tree consequence",
       "stale" in r.stdout.lower(), r.stdout[-200:])
    ok("W1: ...and creates no tag", not tag_exists(work))

# GATE4 must REFUSE a tag on an UNSIGNED commit. This harness cannot mint a
# signed commit (no key in CI), so rather than stub around GATE4 — which would
# test the stub — the unsigned case is asserted as the real property it is.
with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    _origin, work = make_repo(tmp)
    r = run_tag(work)
    unsigned = re.search(r"GATE4 tagged commit signature: %G\?=N", r.stdout) is not None
    ok("GATE4: an UNSIGNED tagged commit is refused", r.returncode != 0 and unsigned,
       f"rc={r.returncode}; {r.stdout[-200:]}")
    ok("GATE4: ...and the refusal creates no tag", not tag_exists(work))

# THE TAG-AND-PUSH PATH needs a signed commit, so it is gated on signing being
# available and SKIPPED LOUDLY otherwise. A silent skip here would leave the
# guards above indistinguishable from a script that always refuses — so the skip
# is printed, and the push path is additionally asserted STATICALLY in part 2.
def signing_available():
    r = subprocess.run(["ssh-add", "-l"], capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.strip():
        return None
    key = subprocess.run(["ssh-add", "-L"], capture_output=True, text=True).stdout.splitlines()
    return key[0] if key else None

SIGKEY = signing_available()
if SIGKEY is None:
    print("  SKIP (loudly) tag-and-push: no ssh key loaded, so no signed commit can")
    print("       be minted here. GATE4 would refuse, which is correct, so this path")
    print("       is covered statically in part 2 rather than silently passed.")
else:
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        origin, work = make_repo(tmp)
        kf = tmp / "signer.pub"
        kf.write_text(SIGKEY + "\n")
        git(work, "config", "gpg.format", "ssh")
        git(work, "config", "user.signingkey", str(kf))
        (work / "README").write_text("signed\n")
        git(work, "add", "-A")
        git(work, "-c", "commit.gpgsign=true", "commit", "-q", "-S", "-m", "signed")
        git(work, "push", "-q", "origin", "main")
        git(work, "fetch", "-q", "origin", "main")
        r = run_tag(work)
        ok("happy path: exits 0", r.returncode == 0, f"rc={r.returncode} {r.stdout[-400:]}")
        ok("happy path: the tag exists locally", tag_exists(work))
        pushed = subprocess.run(["git", "ls-remote", "--tags", "origin"], cwd=work,
                                capture_output=True, text=True).stdout
        ok("happy path: the tag was PUSHED", "refs/tags/v9.9.9" in pushed, pushed)
        ok("happy path: it is an ANNOTATED tag",
           subprocess.run(["git", "cat-file", "-t", "v9.9.9"], cwd=work,
                          capture_output=True, text=True).stdout.strip() == "tag")
        ok("happy path: GATE5's rc is REPORTED, not discarded",
           re.search(r"GATE5 closure gate \(advisory\) rc=\d", r.stdout) is not None,
           r.stdout[-300:])
        # RQ-83-CANCELGAP (#1484): GATE2b must RUN and report, not be skipped.
        # A gate that never executes is the shape this whole lane is about.
        ok("happy path: GATE2b's unverified-check scan RAN and reported its rc",
           re.search(r"GATE2b unverified-check scan rc=\d", r.stdout) is not None,
           r.stdout[-300:])

print("\nPART 2 — STRUCTURE, each assertion proven non-vacuous")
TEXT = SCRIPT.read_text()

STATIC = [
    # RQ-83-CANCELGAP (#1484). Proven non-vacuous by the harness below, which
    # re-runs each assertion against a copy with the construct removed.
    ("GATE2b refuses on an UNVERIFIED check-run, and sets G2 rather than only printing",
     # Anchored on the REFUSAL branch, not on the --unverified-on call. The first
     # version anchored on the call and matched NON-GREEDILY to the first `G2=1`
     # after it — which is the rc=2 branch's, not the refusal branch's — so the
     # mutation removed one instance while the regex was satisfied by another.
     # The harness caught it as vacuous twice before this anchor was right.
     re.compile(r'elif \[ "\$G2B" != "0" \][\s\S]{0,700}?G2=1'),
     # The mutation must remove the property the REGEX depends on. A first version
     # of this entry mutated `G2B=$?`, which the regex never looks at, so the
     # harness correctly reported the assertion VACUOUS — a check that passes with
     # its own subject deleted. The target is the G2=1 that makes the refusal
     # BINDING rather than merely printed.
     # And the replacement must remove the literal `G2=1`, not comment it out:
     # `: # G2=1` still CONTAINS the substring the regex looks for, so the
     # harness reported vacuous a third time. Verified before writing.
     '  G2=1\nfi\necho "  GATE2b', '  true\nfi\necho "  GATE2b'),
    ("GATE2b distinguishes 'could not JUDGE' (rc=2) from 'the answer is no'",
     re.compile(r'\[ "\$G2B" = "2" \]'),
     '[ "$G2B" = "2" ]', '[ "$G2B" = "999" ]'),
    ("GATE2b calls merge_gate rather than carrying a SECOND list of bad states",
     re.compile(r'merge_gate\.py --unverified-on'),
     'merge_gate.py --unverified-on', 'merge_gate.py --no-such-mode'),
    ("the fetch's rc is checked",
     re.compile(r"git fetch -q origin main \|\|"),
     "git fetch -q origin main ||", "git fetch -q origin main #"),
    ("the ff-merge's rc is checked",
     re.compile(r"git merge --ff-only origin/main[^\n]*\n\s*\|\|"),
     "\\\n  || { echo \"  REFUSE: main is not fast-forwardable", "\\\n  # "),
    ("HEAD is asserted equal to origin/main",
     re.compile(r'\[ "\$HEAD_SHA" = "\$ORIGIN_SHA" \]'),
     '[ "$HEAD_SHA" = "$ORIGIN_SHA" ]', '[ 1 = 1 ]'),
    ("the leftover-tag check uses --verify --quiet, never rev-parse's stdout",
     re.compile(r'git rev-parse --verify --quiet "\$VER"'),
     'git rev-parse --verify --quiet "$VER"', 'git rev-parse "$VER"'),
    # NOTE: `git ls-remote --tags origin` also appears in the W2b REFUSE MESSAGE,
    # so a replace() of that bare string hits the message first and leaves the code
    # intact — the mutation then changes nothing and the non-vacuity check fails.
    # Anchor on the code line's own tail instead.
    ("the G3 delete is gated on ls-remote, not on an exit code",
     re.compile(r'! git ls-remote --tags origin "refs/tags/\$VER"'),
     '! git ls-remote --tags origin "refs/tags/$VER"', 'false'),
    ("GATE5's exit code is captured",
     re.compile(r"^G5=\$\?", re.M), "G5=$?", "# G5 not captured"),
    ("the push is the last link of an && chain, never a bare line",
     re.compile(r'git push origin "\$VER" \\\n\s*&& echo "  PUSHED'),
     'git push origin "$VER" \\\n  && echo "  PUSHED',
     'git push origin "$VER"\necho "  PUSHED'),
    ("the tag is created only after the G1/G2/G4 decision",
     re.compile(r'\[ "\$G1" = "0" \] && \[ "\$G2" = "0" \] && \[ "\$G4" = "0" \][\s\S]{0,400}?git tag -a "\$VER"'),
     '[ "$G1" = "0" ] && [ "$G2" = "0" ] && [ "$G4" = "0" ]', '[ 1 = 1 ]'),
]
for name, rx, present, removed in STATIC:
    ok(f"static: {name}", rx.search(TEXT) is not None)
    mutated = TEXT.replace(present, removed, 1)
    ok(f"  ...and the assertion is NON-VACUOUS (reds on a copy without it)",
       mutated != TEXT and rx.search(mutated) is None,
       "removing the property did not break the assertion")

print(f"\ntag-release-tests: {len(fails)} failure(s) over {len(ran)} assertion(s)")
if not ran:
    print("REFUSE: zero assertions ran — a vacuous pass")
    sys.exit(2)
sys.exit(1 if fails else 0)
