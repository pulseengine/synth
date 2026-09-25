#!/usr/bin/env python3
"""RQ-75-APTSHAPE (#1062): drive `pep668_pool_ready` — the tripwire's own
decision — against RECORDED job dicts.

WHY. The tripwire has only ever been run against the LIVE `ci.yml`. That is one
input, it changes under you, and it cannot express the case you care about: a
job that WOULD be blocked. So every claim about what the detector sees was a
claim about one file on one day, and v0.74 recorded nine spellings it misses as
a docstring LIST — prose, which does not go red.

AND THE "LATENT POPULATION" FRAMING WAS FALSE, twice over. FIVE required
contexts run self-hosted today (Clippy, Format, Version Pin Sweep, Claim Check,
Rivet Validation), and `pep668_pool_ready`'s required-context branch fires FOUR
times on the live file — `ci_pool_tripwire.py` prints `blocked 4 required`. So
neither "none is self-hosted" nor "the decisive branch is never taken" holds.

What IS empty is the intersection the apt guard exists for: a required context
that is self-hosted AND needs apt. That is the honest statement, and it is why
driving this decision against RECORDED jobs still matters — the live file cannot
express the case the guard was built for, even though it does exercise the other
branches.

THE DEFECT THIS PINS. Both scans read `str(job)`, a dict REPR, where a newline
renders as backslash + `n`. So `\\bapt` could not match an installer that was not
the FIRST TOKEN of its `run:` value — the `n` of the escaped newline sits
directly before `apt`, and both are word characters. Measured at this lane's cut,
before the fix:

    apt first token             CAUGHT
    apt after another line      MISSED     <- swapping two lines flips it
    apt after a comment         MISSED

Widening the alternation would not have touched it: the pattern was already
correct and was being handed text that could not match. `job_text()` joins the
job's real strings with real newlines, and all three are now caught.

WHAT STAYS UNMATCHED is asserted below rather than described, so the boundary is
executable. These are NOT pinned as a suppression table on purpose: a `KNOWN_*`
table would enter the `known_open_pins` ratchet, which must FALL, and a detector
limitation is not an oracle observing a wrong answer. They are recorded here as
what they are — the reason the real check is executing the install step under
`no_new_privs`, which needs execution and is a v0.76 candidate.
"""

from __future__ import annotations

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import ci_pool_tripwire as T  # noqa: E402

FAILS = 0


def check(name: str, cond: bool, detail: str = "") -> None:
    global FAILS
    if cond:
        print(f"  ok   {name}")
    else:
        print(f"  FAIL {name} {detail}")
        FAILS += 1


def job(run: str, name: str = "Some Job", runs_on=None) -> dict:
    return {"name": name,
            "runs-on": runs_on if runs_on is not None else T.EXACT_LABEL,
            "steps": [{"name": "do it", "run": run}]}


# =====================================================================
# RQ-76-RECORDSHAPE (#1062): the recording, measured against the real file.
#
# v0.75 drove this decision against recorded jobs for the first time. The
# recording was the residual: `job()` above builds a job of exactly three keys
# whose single step has exactly two. The live `ci.yml` is not shaped like that,
# and `job_text()` is a fully general recursion that collects strings from
# ANYWHERE in the job — so an installer sitting in a `uses:`+`with:` step or a
# job-level `env:` IS collected and IS matched, and was never tested. Those
# paths were UNTESTED, NOT UNREACHABLE, which is a different and worse thing:
# the gate had coverage nobody had exercised.
#
# The guard below is NOT "assert the recording has more fields". A hand-written
# recording with more fields is still authored; it moves the fiction one field
# further out. It DERIVES the live key population from `ci.yml` and REDS when
# the real file carries a key no recorded shape can produce. That is what makes
# it survive the next workflow edit rather than this one.
# =====================================================================

CI_YML = pathlib.Path(__file__).resolve().parents[1] / ".github/workflows/ci.yml"


def live_shape() -> tuple[dict, dict]:
    """The key populations of the REAL workflow, derived at run time."""
    import collections

    import yaml

    if not CI_YML.exists():
        sys.exit(f"REFUSE: {CI_YML} not found — cannot derive the live shape")
    jobs = (yaml.safe_load(CI_YML.read_text()) or {}).get("jobs") or {}
    if not jobs:
        sys.exit("REFUSE: ci.yml parsed to ZERO jobs; the comparison would be vacuous")
    job_keys = collections.Counter(k for j in jobs.values() for k in j)
    step_keys = collections.Counter(
        k
        for j in jobs.values()
        for st in (j.get("steps") or [])
        if isinstance(st, dict)
        for k in st
    )
    return dict(job_keys), dict(step_keys)


def shaped_jobs(run: str) -> dict[str, dict]:
    """Recorded jobs that between them carry every key the live file uses.

    Each shape puts `run` somewhere a real workflow actually puts a command, so
    a narrowing of `job_text` to one surface is caught by whichever shape it
    stopped reading.
    """
    return {
        # `uses:` + `with:` — 262 and 133 live steps. An action input is a
        # place a command genuinely lives (`with: {run: ...}`, script inputs).
        "uses-with": {
            "name": "uses-with",
            "runs-on": T.EXACT_LABEL,
            "steps": [{"name": "act", "uses": "some/action@v1", "with": {"run": run}}],
        },
        # job-level `env:` — 7 live jobs.
        "job-env": {
            "name": "job-env",
            "runs-on": T.EXACT_LABEL,
            "env": {"PREP": run},
            "steps": [{"name": "noop", "run": "true"}],
        },
        # step-level `env:` — 41 live steps.
        "step-env": {
            "name": "step-env",
            "runs-on": T.EXACT_LABEL,
            "steps": [{"name": "noop", "run": "true", "env": {"PREP": run}}],
        },
        # `if:` + `id:` + `continue-on-error:` + `timeout-minutes:` + `needs:`
        # — the remaining live keys, carried together so the coverage check
        # below has a producer for each without inventing five more jobs.
        "guarded": {
            "name": "guarded",
            "runs-on": T.EXACT_LABEL,
            "needs": ["other"],
            "timeout-minutes": 5,
            "steps": [
                {
                    "name": "maybe",
                    "id": "maybe",
                    "if": "always()",
                    "continue-on-error": True,
                    "timeout-minutes": 5,
                    "run": run,
                }
            ],
        },
    }


def _keys_of(jobs: dict) -> tuple[set, set]:
    jk = {k for j in jobs.values() for k in j}
    sk = {
        k
        for j in jobs.values()
        for st in (j.get("steps") or [])
        if isinstance(st, dict)
        for k in st
    }
    return jk, sk


def check_recording_covers_live_shape() -> None:
    """RED when the live workflow carries a key no recorded shape produces."""
    live_jk, live_sk = live_shape()
    rec_jk, rec_sk = _keys_of(shaped_jobs("x"))
    rec_jk |= set(job("x"))  # the v0.75 factory is part of the recording too
    rec_sk |= {"name", "run"}
    missing_j = sorted(set(live_jk) - rec_jk)
    missing_s = sorted(set(live_sk) - rec_sk)
    check(
        "recording covers every JOB key the live ci.yml uses",
        not missing_j,
        f"- uncovered {missing_j} (live counts "
        f"{ {k: live_jk[k] for k in missing_j} })",
    )
    check(
        "recording covers every STEP key the live ci.yml uses",
        not missing_s,
        f"- uncovered {missing_s} (live counts "
        f"{ {k: live_sk[k] for k in missing_s} })",
    )
    print(
        f"  ...derived from ci.yml: job keys {sorted(live_jk)}; "
        f"step keys {sorted(live_sk)}"
    )


def blocked_reason(j: dict, required=()) -> str | None:
    ready, blocked = T.pep668_pool_ready({"j": j}, set(required))
    return blocked.get(j["name"])


def main() -> int:
    # ---- RQ-76-RECORDSHAPE: is the recording shaped like the real file? --
    check_recording_covers_live_shape()

    # Every shape must reach the SAME verdict: `job_text` collects strings
    # from anywhere in the job, so an installer hidden in any of them blocks
    # the job just as one in `steps[].run` does. A narrowing of `job_text` to
    # one surface fails whichever shape it stopped reading — which is the
    # measurement, not the count of assertions.
    for shape, j in shaped_jobs("sudo apt-get install -y cowsay").items():
        check(f"apt inside a real shape is blocked: {shape}",
              blocked_reason(j) is not None,
              "- job_text did not reach this surface")
    for shape, j in shaped_jobs("echo hello").items():
        check(f"a benign command in the same shape is NOT blocked: {shape}",
              blocked_reason(j) is None,
              "- false positive")

    # ---- the position defect, in both directions -------------------------
    check("apt as the FIRST token is blocked",
          blocked_reason(job("apt-get install -y x\nset -euo pipefail")) is not None)
    check("apt AFTER another line is blocked (the v0.74 miss)",
          blocked_reason(job("set -euo pipefail\napt-get install -y x")) is not None,
          "this is the dict-repr blindness; it must not come back")
    check("apt after a comment line is blocked",
          blocked_reason(job("# prep the runner\napt-get install -y x")) is not None)
    check("bare `apt` without -get is blocked",
          blocked_reason(job("set -e\napt install -y x")) is not None)
    check("sudo anywhere is blocked",
          blocked_reason(job("set -e\nsudo chmod +x thing")) is not None)

    # ---- the NEGATIVE control: a clean job must NOT be blocked -----------
    # Without this every assertion above is satisfied by a detector that blocks
    # everything, which is the vacuity the rest of this family keeps finding.
    check("a job with no installer is READY, not blocked",
          blocked_reason(job("cargo test --workspace")) is None,
          "a detector that blocks everything proves nothing")
    check("a job mentioning `adapter` is NOT blocked (no false substring)",
          blocked_reason(job("cargo run -- --adapter foo")) is None)

    # ---- the other two branches of the same decision ---------------------
    check("a REQUIRED context on this pool is blocked as a deadlock",
          "required context" in (blocked_reason(
              job("cargo test", name="Test"), required={"Test"}) or ""))
    check("pip install WITHOUT the PEP 668 fallback is blocked",
          blocked_reason(job("pip install pyelftools")) is not None)
    check("pip install WITH the fallback is allowed",
          blocked_reason(job("pip install --break-system-packages pyelftools")) is None)

    # ---- a job on another pool is out of scope entirely -----------------
    # `EXACT_LABEL` is "ubuntu-latest": this function asks which ubuntu-latest
    # jobs could MOVE to self-hosted, so a job ALREADY self-hosted is not a
    # candidate. This assertion first passed "ubuntu-latest" as the off-pool
    # value — which is the label itself — and failed. My test was wrong, not the
    # code; recorded because it is the second such error in this release.
    check("a job already on self-hosted is not a move candidate",
          blocked_reason(job("apt-get install -y x",
                             runs_on=["self-hosted", "linux"])) is None)

    # ---- SCRIPT_RE, driven on REAL input shapes (round 1's M8 fix, fixed) ---
    # Round 1 asserted SCRIPT_RE's behaviour on bare specs like
    # "bash scripts/install-qemu.sh" — every one starting at OFFSET 0. Round 2
    # prepended `^` to the pattern and ALL EIGHT assertions stayed green while the
    # real indirection died, because the live input is `job_text(j)`, which starts
    # with the job's NAME. That is the same position blindness RQ-75-APTSHAPE
    # fixed in APT_RE, reappearing in the sibling pattern one function away.
    #
    # So the specs are now embedded the way the real text embeds them: inside a
    # multi-line job body, never at offset 0.
    for spec, want in (
            ("Some Job\nsteps\nbash scripts/install-qemu.sh\n", "scripts/install-qemu.sh"),
            ("name\nrun\nset -e\nsh scripts/x.sh\n", "scripts/x.sh"),
            ("prep\n  source scripts/env.sh\n", "scripts/env.sh"),
            ("prep\n  . scripts/env.sh\n", "scripts/env.sh"),
    ):
        got = T.SCRIPT_RE.findall(spec)
        check(f"SCRIPT_RE follows a script invocation MID-TEXT ({want})",
              got == [want], f"got {got!r} from {spec!r}")
    for spec in ("job\nbashscripts/x.sh\n", "job\nrebash scripts/x.sh\n",
                 "job\nbash other/x.sh\n"):
        check(f"SCRIPT_RE does NOT match {spec.strip()!r}",
              T.SCRIPT_RE.findall(spec) == [], f"got {T.SCRIPT_RE.findall(spec)!r}")

    # END TO END through job_text, which is the only input that matters.
    # Round 1 wrote a block here that created an installer.sh, computed a `rel`
    # it never read, left an unused import, and whose only assertion was a
    # source-text search for the string "one level" — which passed on a comment.
    # It was unwireable as written and asserted nothing; this replaces it.
    j = job("set -euo pipefail\nbash scripts/install-qemu.sh", name="Indirect Job")
    body = T.job_text(j)
    check("job_text output does NOT start with the run: command (offset != 0)",
          not body.startswith("set -euo pipefail"), f"body starts {body[:30]!r}")
    check("SCRIPT_RE finds the invocation in real job_text output",
          "scripts/install-qemu.sh" in T.SCRIPT_RE.findall(body),
          f"findall={T.SCRIPT_RE.findall(body)!r} over {body[:70]!r}")
    # and the followed script really does contain an installer today, which is
    # what makes the indirection a live hole rather than a hypothetical
    inst = T.ROOT / "scripts/install-qemu.sh"
    if inst.is_file():
        check("the followed script really contains an installer",
              bool(T.APT_RE.search(inst.read_text(errors="ignore"))),
              "scripts/install-qemu.sh no longer carries apt — update the note")

    # ---- THE BOUNDARY, asserted so it is executable rather than prose ----
    # Each of these SHOULD ideally be blocked and is not. They are recorded as
    # known-unmatched, and the assertion is that they remain unmatched — so a
    # future change that starts catching one fails here and forces the
    # disclosure in `job_text` to be updated with it.
    unmatched = {
        "aptitude install": "aptitude install -y x",
        "dpkg -i": "dpkg -i thing.deb",
        "./scripts/x.sh (no bash prefix)": "./scripts/install-qemu.sh",
        "bash .github/x.sh (outside scripts/)": "bash .github/install.sh",
        "python wrapper": "python3 scripts/install-qemu.py",
        "make wrapper": "make -f scripts/install.mk",
    }
    for label, run in unmatched.items():
        check(f"boundary: {label} is still NOT matched (documented)",
              blocked_reason(job(run)) is None,
              "it is now caught — update job_text()'s disclosure and remove "
              "this line")

    print(f"\nci-pool-tripwire-tests: {FAILS} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
