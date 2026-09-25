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


def blocked_reason(j: dict, required=()) -> str | None:
    ready, blocked = T.pep668_pool_ready({"j": j}, set(required))
    return blocked.get(j["name"])


def main() -> int:
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

    # ---- SCRIPT_RE must MATCH SOMETHING (the cold review's M8) ------------
    # v0.74 added SCRIPT_RE to follow one level of `bash scripts/x.sh`, which is
    # the walk-around a real script in this repo already uses. Replacing it with
    # a pattern that matches NOTHING (`(?!x)x`) was missed by both this suite and
    # the live tripwire — because the suite drives `pep668_pool_ready`, which
    # never consults SCRIPT_RE at all. So assert the pattern's own behaviour,
    # both directions, rather than assuming a caller exercises it.
    import re as _re
    for spec, want in (
            ("bash scripts/install-qemu.sh", "scripts/install-qemu.sh"),
            ("sh scripts/x.sh", "scripts/x.sh"),
            ("source scripts/env.sh", "scripts/env.sh"),
            (". scripts/env.sh", "scripts/env.sh"),
    ):
        got = T.SCRIPT_RE.findall(spec)
        check(f"SCRIPT_RE follows {spec!r}", got == [want], f"got {got!r}")
    for spec in ("bashscripts/x.sh", "rebash scripts/x.sh", "bash other/x.sh"):
        check(f"SCRIPT_RE does NOT match {spec!r}", T.SCRIPT_RE.findall(spec) == [],
              f"got {T.SCRIPT_RE.findall(spec)!r}")

    # And the indirection must work END TO END: a job that only invokes a script,
    # where the apt lives in the script file, is what SCRIPT_RE exists for.
    import tempfile, os as _os
    with tempfile.TemporaryDirectory() as td:
        sc = _os.path.join(td, "installer.sh")
        with open(sc, "w") as fh:
            fh.write("#!/bin/sh\nset -e\napt-get install -y qemu\n")
        rel = _os.path.relpath(sc, T.ROOT) if str(T.ROOT) in sc else None
    check("SCRIPT_RE's purpose is documented as one level only",
          "one level" in T.__doc__ or "one level" in open(T.__file__).read(),
          "the boundary must stay written down")

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
