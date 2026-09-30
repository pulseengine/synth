#!/usr/bin/env python3
# ci-status: wired — `--self-test` runs in the required `claim-check` job, and the
# floor itself gates the artifact-citation step in the same job.
"""Gate the artifact-citation summary line — ARITHMETICALLY (#1435).

WHY THIS FILE EXISTS. The step used to assert its non-vacuity floor with a grep:

    ^artifact citations: … in 1[0-9]{2,} artifact files

Its own comment said that "pins the artifact-FILE count above 100". `1[0-9]{2,}`
means THE FIRST DIGIT IS 1. It accepts 100-199 and 1000-1999 and REJECTS 200-999.

It fired for real: the v0.78 planning PR took the artifact-file count from 199 to
206, and `Claim Check` — one of the NINE REQUIRED contexts — went red while the
gate it guards reported a healthy result (33 cited, 32 resolve, 0 false claims).
THE GATE REDDENED BECAUSE THE THING IT GUARDS GOT BIGGER.

This is the SECOND live instance of the class `scripts/ci_mutants_gate.py` was
written to end, whose docstring already states the principle:

    A floor is arithmetic; a character class over digits is not a floor. It also
    failed silently — `grep -q` exits 1 with no indication of which field was
    wrong — so the fix prints the offending value.

v0.66.0 fixed the MUTATION-SURVEY floors and #1243 was closed on that evidence.
The class was never swept, so this instance sat in a different step of the same
workflow with the same defect. v0.77 re-scoped #1243, found it already delivered
for the instance it checked, and recorded a refutation — which is exactly how a
class-wide defect hides behind a correctly-closed issue.

WHAT THIS ASSERTS, and why each part is here:

  * The summary line must be PRESENT. A floor that matches nothing and a floor
    that is satisfied are otherwise the same exit code — and #1333 caused exactly
    that here once already, when the summary's wording moved and the old pattern
    silently matched nothing while the gate passed.
  * Every field is parsed as an INTEGER and compared with `>=`. No digit classes.
  * A failure PRINTS the field, its value and its floor. `grep -q` said nothing.
  * `0 false claim(s)` is an EXACTNESS assertion, not a floor: one false claim is
    a failure regardless of how large the population is.

Usage:
    python3 scripts/ci_citation_floor.py /tmp/artifact-cites.log
    python3 scripts/ci_citation_floor.py --self-test
"""
from __future__ import annotations

import re
import sys

# Floors are LOWER BOUNDS that must not regress. They are deliberately far below
# the live values: this is a non-vacuity floor, not a ratchet. The ratchets live
# in claims.yaml and are slack-free; a floor here exists only to catch a
# collapsed population (the pre-#1333 non-recursive glob saw 30 files and ZERO
# release artifacts).
FLOORS = {
    "cited": 1,
    "test_names": 1,
    "test_targets": 1,
    "artifact_files": 100,
}

LINE = re.compile(
    r"^artifact citations: (?P<cited>\d+) cited "
    r"\((?P<target>\d+) target, (?P<filter>\d+) filter\) "
    r"over (?P<test_names>\d+) test names / (?P<test_targets>\d+) test targets "
    r"in (?P<artifact_files>\d+) artifact files"
    r"(?: — (?P<resolve>\d+) resolve, (?P<false_claims>\d+) false claim)?",
    re.M,
)


def check(text: str) -> list[str]:
    """Returns a list of failure strings; empty means the floor holds."""
    m = LINE.search(text)
    if m is None:
        return [
            "REFUSE: the artifact-citation summary line is ABSENT from the output. "
            "That is not a satisfied floor, it is a floor about nothing — the #1333 "
            "shape, where the summary's wording moved and the old pattern matched "
            "nothing while the gate itself passed. Re-read "
            "artifact_citation_check.py's final print and update this parser."
        ]
    fails = []
    for field, floor in FLOORS.items():
        got = int(m.group(field))
        if got < floor:
            fails.append(
                f"FLOOR: {field}={got} is below its floor of {floor} — the population "
                f"collapsed, or the gate ran over the wrong glob"
            )
    fc = m.group("false_claims")
    if fc is not None and int(fc) != 0:
        # EXACTNESS, not a floor: one false claim fails at any population size.
        fails.append(f"EXACT: false_claims={fc}, want 0 — an artifact cites a test "
                     f"that does not exist")
    return fails


# An ARITHMETIC floor on this self-test's OWN work, and the reason it is here is
# itself a finding: `shipped_feature_census.py` added exactly this guard in the
# SAME release and cited THIS file's lane (#1435) as its precedent — so the idea
# was invented here and never transferred back. v0.78's round-1 gate review
# measured the gap: deleting the `an ABSENT line REFUSES` assertion took the run
# from 15 printed assertions to 14 with rc=0 and "0 failure(s)".
#
# A FLOOR, not an equality: adding an assertion must never red, losing one must.
MIN_ASSERTIONS = 15


def self_test() -> int:
    # A FROZEN SAMPLE of the real line, captured 2026-09-30 at the v0.78 cut —
    # NOT the current output, and deliberately not kept in step with it. The
    # figures move with the corpus every release (the tree emitted `7275 test
    # names / 209 artifact files` when this comment was written), and a fixture
    # that has to be re-synced each time is a fixture nobody trusts. What this
    # sample pins is the SHAPE the parser must read. The LIVE line is checked by
    # the ci.yml step that runs this script against the real
    # `/tmp/artifact-cites.log`, which is where a real drift would surface.
    live = ("artifact citations: 33 cited (15 target, 18 filter) over 7274 test "
            "names / 133 test targets in 206 artifact files — 32 resolve, "
            "0 false claim(s), 1 planned-but-unwritten")
    fails = []
    ran = []

    def ok(name, cond):
        ran.append(name)
        print(f"  {'ok  ' if cond else 'FAIL'} {name}")
        if not cond:
            fails.append(name)

    ok("the live line PASSES", check(live) == [])
    # THE REGRESSION THIS FILE EXISTS TO PREVENT, pinned as a negative control:
    # the old digit-class floor REJECTED this very line. If anyone reverts to a
    # shape check, this assertion is what notices.
    old = re.compile(r"in 1[0-9]{2,} artifact files")
    ok("RQ-78-FLOORREGEX2: the OLD digit-class regex REJECTS the live line, "
       "which is the defect this file replaces — pinned as a negative control "
       "so a revert to a shape check is noticed",
       old.search(live) is None)
    ok("the OLD regex accepts 199 but not 206 (first-digit, not a floor)",
       old.search(live.replace("206 artifact", "199 artifact")) is not None
       and old.search(live) is None)
    # The arithmetic floor is monotone where the regex was not.
    for n in (100, 199, 200, 206, 999, 1000, 5000):
        ok(f"arithmetic floor ACCEPTS {n} artifact files",
           check(live.replace("206 artifact", f"{n} artifact")) == [])
    ok("arithmetic floor REJECTS 99 artifact files",
       any("artifact_files=99" in f for f in check(live.replace("206 artifact", "99 artifact"))))
    ok("a collapsed population is named in the failure",
       any("artifact_files=30" in f for f in check(live.replace("206 artifact", "30 artifact"))))
    ok("an ABSENT line REFUSES rather than passing",
       any(f.startswith("REFUSE:") for f in check("some unrelated output\n")))
    ok("a nonzero false-claim count FAILS at any size",
       any(f.startswith("EXACT:") for f in check(live.replace("0 false claim", "1 false claim"))))
    ok("zero cited is a floor failure, not a pass",
       any("cited=0" in f for f in check(live.replace("33 cited", "0 cited"))))
    print(f"ci-citation-floor-self-test: {len(ran)} assertions, "
          f"{len(fails)} failure(s)")
    if len(ran) < MIN_ASSERTIONS:
        print(f"REFUSE: only {len(ran)} assertions ran, floor is "
              f"{MIN_ASSERTIONS}. Assertions were REMOVED or the body stopped "
              f"early — '0 failures' from a test that did not run is exactly the "
              f"vacuous green a floor exists to make impossible.")
        return 1
    return 1 if fails else 0


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    with open(sys.argv[1], encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    fails = check(text)
    for f in fails:
        print(f)
    if fails:
        return 1
    m = LINE.search(text)
    print(f"citation floor OK: cited={m.group('cited')} "
          f"test_names={m.group('test_names')} "
          f"test_targets={m.group('test_targets')} "
          f"artifact_files={m.group('artifact_files')} "
          f"(floors {FLOORS})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
