#!/usr/bin/env python3
"""Gate the mutation survey's CI summary lines — arithmetically.

WHY THIS FILE EXISTS (#1243). The gate used to be two `grep -E` assertions:

    ^MUTANTS-CI subset=[4-9][0-9]* controls=[2-9][0-9]* non-killed=[2-9][0-9]* failures=0$
    ^MUTANTS-REACH-WIDE entries=[1-9][0-9]* reached=[1-9][0-9]* unreached=0$

`[4-9][0-9]*` was written to mean "at least 4". It means "the first digit is 4
through 9", so it accepted 4-9 and 40-99 and REJECTED 10-39. RQ-66-DELETE grew
the pinned subset from 7 to 10 and the job failed while reporting a healthy
result — every control killed by its own named oracle, every survivor
reproduced, `failures=0`. The gate reddened because the thing it guards got
BIGGER.

That is the vacuity class this repo keeps finding in its own checkers: an
assertion that looks like it checks a QUANTITY and actually checks a SHAPE. A
floor is arithmetic; a character class over digits is not a floor. It also
failed silently — `grep -q` exits 1 with no indication of which field was
wrong — so the fix prints the offending value.

Floors here are LOWER BOUNDS that must not regress; exactness assertions
(`failures`, `unreached`) stay exact. `reached == entries` is checked as an
identity rather than as two independent floors, because a wide-reach probe
that reaches fewer sites than it has entries is the failure this gate exists
to catch.
"""

from __future__ import annotations

import re
import sys

# field -> (line prefix, kind, bound). kind "floor" is `value >= bound`;
# kind "exact" is `value == bound`.
CHECKS = (
    ("subset",     "MUTANTS-CI",         "floor", 4),
    ("controls",   "MUTANTS-CI",         "floor", 2),
    ("non-killed", "MUTANTS-CI",         "floor", 2),
    ("failures",   "MUTANTS-CI",         "exact", 0),
    ("entries",    "MUTANTS-REACH-WIDE", "floor", 1),
    ("reached",    "MUTANTS-REACH-WIDE", "floor", 1),
    ("unreached",  "MUTANTS-REACH-WIDE", "exact", 0),
)


def find_line(text: str, prefix: str) -> str | None:
    """Last line starting with `prefix ` — the survey may print progress first."""
    hits = [ln for ln in text.splitlines() if ln.startswith(prefix + " ")]
    return hits[-1] if hits else None


def field(line: str, name: str) -> int | None:
    """`name=<int>` on a whitespace boundary.

    The boundary matters: `reached` is a substring of `unreached`, and without
    it a lax pattern would read the wrong number and the gate would pass on a
    tree it should refuse.
    """
    m = re.search(rf"(?:^|\s){re.escape(name)}=(\d+)(?=\s|$)", line)
    return int(m.group(1)) if m else None


def gate(text: str) -> list[str]:
    """Return the list of complaints; empty means the gate passes."""
    bad: list[str] = []
    lines: dict[str, str | None] = {}
    for prefix in ("MUTANTS-CI", "MUTANTS-REACH-WIDE"):
        lines[prefix] = find_line(text, prefix)
        if lines[prefix] is None:
            bad.append(f"{prefix}: line absent — the survey did not report it")

    for name, prefix, kind, bound in CHECKS:
        line = lines.get(prefix)
        if line is None:
            continue
        value = field(line, name)
        if value is None:
            bad.append(f"{prefix}: field {name!r} absent from {line!r}")
        elif kind == "floor" and value < bound:
            bad.append(f"{prefix}: {name}={value} is below its floor of {bound}")
        elif kind == "exact" and value != bound:
            bad.append(f"{prefix}: {name}={value}, must be exactly {bound}")

    rw = lines.get("MUTANTS-REACH-WIDE")
    if rw is not None:
        entries, reached = field(rw, "entries"), field(rw, "reached")
        if entries is not None and reached is not None and reached != entries:
            bad.append(
                f"MUTANTS-REACH-WIDE: reached={reached} != entries={entries} — "
                "a DEAD entry stopped reaching"
            )
    return bad


# --- the gate's own red-first evidence -------------------------------------
# A gate nobody has watched fire is a gate being guessed at. These cases run
# on every invocation (`--selftest`) and in `scripts/test_mutation_survey.py`.
SELFTEST = (
    # (label, text, expect_pass)
    ("the exact CI output that #1243 rejected",
     "MUTANTS-CI subset=10 controls=3 non-killed=7 failures=0\n"
     "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n", True),
    ("the pre-RQ-66 shape the old regex accepted",
     "MUTANTS-CI subset=7 controls=3 non-killed=4 failures=0\n"
     "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n", True),
    ("subset below its floor still fails",
     "MUTANTS-CI subset=3 controls=3 non-killed=7 failures=0\n"
     "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n", False),
    ("a real failure is still a failure",
     "MUTANTS-CI subset=10 controls=3 non-killed=7 failures=1\n"
     "MUTANTS-REACH-WIDE entries=4 reached=4 unreached=0\n", False),
    ("a DEAD entry that stopped reaching fails",
     "MUTANTS-CI subset=10 controls=3 non-killed=7 failures=0\n"
     "MUTANTS-REACH-WIDE entries=4 reached=3 unreached=1\n", False),
    ("reached != entries fails even with unreached=0",
     "MUTANTS-CI subset=10 controls=3 non-killed=7 failures=0\n"
     "MUTANTS-REACH-WIDE entries=4 reached=3 unreached=0\n", False),
    ("'reached' is not read out of 'unreached'",
     "MUTANTS-CI subset=10 controls=3 non-killed=7 failures=0\n"
     "MUTANTS-REACH-WIDE entries=1 unreached=0 reached=1\n", True),
    ("a missing line fails rather than passing vacuously",
     "MUTANTS-CI subset=10 controls=3 non-killed=7 failures=0\n", False),
)


def selftest() -> int:
    failures = 0
    for label, text, expect_pass in SELFTEST:
        bad = gate(text)
        ok = (not bad) == expect_pass
        print(f"  {'ok  ' if ok else 'FAIL'}  {label}")
        if not ok:
            print(f"        expected {'pass' if expect_pass else 'fail'}, got {bad or 'pass'}")
            failures += 1
    print(f"MUTANTS-GATE-SELFTEST cases={len(SELFTEST)} failures={failures}")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if len(argv) == 2 and argv[1] == "--selftest":
        return selftest()
    if len(argv) != 2:
        print("usage: ci_mutants_gate.py <mutants-ci.txt> | --selftest", file=sys.stderr)
        return 2
    with open(argv[1], encoding="utf-8") as fh:
        text = fh.read()
    bad = gate(text)
    for complaint in bad:
        print(f"mutants-gate: {complaint}", file=sys.stderr)
    if bad:
        print(f"mutants-gate: {len(bad)} assertion(s) failed", file=sys.stderr)
        return 1
    print("MUTANTS-GATE ok — floors met, exact fields exact, reach complete")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
