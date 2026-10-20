#!/usr/bin/env python3
"""RQ-88-PREPBUMP (#1550) — the topmost CHANGELOG release section must name the
version the workspace carries, checked on EVERY pull request.

WHY THIS EXISTS. The v0.87 release-prep PR (#1547) shipped the `[0.87.0]`
notes with the workspace still at 0.86.0. Every gate on that PR and on the next
one was green. The pretag conformance check caught it at step 0, but that check
runs only at the tag ritual, after every lane has merged, so the bump cost a
third PR and a further full CI cycle. Same gate, earlier window.

WHAT IT DERIVES, and from where. Both halves come from the shipped pretag gate
rather than from a second implementation: `workspace_version` and
`changelog_structure_verdict` are imported from `loop_conformance_check`. So
this check and step 0 cannot disagree about which version a tree carries.

THE WINDOW HAS TWO EDGES, and both are pinned by the self-test on REAL commits:

    d3c13c83  the v0.87 release prep: notes [0.87.0], workspace 0.86.0 -> RED
    f69d3548  the v0.87.0 release commit, bumped                   -> GREEN
    897dbf69  an ordinary mid-release tree (top section is the
              PREVIOUS release, workspace equal to it)             -> GREEN

The third case is the one that matters for adoption: a check that reds every
mid-release PR is a gate people route around. Equality of the two versions is
the whole rule, so mid-release (both at the last release) and a correct cut
(both at the new one) pass, and only the half-done cut fails.

The self-test needs git history; CI's Claim Check job checks out with
fetch-depth 0. Missing history is a FAILURE, not a skip: a self-test that
passes without its fixtures has said nothing.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from loop_conformance_check import (  # noqa: E402
    DERIVED_PASS,
    changelog_structure_verdict,
    workspace_version,
)

ROOT = Path(__file__).resolve().parent.parent

# (commit, expected status) — real history, not invented fixtures.
HISTORY = [
    ("d3c13c832704d18e80884ba85c7793a8bc44e43f", "FAIL"),  # v0.87 prep, bump missing
    ("f69d3548d5a0471583c53d9adced06638d85b533", "PASS"),  # v0.87.0 release commit
    ("897dbf69d1238d6717014959b28ab50b90e67cc8", "PASS"),  # mid-release (v0.88 planning)
]


def verdict(cargo_text: str, changelog_text: str) -> tuple[bool, str]:
    ws = workspace_version(cargo_text)
    if ws is None:
        return False, "no `[workspace.package] version` in Cargo.toml"
    status, detail = changelog_structure_verdict(changelog_text, ws)
    return status == DERIVED_PASS, f"workspace {ws}: {detail}"


def show(commit: str, path: str) -> str | None:
    p = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{commit}:{path}"],
        capture_output=True,
        text=True,
    )
    return p.stdout if p.returncode == 0 else None


def self_test() -> int:
    fails = 0
    for commit, want in HISTORY:
        cargo, cl = show(commit, "Cargo.toml"), show(commit, "CHANGELOG.md")
        if cargo is None or cl is None:
            print(f"  FAIL {commit[:8]}: history unavailable — a self-test without its fixtures proves nothing")
            fails += 1
            continue
        ok, detail = verdict(cargo, cl)
        got = "PASS" if ok else "FAIL"
        mark = "ok  " if got == want else "FAIL"
        fails += got != want
        print(f"  {mark} {commit[:8]} expected {want}, got {got} — {detail}")
    # A tree with NO workspace version must not pass by default.
    ok, _ = verdict("[package]\nversion = \"1.0.0\"\n", "## [1.0.0]\n- x\n")
    print(f"  {'ok  ' if not ok else 'FAIL'} a Cargo.toml without [workspace.package] is REFUSED")
    fails += ok
    print(f"release-version-check self-test: {'OK' if not fails else f'{fails} FAILURE(S)'}")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    ok, detail = verdict((ROOT / "Cargo.toml").read_text(), (ROOT / "CHANGELOG.md").read_text())
    print(f"release-version: {'OK' if ok else 'FAIL'} — {detail}")
    if not ok:
        print(
            "  The topmost CHANGELOG release section and the workspace version must move together.\n"
            "  A release-prep PR bumps every version site; see scripts/check_version_pins.py."
        )
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
