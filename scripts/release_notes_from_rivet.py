#!/usr/bin/env python3
# ci-status: manual (release-time)
"""RQ-70-RIVETNOTES (#1337) — derive the release's artifact section from rivet, not from memory.

# The class this closes

The CHANGELOG's per-release section is hand-written prose ABOUT A TYPED SET rivet
can diff. Every release, someone re-types which artifacts landed and what they
claim — and v0.66 filed two of its OWN artifacts under `[Unreleased]` because the
list was remembered rather than derived. The artifacts are structured data; the
diff is a command.

It also surfaces something no release has looked at: `rivet diff` reports the
DIAGNOSTIC DELTA between two trees. v0.69 shipped 22 new warnings nobody saw, and
v0.70's own planning PR added 21 more (#1337) — trailer-incompatible ids, a
`req-type` outside the schema's allowed set, and requirements with no incoming
`verifies` link. A release that cannot say whether it made the trace graph better
or worse is not reporting on itself.

# Why the version check is load-bearing, not hygiene

`~/.cargo/bin/rivet` on a developer machine is routinely an OLD build (the #1236 /
#1308 PATH-shadow class: the pulseengine rolling root rotated and a stale shim
stayed on PATH). Version skew here is not cosmetic — rivet 0.32 reports
"0 broken cross-refs" on a tree where resolution never RAN, which reads as a
clean bill of health. So this refuses to emit anything from a rivet older than
the version CI pins. A wrong answer is worse than no answer, and a confidently
clean wrong answer is worst.

# Anti-vacuity

A release whose derivation finds ZERO added artifacts is a BROKEN DERIVATION, not
a quiet release — the base ref is wrong, the source paths moved, or the extract
failed. It refuses rather than emitting an empty section that would read as
"nothing shipped".

Usage:
    python3 scripts/release_notes_from_rivet.py --base v0.69.0 [--rivet PATH]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# The version CI installs (see `Install rivet (pinned vX.Y.Z)` in ci.yml). Kept as
# a tuple so "newer is fine, older is refused" is expressible.
PINNED_RIVET = (0, 37, 0)

# The rivet.yaml `sources:` roots plus the config itself — what a diff needs from
# the base tree. Read from rivet.yaml rather than hardcoded, so a source moving is
# a loud extract failure and not a silently narrower diff.
CONFIG = "rivet.yaml"

VERSION_RE = re.compile(r"^rivet (\d+)\.(\d+)\.(\d+)")
def _entry_id(entry):
    """Normalise one `rivet diff` entry to `(id, changes)`.

    RQ-71 (#1337): rivet reports `added` and `removed` as bare id STRINGS but
    `modified` as `{"id": ..., "changes": [...]}`. This renderer f-stringed the
    entry directly, so a modified artifact printed its whole Python dict into
    the CHANGELOG:

        - *(modified)* **{'changes': ['field changed: issue-scope'], 'id': 'RQ-70-NPA'}**

    The path had never run. v0.70 shipped this tool and no release had modified
    a PRIOR release's artifact until v0.71 did (RQ-71-ISSUESCOPE applies
    `issue-scope: outlives` to two v0.70 artifacts), so the defect shipped
    behind a code path nothing reached — the same shape as the four gates v0.70
    found that could not fail.

    The `changes` list is kept rather than dropped: "which field moved on a
    shipped artifact" is exactly what a reader of a release note needs, and it
    is the reason a modified entry is richer than an added one.
    """
    if isinstance(entry, dict):
        return str(entry.get("id", entry)), [str(c) for c in (entry.get("changes") or [])]
    return str(entry), []


SUMMARY_RE = re.compile(r"^(\d+) added, (\d+) removed, (\d+) modified, (\d+) unchanged")
DIAG_RE = re.compile(
    r"^(\d+) new errors?, (\d+) resolved errors?, (\d+) new warnings?, (\d+) resolved warnings?"
)
ADDED_RE = re.compile(r"^\+ (\S+)\s+(.*)$")


def rivet_version(rivet: str) -> tuple[int, int, int]:
    out = subprocess.run([rivet, "--version"], capture_output=True, text=True)
    m = VERSION_RE.match(out.stdout.strip())
    if not m:
        sys.exit(
            f"FAIL: could not read a version from `{rivet} --version` "
            f"(got {out.stdout.strip()!r}). Refusing to derive release notes from "
            f"a tool that cannot state its own version."
        )
    return tuple(int(g) for g in m.groups())  # type: ignore[return-value]


def source_roots(root: Path) -> list[str]:
    """The paths rivet.yaml declares, so an extract covers exactly what a diff reads."""
    text = (root / CONFIG).read_text()
    roots = re.findall(r"^\s*-\s*path:\s*(\S+)", text, re.M)
    if not roots:
        sys.exit(f"FAIL: no `sources: - path:` entries in {CONFIG} — cannot bound the extract")
    return roots


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True, help="previous release tag, e.g. v0.69.0")
    ap.add_argument("--root", type=Path, default=REPO_ROOT)
    ap.add_argument("--rivet", default="rivet", help="rivet binary (default: PATH)")
    ap.add_argument(
        "--allow-older-rivet",
        action="store_true",
        help="escape hatch; prints a LOUD banner into the output so it cannot be pasted quietly",
    )
    a = ap.parse_args()

    ver = rivet_version(a.rivet)
    if ver < PINNED_RIVET and not a.allow_older_rivet:
        sys.exit(
            f"FAIL: rivet {'.'.join(map(str, ver))} is older than the CI pin "
            f"{'.'.join(map(str, PINNED_RIVET))} ({a.rivet}).\n"
            f"       An old rivet does not merely miss findings — 0.32 reports "
            f"'0 broken cross-refs' on a tree where resolution never ran, which "
            f"reads as a clean bill of health.\n"
            f"       Point --rivet at the pinned build (a stale ~/.cargo/bin/rivet "
            f"shadowing it is #1236/#1308), or pass --allow-older-rivet to emit "
            f"with a loud banner."
        )

    roots = source_roots(a.root)
    with tempfile.TemporaryDirectory() as td:
        base = Path(td) / "base"
        base.mkdir()
        archive = subprocess.run(
            ["git", "archive", a.base, *roots, CONFIG],
            cwd=a.root,
            capture_output=True,
        )
        if archive.returncode != 0:
            sys.exit(
                f"FAIL: `git archive {a.base}` failed — is the tag present "
                f"(a shallow clone has no tags)? {archive.stderr.decode()[:200]}"
            )
        subprocess.run(["tar", "-x", "-C", str(base)], input=archive.stdout, check=True)

        text = subprocess.run(
            [a.rivet, "diff", "--base", str(base), "--head", str(a.root)],
            capture_output=True,
            text=True,
        ).stdout
        js = subprocess.run(
            [a.rivet, "diff", "--base", str(base), "--head", str(a.root), "--format", "json"],
            capture_output=True,
            text=True,
        ).stdout

    try:
        data = json.loads(js)
    except json.JSONDecodeError:
        sys.exit("FAIL: rivet diff --format json produced no parseable object")

    added = data.get("added") or []
    # ANTI-VACUITY. Zero added artifacts means the derivation broke (wrong base,
    # moved sources, failed extract), not that a release shipped nothing.
    if not added:
        sys.exit(
            f"FAIL: rivet diff found ZERO added artifacts between {a.base} and the "
            f"working tree. That is a broken derivation, not a quiet release — "
            f"check the base tag and the rivet.yaml source paths. Refusing to emit "
            f"an empty section that would read as 'nothing shipped'."
        )

    titles = {}
    for line in text.splitlines():
        m = ADDED_RE.match(line)
        if m:
            titles[m.group(1)] = m.group(2).strip()

    diag = next((DIAG_RE.match(l) for l in text.splitlines() if DIAG_RE.match(l)), None)

    print(f"<!-- DERIVED by scripts/release_notes_from_rivet.py from `rivet diff` -->")
    print(f"<!-- base {a.base} · rivet {'.'.join(map(str, ver))} · do not hand-edit the lists -->")
    if ver < PINNED_RIVET:
        print(
            f"\n> **WARNING — derived with rivet {'.'.join(map(str, ver))}, older than "
            f"the CI pin {'.'.join(map(str, PINNED_RIVET))}.** An old rivet can report "
            f"a clean graph it never resolved; treat every number below as unverified."
        )
    print(f"\n### Artifacts ({data.get('summary', '')})\n")
    for aid in added:
        print(f"- **{aid}** — {titles.get(aid, '(title unavailable)')}")
    for entry in data.get("modified") or []:
        aid, changes = _entry_id(entry)
        why = f" — {', '.join(changes)}" if changes else ""
        print(f"- *(modified)* **{aid}**{why}")
    for entry in data.get("removed") or []:
        aid, _ = _entry_id(entry)
        print(f"- *(removed)* **{aid}**")

    print("\n### Trace-graph delta\n")
    if diag:
        ne, re_, nw, rw = (int(g) for g in diag.groups())
        print(f"- errors: **+{ne} / -{re_}**")
        print(f"- warnings: **+{nw} / -{rw}**")
        if ne:
            print(
                f"\n> {ne} NEW rivet ERROR(s) ship in this release. An error is a "
                f"broken trace, not a style note — resolve or record why before tagging."
            )
        if nw and not ne:
            print(
                f"\n> {nw} new warning(s), 0 new errors. Listed so the release says "
                f"whether it improved the trace graph or degraded it — v0.69 shipped "
                f"22 unseen (#1337)."
            )
    else:
        print("- _rivet printed no diagnostic summary line_ — parser or format drift, not a clean graph.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
