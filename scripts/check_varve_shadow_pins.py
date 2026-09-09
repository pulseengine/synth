#!/usr/bin/env python3
"""RQ-66-VARVE (#1236): known-open PATH-shadow pins for the varve toolchain pin.

`varve verify` (REQ-SHADOW-001) is varve's own PATH-shadowing oracle — not a
hand-written parser here, the shipped tool's own check. Wired into the
`rivet-federated` CI job (#1244), it found a REAL, reproduced-on-two-
different-self-hosted-runners hazard: `rivet` on the runner's PATH resolves
to an ambient `.cargo/bin/rivet` the required `rivet` job's
`cargo install --force --git` (no `--root`) leaves behind on a shared,
persistent machine, not to the varve-pinned copy (measured paths
`/var/lib/runners/runner9/.cargo/bin/rivet` and
`/var/lib/runners/runner12/.cargo/bin/rivet` — different runner, same
`.cargo/bin/rivet` suffix, which IS the mechanism: a plain
`cargo install` with no `--root` always lands there).

That hazard is real but not fixable inside this change (it needs a decision
about the OTHER job's install step, on shared infrastructure). Making the
job hard-fail forever on it is not "watched" in this release's sense
("watched, fixed, or deleted — there is no fourth") — a gate that is red on
every run trains everyone to ignore it and blocks unrelated work with it,
the exact failure mode RQ-66-PINDEBT's `known_open_pins` ratchet exists to
make visible and accountable instead of silently tolerated forever.

So: pin the KNOWN shadow exactly, the same shape as the parity oracle's and
the home-alias differential's `KNOWN_OPEN` tables (`scripts/repro/
home_alias_class_1189_differential.py`) — a dict literal countable by
`scripts/claim_check.py`'s `pin-table` measure (RQ-66-PINDEBT, #242)
without importing this file (it is parsed with `ast`, matching that
mechanism's own "never hand-tally, never import an oracle into the ledger"
rule). Register this file + `KNOWN_OPEN` under `known_open_pins.tables` in
claims.yaml once RQ-66-PINDEBT (#1242) is merged to this branch's base —
NOT YET POSSIBLE from this branch alone: #1242 is an OPEN PR on
`feat/pindebt-242`, not an ancestor of this branch's base, as of when this
was written. Noted here and in the PR/artifact rather than silently assumed
done.

SCOPE, DELIBERATELY NARROWER THAN "tool name matched": the pin key is
(tool name, ambient-path SHAPE), not tool name alone. `rivet` shadowed via
some path that does NOT match the pinned shape (a foreign image bake, a
homebrew keg, a different install root) is a DIFFERENT hazard wearing the
same tool name and must NOT be silently absorbed into this pin — it is
reported as its own finding, separate from "resolved" (which means the
pinned variant specifically is gone) and from "new" (which means an
entirely different TOOL is now shadowed).

CONTRACT, exact match in every direction (the #911 / ratchet discipline —
a win must be captured, not silently absorbed as slack):
  - a shadowed tool NOT in KNOWN_OPEN at all is a NEW hazard -> RED;
  - a tool KNOWN_OPEN pins, shadowed via a path that does NOT match the
    pinned shape, is a DIFFERENT hazard under the same name -> RED,
    reported distinctly (do not conflate with the pinned variant);
  - a tool KNOWN_OPEN pins that `varve verify` no longer reports shadowed
    AT ALL is an IMPROVEMENT -> RED until the entry is removed in the SAME
    PR that fixed it (silently accepting the win would hide it);
  - the pinned tool shadowed via exactly the pinned path shape, and nothing
    else drifted -> GREEN.

Usage: `varve verify` output on stdin (any exit code); this script's own
exit code is the real gate signal.
"""

from __future__ import annotations

import re
import sys

# (issue, note, ambient_path_pattern) — the note POINTS at evidence (measured
# CI runs, run ids, runner names — see #1236 / PR #1244) rather than
# repeating it, so this table cannot drift out of sync with the commentary
# that justifies it. `ambient_path_pattern` is a regex matched against the
# END of the shadowing path (re.search) — the stable part across runners is
# the SUFFIX (`.cargo/bin/<tool>`), never the `/var/lib/runners/runnerN/`
# prefix, which varies by design (whichever runner the job lands on).
KNOWN_OPEN: dict[str, tuple[str, str, str]] = {
    "rivet": (
        "#1236",
        "required `rivet` job's cargo install (no --root) shadows the pin's "
        "rivet on shared self-hosted runners; reproduced on two different "
        "runners (pulseengine-ci-01-9, pulseengine-ci-01-12) in PR #1244",
        r"\.cargo/bin/rivet$",
    ),
}

_SHADOW_LINE = re.compile(
    r"^`([A-Za-z0-9_-]+)` on your PATH is (\S+), not the pinned", re.MULTILINE
)


def shadowed_pairs_from_verify_output(text: str) -> list[tuple[str, str]]:
    """Extract (tool, ambient_path) pairs from `varve verify`'s own wording.

    Text extraction of what varve's own error already names, not a
    reimplementation of the shadow-detection logic itself — that stays
    entirely inside varve (REQ-SHADOW-001), the tool this repo is pinning.
    """
    return _SHADOW_LINE.findall(text)


def shadowed_tools_from_verify_output(text: str) -> set[str]:
    """Tool names only — kept for callers/tests that don't need the path."""
    return {tool for tool, _path in shadowed_pairs_from_verify_output(text)}


def check(text: str) -> tuple[bool, list[str]]:
    """Return (ok, messages). ok is False iff the pin table needs editing."""
    if "signature OK" not in text and "REQ-SHADOW-001" not in text:
        return False, [
            "input does not look like `varve verify` output (no 'signature "
            "OK' and no 'REQ-SHADOW-001') — cannot check shadow pins"
        ]

    pairs = shadowed_pairs_from_verify_output(text) if "REQ-SHADOW-001" in text else []
    actual_tools = {tool for tool, _path in pairs}
    pinned_tools = set(KNOWN_OPEN)

    problems: list[str] = []

    for tool, path in pairs:
        if tool not in KNOWN_OPEN:
            problems.append(
                f"NEW PATH shadow found, not in KNOWN_OPEN: `{tool}` (via "
                f"{path}). Either this is a real new hazard (investigate "
                f"before pinning it) or the runner fleet changed — do not "
                f"silently widen the pin without a reason and an issue."
            )
            continue
        issue, note, pattern = KNOWN_OPEN[tool]
        if not re.search(pattern, path):
            problems.append(
                f"`{tool}` is shadowed via {path!r}, which does NOT match the "
                f"pinned shape ({pattern!r}) for KNOWN_OPEN[{tool!r}] "
                f"({issue}: {note}). This may be a DIFFERENT hazard wearing "
                f"the same tool name — investigate before assuming it's the "
                f"known one; do not widen the pattern to paper over it."
            )

    resolved = sorted(pinned_tools - actual_tools)
    for tool in resolved:
        issue, note, _pattern = KNOWN_OPEN[tool]
        problems.append(
            f"KNOWN_OPEN pins `{tool}` ({issue}: {note}) as shadowed, but "
            f"`varve verify` no longer reports it shadowed at all. That is "
            f"an IMPROVEMENT — remove this entry from KNOWN_OPEN in the SAME "
            f"PR that fixed it; do not leave a stale pin claiming a hazard "
            f"that is gone."
        )

    if problems:
        return False, problems
    return True, [
        f"varve shadow pins: {len(pinned_tools)} known-open "
        f"({', '.join(sorted(pinned_tools))}), all present at their "
        f"pinned path shape, no new or different hazard."
    ]


def main(argv: list[str]) -> int:
    text = sys.stdin.read()
    ok, messages = check(text)
    for m in messages:
        print(f"::error::{m}" if not ok else m)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
