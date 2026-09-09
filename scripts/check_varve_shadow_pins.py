#!/usr/bin/env python3
"""RQ-66-VARVE (#1236): known-open PATH-shadow REPORT for the varve toolchain pin.

`varve verify` (REQ-SHADOW-001) is varve's own PATH-shadowing oracle — not a
hand-written parser here, the shipped tool's own check. Wired into the
`rivet-federated` CI job (#1244), it found `rivet` on the runner's PATH
resolving to an ambient `.cargo/bin/rivet` instead of the varve-pinned copy,
on THREE distinct self-hosted runners (`pulseengine-ci-01-9`,
`-01-12`, `-01-11`).

REVISION HISTORY, because the wrong model was tried first and the mistake is
worth keeping visible:

1. First cut: hard-fail the job on ANY `varve verify` failure. Immediately
   red on every run — a real hazard, but not fixable inside this change, so
   this violated the release's own "watched, fixed, or deleted" rule (a
   gate red every run trains people to ignore it).
2. Second cut: an EXACT-MATCH known-open pin, same shape as the parity
   oracle's / home-alias differential's `KNOWN_OPEN` tables — green when
   the observed shadow set equals the pinned set, red on a NEW tool AND
   (symmetrically) red when a PINNED tool stops being observed (an
   "improvement" that must be captured, the #911 / ratchet discipline).
   This is the RIGHT shape for a REPRODUCIBLE CODE DEFECT (the parity/
   home-alias tables: a given WASM shape ALWAYS produces the same wrong
   bytes, deterministically, on every run, on every machine). It is the
   WRONG shape here: a FOURTH real CI run, on a fourth distinct runner
   (`pulseengine-ci-01-6`), came back with `varve verify` completely CLEAN
   — no shadow at all. The observable is not a property of the CODE or the
   PIN; it is a property of RUNNER STATE (whether the required `rivet`
   job's `cargo install --force --git`, no `--root`, happened to run on
   THAT particular shared, persistent machine before). Treating "is rivet
   shadowed right now" as an exact-match invariant made the gate FLAKY —
   green or red depending on which machine happened to pick up the job,
   which is worse than either a clean green or an honest red: a flaky gate
   is exactly how a real regression gets waved through as "just the runner
   again" (the coordinator's diagnosis, confirmed by run 4's clean log).

3. THIS CUT: REPORT, don't gate, on the ALREADY-KNOWN, runner-state-driven
   observation. Gate ONLY on something that would be NEW information no
   matter which runner ran the job:
     - a shadowed tool NOT in KNOWN_OPEN at all (a genuinely new hazard);
     - a KNOWN_OPEN tool shadowed via a path that does NOT match its pinned
       shape (a DIFFERENT mechanism wearing the same tool name).
   Presence or absence of the ALREADY-EXPLAINED `rivet` shadow, at its
   already-pinned path shape, is neither passed over silently (it is always
   printed) nor treated as pass/fail — because a single run's presence or
   absence proves nothing about whether the underlying cause (the sibling
   job's install step) is fixed everywhere, one runner, or nowhere.

NOT registered under `known_open_pins` (RQ-66-PINDEBT, claims.yaml): that
ratchet's population is explicitly scoped to REPRODUCIBLE CODE DEFECTS
under `scripts/repro/` (its own "EXCLUDED, and why" block already carves
out EXPECTED_DECLINES/EXPECTED_SKIPS and ci.yml `# ci-checks:` floors as a
different kind of thing than a suppressed wrong-answer). This hazard is a
third kind again — non-deterministic SHARED-INFRASTRUCTURE state, not a
defect this repo's own code produces reproducibly — so it does not belong
in that population any more than a flaky network timeout would. Verified
directly rather than assumed: the population tripwire's glob
(`scripts/repro/**/*.py`) does not match this file's path at all, and
`python3 scripts/claim_check.py claims.yaml` / `--metric` are unaffected
(65/65 hold, `known_open_pins` stays 104/104) whether or not this file
exists — confirmed empirically, not inferred from reading the pattern.

Usage: `varve verify` output on stdin (any exit code); this script's own
exit code is the real gate signal (0 unless a NEW-information case fires).
"""

from __future__ import annotations

import re
import sys

# (issue, note, ambient_path_pattern) — the note POINTS at evidence (measured
# CI runs, run ids, runner names — see #1236 / PR #1244) rather than
# repeating it, so this table cannot drift out of sync with the commentary
# that justifies it. `ambient_path_pattern` is a regex matched (re.search)
# against the shadowing path — the stable part across runners is the SUFFIX
# (`.cargo/bin/<tool>`), never the `/var/lib/runners/runnerN/` prefix, which
# varies by design (whichever runner the job lands on, and whether that
# specific runner has ever run the sibling job that leaves rivet there).
KNOWN_OPEN: dict[str, tuple[str, str, str]] = {
    "rivet": (
        "#1236",
        "required `rivet` job's cargo install (no --root) shadows the pin's "
        "rivet on shared self-hosted runners WHEN a given runner has run "
        "that job before — observed present on pulseengine-ci-01-9, -01-12, "
        "-01-11 and ABSENT (clean) on -01-6 in PR #1244, confirming this is "
        "runner-state, not a stable repo property",
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
    """Return (ok, messages).

    ok is False ONLY for information a runner-state explanation cannot
    account for: a tool not in KNOWN_OPEN at all, or a KNOWN_OPEN tool
    shadowed via a path that doesn't match its pinned shape. Presence or
    absence of the already-pinned (tool, path) pair is REPORTED, never
    gated — see the module docstring for why.
    """
    if "signature OK" not in text and "REQ-SHADOW-001" not in text:
        return False, [
            "input does not look like `varve verify` output (no 'signature "
            "OK' and no 'REQ-SHADOW-001') — cannot check shadow pins"
        ]

    pairs = shadowed_pairs_from_verify_output(text) if "REQ-SHADOW-001" in text else []
    actual_tools = {tool for tool, _path in pairs}
    pinned_tools = set(KNOWN_OPEN)

    problems: list[str] = []
    info: list[str] = []

    for tool, path in pairs:
        if tool not in KNOWN_OPEN:
            problems.append(
                f"NEW PATH shadow found, not in KNOWN_OPEN: `{tool}` (via "
                f"{path}). This is not explained by the known runner-state "
                f"variance — either a real new hazard (investigate before "
                f"pinning it) or a different runner-fleet change; do not "
                f"silently widen the pin without a reason and an issue."
            )
            continue
        issue, note, pattern = KNOWN_OPEN[tool]
        if re.search(pattern, path):
            info.append(
                f"`{tool}` is shadowed via {path} — matches the KNOWN_OPEN "
                f"shape for {tool!r} ({issue}). Known runner-state variance, "
                f"not gated (see module docstring)."
            )
        else:
            problems.append(
                f"`{tool}` is shadowed via {path!r}, which does NOT match the "
                f"pinned shape ({pattern!r}) for KNOWN_OPEN[{tool!r}] "
                f"({issue}: {note}). This may be a DIFFERENT hazard wearing "
                f"the same tool name — investigate before assuming it's the "
                f"known one; do not widen the pattern to paper over it."
            )

    not_observed = sorted(pinned_tools - actual_tools)
    for tool in not_observed:
        issue, _note, _pattern = KNOWN_OPEN[tool]
        info.append(
            f"`{tool}` (KNOWN_OPEN, {issue}) is NOT shadowed on this runner "
            f"this run. Not gated: a single clean run does not prove the "
            f"hazard is fixed everywhere (it is runner-state-dependent), and "
            f"a single shadowed run does not prove it is fixed nowhere."
        )

    if problems:
        return False, problems
    if not info:
        info.append("varve verify: clean, no shadow reported.")
    return True, info


def main(argv: list[str]) -> int:
    text = sys.stdin.read()
    ok, messages = check(text)
    for m in messages:
        print(f"::error::{m}" if not ok else m)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
