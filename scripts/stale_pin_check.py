#!/usr/bin/env python3
"""RQ-73-PINDEBT (#1373) — refuse a live pin whose issue is already CLOSED.

A red-first pin says "this function returns this wrong answer today, issue #N",
exact in both directions, so CI stays green without hiding the bug and the pin
moving is the fix's own evidence. `known_open_pins` makes the pin count a
ratchet. Neither makes a pin's ISSUE mean anything: an issue can close while its
pin keeps observing the divergence on every run, and NOTHING NOTICES. A pin
whose issue is closed is debt with no owner — the board says fixed, the oracle
says otherwise, and the oracle is the one running against the live compiler.

THE SPECIMEN THIS WAS BUILT FROM (v0.73, measured 2026-09-24). #1229 — "the arm
direct selector rejects VALID spec modules" — is CLOSED, while
`false_reject_1229_differential.py` pins 130 false rejections across 12
(file, backend) cells and PASSES on main. It was closed by PR #1246, the very PR
that shipped that oracle, from a sentence describing what a HYPOTHETICAL future
fix would do; two lines below it the same PR says "filed as watched, not fixed".
The board recorded a completion nobody asserted.

WHAT THIS CHECKS. For every table in the `known_open_pins` population declared
in claims.yaml (the single authority on WHICH tables are pins), derive the
issue(s) that table's entries are charged to, then require each to be OPEN.

ISSUE ATTRIBUTION — two strengths, both DERIVED, never a hand tally:

  per-entry  the entry's value carries the issue (`('#1206', 2)`,
             `(0, '#1223')`). Position-independent: every string element of the
             value is examined, because the tables disagree about position --
             the parity table is (issue, count) and the home-alias table is
             (count, issue), a reversal claims.yaml already documents.

  per-table  the value carries NO issue, so the declaration in claims.yaml
             must supply `issue:`. Four of the seven non-empty tables are in
             this class (#1207/#1229/#1230/#1231 — the RQ-66-UNWATCHED set),
             because their values are bare ints. Attribution lives in the
             declared population rather than in a filename regex: a rule like
             `_(\\d{3,5})[_.]` over `ra003_join_1230_differential.py` is one
             character away from reading `003`, and a gate must not guess.

A table that is non-empty and yields NO issue by either route is a HARD ERROR.
Defaulting it to "unattributed" would be a gate that cannot fail on the failure
it defines. Silence is the thing being checked for; it is never the answer.

WHY THE ISSUE MATCH IS ANCHORED (`^#\\d+$`, not a search). The issue slot also
holds REASON SLUGS: the parity table's `('#539-grow-fails', 1)` sits exactly
where `('#1206', 2)` sits, and its own comment reads "Recorded with this reason,
NO ISSUE: the divergence is a capability boundary, not a miscompile". #539 IS
closed, so an unanchored `#(\\d+)` reports 14 deliberate, documented envelope
pins as stale debt. The first draft of this derivation did exactly that and was
caught by reading the entries it had just classified.

Usage:
    python3 scripts/stale_pin_check.py            # REST via GH_TOKEN/GITHUB_TOKEN,
                                                  # falling back to `gh` when neither
                                                  # is set. NOT `gh` first: it is
                                                  # absent from the self-hosted pool
                                                  # where this runs, and a missing
                                                  # binary RAISES rather than
                                                  # returning non-zero.
    python3 scripts/stale_pin_check.py --self-test        # prove both verdicts
    python3 scripts/stale_pin_check.py --states-file s.json   # offline

Exit 0 = every pinned issue is open. Exit 1 = at least one stale pin, a table
whose issue cannot be derived, or a board this gate could not read — an
unreadable board is never reported as a clean one.
"""

from __future__ import annotations

import argparse
import collections
import ast
import json
import os
import pathlib
import re
import subprocess
import urllib.request
import sys

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
REPO = "pulseengine/synth"

# Anchored at BOTH ends. See the module docstring: `#539-grow-fails` occupies
# the same tuple position as a real issue reference.
ISSUE_RE = re.compile(r"^#(\d+)$")

# Anything carrying a `#<digits>` that is NOT an exact issue reference.
_HASH_NUM = re.compile(r"#\d+")

# The ONLY strings allowed to sit in the issue slot while carrying a `#N`
# without being an issue reference. Declared, not inferred (v0.73 cold review,
# gate finding F1).
#
# The "reason" bucket used to be a silent catch-all: any value with no exact
# match was booked as reason-charged, the `attributed + reasoned == total`
# accounting still balanced, and the issue was never checked for closure. So a
# TYPO was indistinguishable from a deliberate suppression reason.
# DEMONSTRATED: `('#1206', 2)` -> `('issue #1206', 2)` silently dropped #1206
# from the checked set and the gate still printed PASS.
#
# Enumerated from the live tables rather than imagined: exactly two strings
# qualify today, and both are deliberate.
REASON_STRINGS = frozenset({
    # the parity table's capability-boundary envelope, whose own comment reads
    # "Recorded with this reason, NO ISSUE"
    "#539-grow-fails",
    # the boot sweep's GROW_ENVELOPE constant
    "memory.grow on a fixed-memory image fails (-1): spec-legal, the #539 envelope",
})


class StalePinError(Exception):
    """A shape assumption failed. Never downgraded to a warning."""


def _binding(tree: ast.Module, name: str) -> ast.expr | None:
    """The top-level value bound to `name` — `X = {}` and `X: T = {}` both."""
    for node in tree.body:
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        for t in targets:
            if isinstance(t, ast.Name) and t.id == name:
                return node.value
    return None


def entry_issues(path: pathlib.Path, name: str) -> collections.Counter:
    """issue -> how many of THIS table's entries are charged to it.

    A count, not a set: one table can serve several issues (the parity table's
    20 entries split across #1206, #1215 and the `#539-grow-fails` envelope),
    and reporting the TABLE's size against each of them overstates every one of
    them. The first draft returned a set and printed "20 pins" for both #1206
    and #1215, summing to 105 against a `known_open_pins` ratchet of 85 — a
    label that did not mean what it said, caught only because an independently
    derived 85 existed to contradict it.

    Empty for a comprehension or a table of bare values — not an error here, it
    routes the table to per-table attribution.
    """
    tree = ast.parse(path.read_text(errors="ignore"), filename=str(path))
    node = _binding(tree, name)
    if node is None:
        raise StalePinError(f"{path.name}::{name} is not bound at top level")
    # Top-level `NAME = "string"` constants, so a value that references one is
    # RESOLVED rather than skipped. The boot sweep writes `(GROW_ENVELOPE, 12)`;
    # `literal_eval` raises on the Name, and the first draft caught the raise
    # and `continue`d — silently dropping 3 of that table's 6 entries. The
    # per-table accounting invariant below is what surfaced it.
    consts: dict[str, str] = {}
    for stmt in tree.body:
        tgts = (stmt.targets if isinstance(stmt, ast.Assign)
                else [stmt.target] if isinstance(stmt, ast.AnnAssign) else [])
        for t in tgts:
            if (isinstance(t, ast.Name) and isinstance(stmt.value, ast.Constant)
                    and isinstance(stmt.value.value, str)):
                consts[t.id] = stmt.value.value

    def elements(v: ast.expr) -> list:
        """The value's elements, resolving top-level string constants."""
        items = v.elts if isinstance(v, ast.Tuple) else [v]
        out = []
        for e in items:
            if isinstance(e, ast.Name):
                if e.id not in consts:
                    raise StalePinError(
                        f"{path.name}::{name} line {e.lineno}: value references "
                        f"`{e.id}`, which is not a top-level string constant — "
                        f"this derivation will not guess what a pin is charged to"
                    )
                out.append(consts[e.id])
            else:
                try:
                    out.append(ast.literal_eval(e))
                except (ValueError, SyntaxError):
                    out.append(None)
        return out

    found: collections.Counter = collections.Counter()
    found.reasoned = 0  # entries carrying no issue (a documented reason slug)
    if not isinstance(node, ast.Dict):
        return found
    for value in node.values:
        parts = elements(value)
        hit = False
        for part in parts:
            if isinstance(part, str):
                t = part.strip()
                m = ISSUE_RE.match(t)
                if m:
                    found[int(m.group(1))] += 1
                    hit = True
                elif _HASH_NUM.search(t) and t not in REASON_STRINGS:
                    # AMBIGUOUS: carries a `#N` but is not an issue reference
                    # and is not a declared reason. Silently booking this as
                    # "reason-charged" is how a typo'd issue reference stops
                    # being checked while every count still balances.
                    raise StalePinError(
                        f"{path.name}::{name}: value {part!r} carries a `#N` "
                        f"but is neither an exact issue reference nor one of "
                        f"the declared REASON_STRINGS. If it is a suppression "
                        f"reason, declare it; if it is meant to name an issue, "
                        f"write it as `#1234` exactly. Left alone it would be "
                        f"counted as a reason and the issue never checked."
                    )
        if not hit:
            found.reasoned += 1
    return found


def attribute(root: pathlib.Path) -> dict[int, list[tuple[str, int]]]:
    """issue -> [(oracle file, entries in that table), ...]"""
    sys.path.insert(0, str(root / "scripts"))
    import claim_check  # noqa: PLC0415  (kept local: it is the authority, not a dep)

    claims = yaml.safe_load((root / "claims.yaml").read_text())
    tables = claims["status_fields"]["known_open_pins"]["tables"]

    charged: dict[int, list[tuple[str, int]]] = {}
    reasoned = 0  # pins charged to a documented reason, not an issue
    declared_total = claim_check._pin_table(tables, "entries", root)

    for t in tables:
        rel, name = t["file"], t["name"]
        n = claim_check._pin_table([t], "entries", root)
        if n == 0:
            continue  # an empty suppression list is the goal state

        issues = entry_issues(root / rel, name)
        if not issues:
            declared = t.get("issue")
            if declared is None:
                raise StalePinError(
                    f"{rel}::{name} has {n} live pin(s) but carries no issue in "
                    f"its entry values and declares no `issue:` in claims.yaml. "
                    f"A pin charged to nobody cannot be checked for staleness — "
                    f"add the issue to the entry values, or declare `issue:` on "
                    f"this table in claims.yaml."
                )
            # Whole table to one issue: the entries are bare, so there is no
            # finer split to derive. Today every table on this path holds bare
            # ints, so "reason-charged" was never a real classification for
            # them and folding it in is exact. A future dict-literal table that
            # mixed genuine reason slugs with NO issue anywhere would be
            # over-attributed here — the printed COUNT would overstate, though
            # the verdict could not change, since the verdict reads issue STATE
            # and this path can only add issues to check, never drop one.
            issues = collections.Counter({int(declared): n})
            issues.reasoned = 0

        # EVERY entry is accounted for, or the parse drifted. An entry this
        # derivation silently skipped is a pin whose issue is never checked —
        # invisible, which is the exact condition being tested for.
        attributed_entries = sum(issues.values())
        if attributed_entries + issues.reasoned != n:
            raise StalePinError(
                f"{rel}::{name}: accounted for {attributed_entries} issue-charged "
                f"+ {issues.reasoned} reason-charged entries, but the table has "
                f"{n}. Some entry was neither — this derivation's shape "
                f"assumptions no longer match the table."
            )
        reasoned += issues.reasoned

        for i, cnt in issues.items():
            charged.setdefault(i, []).append((rel, cnt))

    if not charged:
        raise StalePinError(
            "derived 0 pinned issues from a non-empty population — this gate "
            "would pass no matter what; refusing to report success"
        )
    attributed = sum(sum(c for _, c in v) for v in charged.values())
    if attributed + reasoned != declared_total:
        raise StalePinError(
            f"{attributed} issue-charged + {reasoned} reason-charged != "
            f"{declared_total} declared pins — this gate did not see every pin"
        )
    return charged, reasoned, declared_total


def _rest(n: int, token: str) -> dict:
    """One issue via the REST API. No `gh` binary — it is ABSENT on the
    self-hosted pool (RQ-72-CIPOOL measured it), where this gate runs."""
    req = urllib.request.Request(
        f"https://api.github.com/repos/{REPO}/issues/{n}",
        headers={"Authorization": f"Bearer {token}",
                 "Accept": "application/vnd.github+json",
                 "User-Agent": "synth-stale-pin-check"},
    )
    with urllib.request.urlopen(req, timeout=30) as r:  # noqa: S310
        d = json.loads(r.read())
    return {
        "number": d["number"],
        # REST spells it lowercase; the rest of this file compares against the
        # CLI's uppercase. Normalise HERE, once, rather than at each comparison.
        "state": d["state"].upper(),
        "closedAt": d.get("closed_at"),
        "stateReason": (d.get("state_reason") or "").upper() or None,
        "title": d.get("title", ""),
    }


def _gh(n: int) -> dict:
    """Fallback for a local run with no token. `gh` missing RAISES OSError
    rather than returning non-zero — caught by the caller, never swallowed."""
    r = subprocess.run(
        ["gh", "issue", "view", str(n), "--repo", REPO,
         "--json", "number,state,closedAt,stateReason,title"],
        capture_output=True, text=True, timeout=30,
    )
    if r.returncode != 0:
        raise StalePinError(f"gh could not read #{n}: {r.stderr.strip()}")
    return json.loads(r.stdout)


def issue_states(issues: list[int], states_file: str | None) -> dict[int, dict]:
    if states_file:
        raw = json.loads(pathlib.Path(states_file).read_text())
        return {int(k): v for k, v in raw.items()}

    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    out: dict[int, dict] = {}
    for n in issues:
        try:
            out[n] = _rest(n, token) if token else _gh(n)
        except StalePinError:
            raise
        except Exception as e:  # noqa: BLE001
            # An unreadable board is NOT an open board. A gate whose whole job
            # is to report a stale pin must never pass because the lookup died.
            raise StalePinError(
                f"could not read issue #{n}: {type(e).__name__}: {e}. Refusing "
                f"to report PASS on a board this gate could not read."
            ) from e
    return out


def verdict(charged, states, reasoned, declared_total, quiet: bool = False) -> int:
    """The ONE decision path. The self-test drives this, not a copy of it."""
    def say(*a):
        if not quiet:
            print(*a)

    stale = []
    say(f"{'issue':<8}{'state':<9}{'pins':>5}  oracle(s)")
    for issue in sorted(charged):
        st = states[issue]
        tables = charged[issue]
        pins = sum(n for _, n in tables)
        names = ", ".join(pathlib.Path(f).name for f, _ in tables)
        say(f"#{issue:<7}{st['state']:<9}{pins:>5}  {names}")
        if st["state"] != "OPEN":
            stale.append((issue, st, pins, names))

    attributed = sum(sum(n for _, n in v) for v in charged.values())
    say(
        f"\nstale-pin check: {len(charged)} issue(s) carrying {attributed} pin(s); "
        f"{reasoned} further pin(s) charged to a documented reason, not an issue "
        f"(total {declared_total} = known_open_pins)"
    )

    if not stale:
        say("RESULT: PASS — every issue carrying a live pin is OPEN")
        return 0

    say("")
    for issue, st, pins, names in stale:
        say(
            f"REFUSE: #{issue} is {st['state']}"
            f" (closedAt={st.get('closedAt')}, stateReason={st.get('stateReason')})"
            f" while {pins} pin(s) in {names} still observe its divergence."
        )
        say(f"    {st.get('title', '')}")
    say(
        "\nRESULT: FAIL — a closed issue's pin is debt with no owner. Either the "
        "divergence is fixed (move the pin, in the same PR) or the issue is not "
        "fixed (reopen it). A green board over a red oracle is the thing this "
        "gate exists to refuse."
    )
    return 1


def self_test() -> int:
    """Potency: this gate must still be ABLE to fail once the board is correct.

    #1229 was its red half and is now reopened, so on the live board the check
    passes — and a check that passes today and cannot be shown to fail is
    indistinguishable from one that never looks. Both verdicts are exercised
    against the REAL attribution (the same tables, the same derivation), with
    only the ISSUE STATES substituted, because the states are the one input a
    test can legitimately fabricate.
    """
    charged, reasoned, total = attribute(ROOT)
    issues = sorted(charged)
    ok = 0

    all_open = {i: {"number": i, "state": "OPEN", "title": "t"} for i in issues}
    victim = next(i for i in issues if charged[i])
    one_closed = dict(all_open)
    one_closed[victim] = {"number": victim, "state": "CLOSED",
                          "closedAt": "2026-01-01T00:00:00Z",
                          "stateReason": "COMPLETED", "title": "t"}

    for label, states, want in (
        ("every pinned issue OPEN -> pass", all_open, 0),
        (f"#{victim} CLOSED with live pins -> refuse", one_closed, 1),
    ):
        got = verdict(charged, states, reasoned, total, quiet=True)
        status = "ok" if got == want else "FAIL"
        print(f"  {status}  {label} (rc={got}, want {want})")
        ok += got == want

    # The population itself must be non-trivial, or both legs are vacuous.
    if len(issues) < 2:
        print(f"  FAIL  population is {len(issues)} issue(s) — both legs vacuous")
        return 1
    print(f"  ok  population: {len(issues)} issues, {total} pins")
    return 0 if ok == 2 else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--states-file", help="JSON {issue: {state,...}} for offline runs")
    ap.add_argument("--self-test", action="store_true", help="prove both verdicts")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    try:
        charged, reasoned, declared_total = attribute(ROOT)
        states = issue_states(sorted(charged), args.states_file)
    except StalePinError as e:
        print(f"REFUSE: {e}")
        return 1

    return verdict(charged, states, reasoned, declared_total)


if __name__ == "__main__":
    sys.exit(main())
