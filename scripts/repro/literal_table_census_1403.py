#!/usr/bin/env python3
# ci-status: manual (measurement) — a CENSUS with no verdict about the compiler.
# RQ-77-CENSUS (#1403): the literal-table population was PROSE, and v0.76 marked
# its figures UNVERIFIED after an independent reconstruction of the stated
# predicate disagreed. This derives the population from the tree instead. It has
# no expected values and nothing for CI to fail on; the numbers are judged by a
# reader. The shapes it counts are gated only where `claims.yaml` NAMES them:
# `claim_check`'s `pin-table` kind reads the ten suppression tables the ledger
# lists, and a change to one of those moves `known_open_pins`. A suppression
# table in a file the ledger does NOT list is caught by nothing, which CLAUDE.md
# records as a review-time obligation. (An earlier version of this header
# credited `ci_pool_tripwire` with walking the KNOWN*/PINNED* tables; it does
# not — it checks `ci.yml` job pools, and grepping it for KNOWN|PINNED returns a
# single unrelated comment. The corrected wording reached `claims.yaml` in the
# same lane and not this file, so the artifact claimed a fix it had not applied;
# round 1 of v0.77's cold review caught that.) Wiring it would mean inventing an assertion the artifact was
# scoped not to make — the same call recorded for partial_census_1017.py.
"""RQ-77-CENSUS (#1403) — derive the module-level literal-table population.

WHY THIS EXISTS. v0.76's RQ-76-GHSHAPE asserted "353 module-level literal tables
across 173 files" from a predicate described only in prose. A cold reviewer
implemented that stated predicate at the same commit and got **362 across 190**,
and looser readings gave 493 and 649. The figures were marked UNVERIFIED. The
defect is not the arithmetic: it is that *a hand-asserted count of hand-written
tables is itself a hand-written table*, and the prose did not pin the predicate.

WHAT THIS DOES DIFFERENTLY, and it is the whole point: it does NOT report one
number. The prose left three genuine ambiguities, and each changes the answer:

  * MODULE-LEVEL — does a table inside a `class` body count? Inside
    `if TYPE_CHECKING:` or `try:`? "Module-level" reads as "not in a function",
    but an `ast.walk` finds nested ones too.
  * OF CONSTANTS — is `{"a": 1}` a literal table and `{"a": (1, 2)}` not? Does a
    container of containers of constants qualify?
  * A TABLE — is a bare `list` of strings a table, or only a `dict`?

So the census reports the count under each reading, and the SPREAD is the
finding. A single number here would recreate exactly the defect #1403 is about,
one level up: a figure whose subject is whichever reconstruction the reader
happens to make.

The readings are named, not ranked. Anyone citing a figure from this census must
cite WHICH reading, and the artifact does.

Run:  python3 scripts/repro/literal_table_census_1403.py
      python3 scripts/repro/literal_table_census_1403.py --show strict-dict
"""
import argparse
import ast
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GLOB = "scripts/**/*.py"

CONTAINER = (ast.Dict, ast.List, ast.Tuple, ast.Set)


def targets_of(node):
    if isinstance(node, ast.Assign):
        return node.targets
    if isinstance(node, ast.AnnAssign):
        return [node.target]
    return []


def all_constants(v, depth=0, max_depth=0):
    """Every element is a Constant. `max_depth` allows nested containers."""
    if not isinstance(v, CONTAINER):
        return False
    if isinstance(v, ast.Dict):
        # A `**spread` gives a None key; it is not a constant element.
        items = [x for x in (list(v.keys) + list(v.values)) if x is not None]
    else:
        items = list(v.elts)      # List / Tuple / Set all use `.elts`
    if not items:
        return False                      # an empty literal is not a table
    for it in items:
        if isinstance(it, ast.Constant):
            continue
        if isinstance(it, CONTAINER) and depth < max_depth:
            if all_constants(it, depth + 1, max_depth):
                continue
            return False
        return False
    return True


def top_level_stmts(tree):
    """Statements at the MODULE body only — no class bodies, no if/try nesting."""
    return list(tree.body)


def guarded_stmts(tree):
    """Module body PLUS one level of `if`/`try` at module scope.

    `if TYPE_CHECKING:` and `try: ... except ImportError:` are module-level in
    every sense a reader means, but they are not in `tree.body` directly.
    """
    out = list(tree.body)
    for node in tree.body:
        if isinstance(node, (ast.If, ast.Try)):
            for blk in ("body", "orelse", "finalbody"):
                out.extend(getattr(node, blk, []) or [])
            for h in getattr(node, "handlers", []) or []:
                out.extend(h.body)
    return out


READINGS = {
    # name: (statement selector, dict-only?, nesting depth allowed)
    "strict-dict":   (top_level_stmts, True, 0),
    "strict-any":    (top_level_stmts, False, 0),
    "guarded-any":   (guarded_stmts, False, 0),
    "nested-any":    (guarded_stmts, False, 2),
    "anywhere-any":  (None, False, 2),        # ast.walk — includes class bodies
}


def census(reading: str):
    sel, dict_only, depth = READINGS[reading]
    files = sorted(ROOT.glob(GLOB))
    hits = []
    parsed = 0
    for p in files:
        try:
            tree = ast.parse(p.read_text())
        except SyntaxError:
            continue
        parsed += 1
        stmts = ast.walk(tree) if sel is None else sel(tree)
        for node in stmts:
            if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                continue
            v = node.value
            if v is None:
                continue
            if dict_only and not isinstance(v, ast.Dict):
                continue
            if not all_constants(v, 0, depth):
                continue
            for t in targets_of(node):
                if isinstance(t, ast.Name):
                    hits.append((str(p.relative_to(ROOT)), t.id, node.lineno))
    return parsed, hits


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--show", metavar="READING",
                    help="list every hit under one reading")
    args = ap.parse_args()

    files = sorted(ROOT.glob(GLOB))
    # NON-VACUITY (RQ-77-SUBJECT, #1418): a census that enumerated no files would
    # report "0 tables" and be a true statement about the empty set.
    if not files:
        sys.exit(f"REFUSE: {GLOB} matched no files under {ROOT} — every count "
                 f"below would be about the empty set")
    print(f"files matched by {GLOB!r}: {len(files)}")

    rows = {}
    for name in READINGS:
        parsed, hits = census(name)
        rows[name] = (parsed, hits)
    if all(len(h) == 0 for _p, h in rows.values()):
        sys.exit("REFUSE: every reading found ZERO tables across a non-empty file "
                 "set — the predicate is broken, not the tree")

    print(f"python files parsed             : {rows['strict-dict'][0]}")
    print("\nthe population under each READING — the SPREAD is the finding, and a")
    print("citation must name which reading it used:")
    for name in READINGS:
        _parsed, hits = rows[name]
        nfiles = len({h[0] for h in hits})
        print(f"  {name:14} {len(hits):5} tables across {nfiles:4} files")

    lo = min(len(h) for _p, h in rows.values())
    hi = max(len(h) for _p, h in rows.values())
    print(f"\nRQ-77-CENSUS spread: {lo} .. {hi} tables — a factor of "
          f"{hi / max(lo, 1):.1f}. That is why\n#1403's prose figure could not be "
          f"reproduced: the predicate, not the tree, was\nthe ambiguous part. No "
          f"single number here is 'the' population.")

    if args.show:
        if args.show not in READINGS:
            sys.exit(f"REFUSE: unknown reading {args.show!r}; "
                     f"choose one of {sorted(READINGS)}")
        print(f"\nevery hit under {args.show!r}:")
        for path, name, line in sorted(rows[args.show][1]):
            print(f"  {path}:{line}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
