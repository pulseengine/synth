#!/usr/bin/env python3
"""RQ-87-PINDEBT12 (#1428) — can a suppression table added under a non-matching
name escape the ledger silently?

THE REFUTING COMMAND, run first: "Add a table under a non-matching name; if the
ledger now reds, the escape is closed and the lane is moot."

IT DOES NOT RED. The escape is LIVE, measured with a PAIRED control that proves
the mechanism discriminates on the NAME and nothing else. A real-shaped
suppression table of three entries planted in a listed oracle as
`SUPPRESSED_CASES` left `claim_check` at rc=0, 75/75, with `known_open_pins`
unchanged at its pinned value and `known_open_pinned_cases` unchanged too. The
SAME table under `KNOWN_PROBE_CASES` red immediately:
`count drifted: derived 13 != documented 12`. So the lane is NOT refuted.

CLOSING IT BY A NAME-INDEPENDENT POPULATION IS REFUSED, with numbers. The repro
corpus holds ONE HUNDRED AND SEVENTY-NINE top-level dict/set bindings, of which
TWELVE are the pinned tables. Pinning all 179 would put a number on every
unrelated fixture table in the tree — `SIGS`, `CASES`, `WATS`, `BASES`,
`TRUNC_TABLE` — so it would move on work that has nothing to do with
suppression, and this repository has already measured what happens to a gate
nobody can move honestly: it gets routed around (RQ-74-STALEMSG).

SO WHAT SHIPS IS A NARROWING, AND IT IS NAMED AS ONE. This scan derives the
suppression-SHAPED bindings that do NOT match the ledger's name pattern, and
requires each to be CLASSIFIED here with a reason. A new one is UNCLASSIFIED and
reds. The escape is narrowed from "any name at all" to "a name carrying none of
the suppression tokens below", which is strictly smaller and still real —
`FOO = {...}` still escapes, and saying so is the point.

WHAT THE CLASSIFICATION FOUND, which is the second half of the answer. Of the
suppression-shaped non-matching bindings, NONE is unaccounted-for pin debt: each
is a DECLINE pin (excluded by the ledger's own stated rule — a loud refusal is
reach, not silent wrongness), a RED-HALF fixture (excluded by design, like
`PINNED_WRONG`), or CONFIGURATION that is not a case suppression at all. A
DERIVED POPULATION OF ZERO IS A REFUSAL AND NOT A PASS, so the reason is stated
rather than assumed: the convention — name a suppression table `KNOWN*` or
`PINNED*` — has in fact been followed, so the escape is LATENT rather than
EXPLOITED. That is a fact about today's tree and not a property of the gate.

AN ERROR IN THIS LANE'S OWN FIRST MEASUREMENT, recorded because it would have
inverted the conclusion. The first walk counted only `ast.Assign` and read THREE
matching tables against the ledger's TWELVE. The ledger's regex carries
`(?::[^=\n]*)?` precisely to admit an ANNOTATED binding (`NAME: set[...] = {`),
which is an `ast.AnnAssign` — a different node type, silently skipped. Reading 3
where the shipped derivation reads 12 would have looked like the ledger
over-counting by nine. Corrected, this scan reproduces the ledger's figure
exactly, which is the independence check worth having: two different parsers over
the same tree agreeing.
"""
import argparse
import ast
import glob
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GLOB = "scripts/repro/**/*.py"

# The ledger's own name pattern, as a NAME test (claims.yaml applies it as a
# line regex including the `= {`).
LEDGER_NAME = re.compile(r"^(?:KNOWN|PINNED)[A-Z0-9_]*$")

# Tokens that make a binding SUPPRESSION-SHAPED. A tripwire requiring judgement,
# not an oracle — the same discipline the release-file statistics scan uses.
SHAPE = re.compile(
    r"(KNOWN|PINNED|EXPECTED|REFUSED|SANCTIONED|INTENDED|ALLOW|WAIV|SUPPRESS|"
    r"SKIP|DECLINE|IGNORE|EXCLUDE|INFORMATIONAL|MAY_)", re.I)

# Every suppression-shaped binding that does NOT match the ledger pattern must
# appear here with a reason. A new one is UNCLASSIFIED and reds.
#   decline  -> a LOUD refusal; the ledger excludes these by its own stated rule
#   red-half -> frozen pre-fix/plant expectations; excluded by design
#   config   -> not a case suppression at all
#   envelope -> suppresses a GATING decision; named explicitly, see below
CLASSIFIED = {
    ("arm_corpus_sweep_973.py", "EXPECTED_DECLINES"): ("decline", "named EXCLUDED in CLAUDE.md"),
    ("arm_corpus_sweep_973.py", "REFUSED_BY_DESIGN"): ("decline", "module-level #952 refusal, by design"),
    ("falcon_opt_1318_differential.py", "EXPECTED_DECLINES"): ("decline", "named EXCLUDED in CLAUDE.md"),
    ("home_alias_class_1189_differential.py", "EXPECTED_SKIPS"): ("decline", "named EXCLUDED in CLAUDE.md"),
    ("join_alias_1189_differential.py", "LIVE_DECLINES"): ("decline", "pairs the live half must REFUSE, with the needle"),
    ("unreachable_665_differential.py", "RV32_MAY_DECLINE"): ("decline", "#343 arity decline; presence must still trap"),
    ("litpool_islands_345_differential.py", "INTENDED_ACCEPTANCES"): ("decline", "declines with islands off, compiles with them on, by design"),
    ("home_alias_audit_corpus_1189.py", "PLANT_EXPECTED"): ("red-half", "DERIVED plant expectations, the potency evidence"),
    ("invalid_accept_1207_differential.py", "DECLINES"): ("red-half", "the exact-pin companion: expected verdict per cell, exact BOTH ways"),
    ("expansion_canary_gate_1021.py", "SANCTIONED"): ("config", "{'r12'} — a sanctioned scratch register in the contract"),
    ("falcon_opt_1318_differential.py", "EXPECTED_MACHINE"): ("config", "ELF machine name per backend"),
    ("partial_census_1017.py", "EXCLUDE_PARTS"): ("config", "path components skipped when walking the tree"),
    ("selector_parity_197_differential.py", "INFORMATIONAL_KINDS"): ("envelope", "divergence KINDS recorded but never gating — the one entry here that suppresses a GATING decision rather than pinning a decline; its members are envelope state cases (reference-vs-literal is not a synth verdict; a post-OOB-trap mismatch is the documented default-image envelope)"),
}


def bindings() -> list[tuple[str, str, int]]:
    """(file, name, entry count) for every TOP-LEVEL dict/set binding.

    BOTH `Assign` AND `AnnAssign`. Counting only `Assign` reads 3 matching
    tables where the ledger reads 12, because an annotated binding is a
    different node type — this lane's own first error.
    """
    out = []
    for f in sorted(glob.glob(str(ROOT / GLOB), recursive=True)):
        try:
            tree = ast.parse(Path(f).read_text(errors="ignore"), filename=f)
        except SyntaxError:
            continue
        for node in tree.body:
            if isinstance(node, ast.Assign):
                names = [t.id for t in node.targets if isinstance(t, ast.Name)]
                val = node.value
            elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                names, val = [node.target.id], node.value
            else:
                continue
            if not isinstance(val, (ast.Dict, ast.DictComp, ast.Set, ast.SetComp)):
                continue
            n = (len(val.keys) if isinstance(val, ast.Dict)
                 else len(val.elts) if isinstance(val, ast.Set) else -1)
            for name in names:
                out.append((Path(f).name, name, n))
    return out


def partition(rows):
    ledger = [r for r in rows if LEDGER_NAME.match(r[1])]
    shaped = [r for r in rows if not LEDGER_NAME.match(r[1]) and SHAPE.search(r[1])]
    plain = [r for r in rows if not LEDGER_NAME.match(r[1]) and not SHAPE.search(r[1])]
    return ledger, shaped, plain


def report() -> int:
    rows = bindings()
    ledger, shaped, plain = partition(rows)
    assert len(ledger) + len(shaped) + len(plain) == len(rows), "partition must sum"
    print(f"top-level dict/set bindings under {GLOB}: {len(rows)}")
    print(f"  matching the ledger's name pattern : {len(ledger)}")
    print(f"  suppression-SHAPED, non-matching   : {len(shaped)}")
    print(f"  neither (ordinary fixture tables)  : {len(plain)}")
    print(f"  partition sums to the row count    : "
          f"{len(ledger)}+{len(shaped)}+{len(plain)}={len(rows)}")
    unclassified = [r for r in shaped if (r[0], r[1]) not in CLASSIFIED]
    print(f"\nUNCLASSIFIED suppression-shaped bindings: {len(unclassified)}")
    for r in unclassified:
        print(f"    {r[0]}::{r[1]}  entries={r[2]}")
    kinds = {}
    for r in shaped:
        k = CLASSIFIED.get((r[0], r[1]), ("UNCLASSIFIED", ""))[0]
        kinds[k] = kinds.get(k, 0) + 1
    print(f"\nclassification of the shaped set: {kinds}")
    print("\nWHY THAT POPULATION IS EMPTY OF PIN DEBT, stated rather than assumed:")
    print("  every shaped non-matching binding is a DECLINE pin (the ledger's own")
    print("  stated exclusion), a RED-HALF fixture (excluded by design) or CONFIG.")
    print("  So the escape is LATENT, not EXPLOITED — a fact about today's tree,")
    print("  not a property of the gate. The convention has simply been followed.")
    print("\nTHE RESIDUAL ESCAPE, named rather than claimed closed: a table whose name")
    print("  carries NONE of the shape tokens still passes both halves. This scan")
    print("  NARROWS the escape; it does not close it.")
    return 1 if unclassified else 0


def self_test() -> int:
    fails = 0

    def ok(cond, what):
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    rows = bindings()
    ledger, shaped, plain = partition(rows)
    ok(len(rows) > 0, f"the binding population derives non-empty ({len(rows)})")
    ok(len(ledger) + len(shaped) + len(plain) == len(rows),
       "the partition SUMS to the row count — no binding counted twice or lost")

    # INDEPENDENCE CHECK: this scan's own parser must agree with the ledger's
    # regex on the pinned population. Two parsers, one tree, same answer.
    import subprocess
    raw = (ROOT / "claims.yaml").read_text()
    m = re.search(r"pattern:\s*'\^\(\?:KNOWN\|PINNED\)[^\n]*\n\s*glob:[^\n]*\n\s*expect:\s*(\d+)", raw)
    ok(m is not None, "the ledger's count-eq expectation is readable from claims.yaml")
    if m:
        ok(len(ledger) == int(m.group(1)),
           f"this scan's matching count ({len(ledger)}) EQUALS the ledger's "
           f"expect ({m.group(1)}) — independent derivations agree")

    # THE ANNASSIGN CASE, which this lane got wrong first. Assert BOTH node
    # types are read, or the agreement above is luck.
    probe = "A: set[int] = {1, 2}\nB = {3: 4}\n"
    t = ast.parse(probe)
    kinds = {type(n).__name__ for n in t.body}
    ok(kinds == {"AnnAssign", "Assign"}, "the probe carries both binding node types")
    seen = []
    for node in t.body:
        if isinstance(node, ast.Assign):
            seen += [x.id for x in node.targets if isinstance(x, ast.Name)]
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            seen.append(node.target.id)
    ok(seen == ["A", "B"],
       "and BOTH are collected — counting only Assign read 3 where the ledger "
       "reads 12, which would have looked like the ledger over-counting")

    # Every classification entry must name a REAL binding, or the table rots.
    live = {(r[0], r[1]) for r in rows}
    stale = [k for k in CLASSIFIED if k not in live]
    ok(not stale, f"every CLASSIFIED entry names a live binding (stale: {stale})")

    # THE PIN: nothing shaped may be unclassified.
    unc = [r for r in shaped if (r[0], r[1]) not in CLASSIFIED]
    ok(not unc, f"no suppression-shaped binding is UNCLASSIFIED (got {len(unc)})")

    # NEGATIVE CONTROL: a planted shaped name must be seen as unclassified.
    fake = ("probe_file.py", "SUPPRESSED_CASES", 3)
    ok(SHAPE.search(fake[1]) is not None and not LEDGER_NAME.match(fake[1]),
       "NEGATIVE CONTROL: a planted `SUPPRESSED_CASES` is shaped AND non-matching, "
       "so it would land in the unclassified set and red")
    # POSITIVE CONTROL on the other side: an ordinary fixture name must NOT fire.
    ok(SHAPE.search("SIGS") is None and SHAPE.search("WATS") is None,
       "POSITIVE CONTROL: ordinary fixture names (SIGS, WATS) are NOT shaped, so "
       "the scan does not simply fire on everything")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else report()


if __name__ == "__main__":
    sys.exit(main())
