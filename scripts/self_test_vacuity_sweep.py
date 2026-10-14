#!/usr/bin/env python3
"""RQ-86-SELFTEST2 (#1515) — leave-one-out vacuity sweep over the tree's self-tests.

For each self-test-bearing script, neutralise ONE of its own top-level functions
at a time (body -> `return None`) and re-run `--self-test`. A self-test that
stays GREEN with one of its subjects removed does not cover that subject: that
is the vacuity signal, and it is the only one of the three verdicts that is a
finding. `red-crash` means the self-test noticed, badly; `red-detected` means it
noticed and said so.

WHY THIS FILE EXISTS AT ALL, which is the lane's own correction. Round one found
that every figure RQ-86-SELFTEST2 reported came from this script while this
script was in no commit — so a release themed "the instrument is part of the
evidence" shipped its vacuity figures with the instrument left out. It is
committed here unchanged in behaviour, so the recorded figures re-derive.

ITS OWN KNOWN DEFECT, printed rather than hidden. `FILES` is HAND-WRITTEN, and
a hand-written population is the mirror class this repository's North Star names
first. It is kept as-is because the shipped figures were measured over it and
changing it would invalidate them in the same breath as the correction; instead
the sweep DERIVES the self-test-bearing population and prints the drift, so the
omission is visible in its own output.

DO NOT QUOTE THE DRIFT HERE -- READ `report()`'s OWN TWO LINES. An earlier version
of this docstring said "the drift is two files each way", which the function below
contradicts in the same file and the same commit: it prints ONE swept-but-not-
defining and FIVE defining-but-not-swept. "Two each way" was the drift against a
NON-RECURSIVE population (`scripts/*.py`); `derived_population()` is RECURSIVE
(`scripts/**/*.py`), so the docstring described a set the script does not compute.
Among the unswept are the THREE self-test-bearing scripts this release added --
three, not two, the third being this file.

NOT a CI gate. It mutates files in the working tree and restores them, so it is
run deliberately, in a disposable checkout, and never against uncommitted work.
"""
import argparse
import ast
import glob
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Hand-written; see the module docstring. Order is the order measured.
FILES = [
    "scripts/ci_citation_floor.py", "scripts/extract_r1_numbers.py",
    "scripts/merge_gate.py", "scripts/release_trigger_check.py",
    "scripts/shipped_feature_census.py", "scripts/stale_pin_check.py",
    "scripts/test_merge_gate_callsite.py", "scripts/verdict_prose_check.py",
    "scripts/repro/jessdiverge3_gravity_faithful_1436.py",
]


def derived_population() -> list[str]:
    """Every script that DEFINES a runnable self-test, derived from the tree."""
    out = []
    for f in sorted(glob.glob(str(ROOT / "scripts" / "**" / "*.py"), recursive=True)):
        try:
            src = Path(f).read_text()
        except OSError:
            continue
        if any(l.startswith("def self_test") for l in src.split("\n")):
            out.append(str(Path(f).relative_to(ROOT)))
    return out


def run_self_test(path: Path) -> tuple[int, str]:
    r = subprocess.run([sys.executable, str(path), "--self-test"],
                       capture_output=True, text=True, timeout=300, cwd=ROOT)
    return r.returncode, (r.stdout + r.stderr)


def neutralise(src: str, fn: ast.FunctionDef) -> str:
    """Replace fn's body with `return None`, preserving the signature line."""
    lines = src.split("\n")
    start = fn.body[0].lineno - 1
    end = fn.end_lineno
    indent = " " * (len(lines[start]) - len(lines[start].lstrip()))
    return "\n".join(lines[:start] + [indent + "return None"] + lines[end:])


def sweep() -> list[tuple[str, str, str, str]]:
    rows = []
    for rel in FILES:
        p = ROOT / rel
        orig = p.read_text()
        tree = ast.parse(orig)
        fns = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
        try:
            for fn in fns:
                if "self_test" in fn.name:
                    continue              # the harness itself, not a subject
                try:
                    mutated = neutralise(orig, fn)
                    compile(mutated, rel, "exec")
                except Exception as e:
                    rows.append((rel, fn.name, "SKIP", f"{type(e).__name__}: {e}"[:70]))
                    continue
                p.write_text(mutated)
                rc, out = run_self_test(p)
                if rc == 0:
                    verdict = "GREEN-undetected"
                elif "Traceback" in out:
                    verdict = "red-crash"
                else:
                    verdict = "red-detected"
                rows.append((rel, fn.name, verdict, out.strip().split("\n")[-1][:70]))
        finally:
            p.write_text(orig)            # restore even on an exception
    return rows


def report() -> int:
    hand, derived = set(FILES), set(derived_population())
    print(f"POPULATION: {len(FILES)} file(s) swept (hand-written); "
          f"{len(derived)} define a self-test (derived)")
    print(f"  swept but NOT self-test-defining: {sorted(hand - derived) or 'none'}")
    print(f"  self-test-defining but NOT SWEPT: {sorted(derived - hand) or 'none'}")
    print("  (the second line is this instrument's own known defect; see the docstring)\n")

    rows = sweep()
    print(f"{'file':52s} {'function':34s} {'verdict':18s} tail")
    for rel, name, v, tail in rows:
        print(f"{rel:52s} {name:34s} {v:18s} {tail}")
    c = Counter(v for _, _, v, _ in rows)
    print(f"\nSUMMARY: {dict(c)} subjects={len(rows)}")
    print("\nUNDETECTED (the self-test stayed GREEN with this subject removed):")
    for rel, name, v, _ in rows:
        if v == "GREEN-undetected":
            print(f"  {rel}  ::  {name}")
    return 0


def self_test() -> int:
    """The sweep's own cases. It MUTATES the tree, so these touch no file."""
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    src = "def keep(x):\n    return x + 1\n\n\ndef drop(y):\n    z = y * 2\n    return z\n"
    t = ast.parse(src)
    fns = {n.name: n for n in t.body if isinstance(n, ast.FunctionDef)}
    out = neutralise(src, fns["drop"])
    ok("return None" in out, "neutralise replaces the target body")
    ok("y * 2" not in out, "and the original body is gone")
    ok("x + 1" in out, "while the OTHER function is untouched")
    compile(out, "<probe>", "exec")
    ok(True, "and the result still compiles")

    pop = derived_population()
    ok(len(pop) > 0, "the derived self-test population is non-empty")
    ok(all((ROOT / f).exists() for f in FILES), "every hand-listed file exists")
    # BOTH halves are asserted. Round two fired the mutant that put this file
    # INTO `FILES` and the case stayed GREEN -- it tested membership of the
    # DERIVED population and never tested absence from the HAND LIST, so it was
    # green under exactly the state its own message forbids. The half carrying
    # the finding was the unasserted one.
    me = str(Path(__file__).resolve().relative_to(ROOT))
    ok(me in pop, "THIS file is in the derived population")
    ok(me not in FILES,
       "and NOT in the hand list — so the drift the report prints is real, not a "
       "formatting artefact")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    return report()


if __name__ == "__main__":
    sys.exit(main())
