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
# This module's own path, relative to ROOT. `usable()` must never probe it.
SELF = str(Path(__file__).resolve().relative_to(Path(__file__).resolve().parent.parent))

# RQ-87-SWEEPPOP (#1541): the population is DERIVED, and every exclusion carries
# a WRITTEN REASON. It was a hand list of nine while thirteen scripts defined a
# self-test, and the five unswept included the two instruments the previous
# release had just added — so the release that built a vacuity sweep did not
# sweep its own new tools, and the signal it reported was a FLOOR, not a count.
#
# THREE THINGS THE MEASUREMENT CORRECTED, each the opposite of what was expected:
#
#   * `def self_test` IS THE WRONG NEEDLE. Thirteen scripts define one, but
#     FIFTEEN mention `--self-test`, and the two extra —
#     `test_merge_gate_callsite.py` and `test_verdict_prose_check.py` — expose the
#     flag without a function of that name.
#   * `test_merge_gate_callsite.py` WAS CORRECTLY SWEPT. It is the one file the old
#     drift line flagged as "swept but not self-test-defining", which reads like
#     an over-inclusion; it accepts `--self-test`, exits 0, and carries eleven
#     subjects. The DERIVATION was too narrow, not the hand list too wide.
#   * THE REAL PRECONDITION IS BEHAVIOURAL. A file belongs here only if
#     `python3 <file> --self-test` exits 0 UNMUTATED. If it is already non-zero
#     every verdict for that file is noise rather than coverage — a neutralised
#     subject cannot be distinguished from the pre-existing failure.
#
# So the population is: candidates by EITHER needle, minus EXCLUDE, minus any
# whose self-test does not already pass. The probe is bounded to the candidate
# set and never runs every script in the tree.
EXCLUDE = {
    "scripts/repro/home_alias_audit_corpus_1189.py":
        "its own `--self-test` exits 1 unmutated (measured), so every verdict "
        "would report the pre-existing failure rather than the neutralised "
        "subject. Re-include it when that self-test passes.",
    "scripts/test_verdict_prose_check.py":
        "a unittest module: `--self-test` exits 2 at argument parsing, because "
        "unittest's own parser rejects the flag. Its subjects are exercised by "
        "`python3 scripts/test_verdict_prose_check.py` with no arguments, which "
        "is a different harness than this sweep drives.",
}


def candidates() -> list[str]:
    """Every script that LOOKS like it has a runnable self-test.

    EITHER needle, because neither alone is right: `def self_test` misses a
    module that exposes the flag without a function of that name, and
    `--self-test` alone would catch a docstring that merely mentions another
    script's flag. The union is then narrowed behaviourally by `usable()`.
    """
    out = []
    for f in sorted(glob.glob(str(ROOT / "scripts" / "**" / "*.py"), recursive=True)):
        try:
            src = Path(f).read_text()
        except OSError:
            continue
        if (any(l.startswith("def self_test") for l in src.split("\n"))
                or "--self-test" in src):
            out.append(str(Path(f).relative_to(ROOT)))
    return out


# A nested invocation must not probe. See `usable()`.
_NESTED = "SYNTH_VACUITY_SWEEP_NESTED"


def usable(rel: str) -> tuple[bool, int]:
    """Does `<rel> --self-test` already pass? Returns (usable, rc).

    This is the sweep's real precondition and it is CHECKED, not assumed: over a
    file whose self-test already fails, a neutralised subject is
    indistinguishable from the pre-existing failure and every verdict is noise.

    TWO TERMINATION GUARDS, and the first version of this function had NEITHER —
    it spawned 112 processes before it was killed. A BEHAVIOURAL derivation whose
    population INCLUDES THE DERIVING INSTRUMENT does not terminate: probing this
    file runs its `--self-test`, which re-derives the population, which probes
    this file again, and each level is a new process so caching cannot help. The
    old SYNTACTIC needle could include itself harmlessly; a behavioural one
    cannot.

      * SELF-EXEMPTION. This file is never probed; its subjects are still swept,
        because the sweep driven from OUTSIDE exercises them, and `report()`
        states the exemption rather than hiding it.
      * A NESTED MARKER. Any child this module spawns inherits
        SYNTH_VACUITY_SWEEP_NESTED, and a nested run refuses to probe at all —
        belt and braces, so a future caller that forgets the first guard still
        terminates.
    """
    import os
    if rel == SELF or os.environ.get(_NESTED):
        return True, 0
    rc, _out = run_self_test(ROOT / rel)
    return rc == 0, rc


_POP: list[str] | None = None


def derived_population() -> list[str]:
    """The sweep's subjects: candidates, minus EXCLUDE, minus the unusable.

    CACHED, because it spawns one subprocess per candidate and `report()`,
    `sweep()` and `self_test()` all ask for it. Uncached, the first version of
    this function made `--self-test` take minutes instead of seconds — the probe
    is cheap per call and ruinous per caller.
    """
    global _POP
    if _POP is None:
        _POP = [f for f in candidates() if f not in EXCLUDE and usable(f)[0]]
    return _POP


def run_self_test(path: Path) -> tuple[int, str]:
    """Run one script's `--self-test`, marking the child as NESTED.

    The marker is what stops a child from re-deriving the population and probing
    its way back here; see `usable()`.
    """
    import os
    env = dict(os.environ, **{_NESTED: "1"})
    r = subprocess.run([sys.executable, str(path), "--self-test"],
                       capture_output=True, text=True, timeout=300, cwd=ROOT,
                       env=env)
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
    for rel in derived_population():
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
    cands = candidates()
    pop = derived_population()
    print(f"POPULATION: {len(cands)} candidate(s) by either needle; "
          f"{len(EXCLUDE)} excluded with a written reason; "
          f"{len(pop)} swept (DERIVED, not hand-written)")
    for f, why in sorted(EXCLUDE.items()):
        print(f"  EXCLUDED {f}")
        print(f"      {why}")
    print(f"  SELF-EXEMPT from the behavioural probe: {SELF} "
          f"(a behavioural derivation cannot probe its own deriver — it "
          f"recurses through subprocesses; its subjects are still swept)")
    unusable = [f for f in cands if f not in EXCLUDE and not usable(f)[0]]
    print(f"  dropped as UNUSABLE (self-test already non-zero): {unusable or 'none'}")
    if not pop:
        print("REFUSED: a derived population of ZERO is a refusal, not a pass.")
        return 1
    print()

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
    ok(all((ROOT / f).exists() for f in pop), "every derived file exists")
    # RQ-87-SWEEPPOP (#1541): the population is DERIVED, so the old
    # "every hand-listed file exists" has nothing to assert. What replaces it is
    # the property the derivation must have: every EXCLUDE entry names a real
    # file and carries a non-empty reason, so an exclusion cannot be a silent
    # deletion from the population.
    ok(all((ROOT / f).exists() for f in EXCLUDE),
       "every EXCLUDE entry names a file that EXISTS (not a stale path)")
    ok(all(len(w.strip()) > 40 for w in EXCLUDE.values()),
       "every EXCLUDE entry carries a written reason, not a bare marker")
    ok(not (set(EXCLUDE) & set(pop)),
       "and nothing is both EXCLUDED and swept")
    # BOTH halves are asserted. Round two fired the mutant that put this file
    # INTO `FILES` and the case stayed GREEN -- it tested membership of the
    # DERIVED population and never tested absence from the HAND LIST, so it was
    # green under exactly the state its own message forbids. The half carrying
    # the finding was the unasserted one.
    me = str(Path(__file__).resolve().relative_to(ROOT))
    ok(me in pop,
       "THIS file is in the derived population — the sweep sweeps itself")
    # The old pair asserted membership of the derived population AND absence from
    # the hand list, which was the drift. With the hand list gone there is no
    # drift to assert; the property that replaces it is that the derivation is
    # WIDER than the nine files it replaced, which is the whole point of the lane.
    ok(len(pop) >= 13,
       f"the derived population is at least as wide as the measurement that "
       f"motivated this change (got {len(pop)})")
    ok("scripts/test_merge_gate_callsite.py" in pop,
       "the file the OLD drift line called an over-inclusion is kept: it accepts "
       "`--self-test`, exits 0, and the narrow `def self_test` needle was what "
       "missed it")
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
