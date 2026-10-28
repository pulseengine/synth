#!/usr/bin/env python3
"""mutant_residue_check — is a mutation-survey mutant sitting in this tree?

RQ-89-SWEEPMUTANT (#1611). Four v0.89 lanes found a mutant from
scripts/mutation_survey.py in their working tree after a local CI sweep's
per-command timeout killed the survey's wrapper shell (observed:
`encode_thumb2_movw(10, …)` -> `9` in crates/synth-cli/src/main.rs — the
`CONTROL/startup-r10-seeded-into-r9` mutant — and a reach probe in
crates/synth-backend/src/arm_backend.rs). A mutant committed that way passes CI
silently unless an oracle happens to kill it, which for an UNTESTED, EQUIVALENT
or DEAD mutant is by definition not the case.

The survey now applies mutants only to a shadow copy, so this should never
fire. It is the cheap commit-side check that would have caught every incident
whatever the survey does: it reads the mutation ledger's own catalogue
(docs/status/mutation_survey.json — every surveyed mutant and control records
its file and its `after` text) and fails if any `after` block is present in
its file, matched as whole lines ANYWHERE in the file, because line numbers
drift and the ledger's control line numbers are stale by design. It also fails
on the two markers only the survey writes: the reach-probe marker
`SYNTH-MUTANT-REACHED` and the DROPMOV `/* MUTANT:` comment, which catch a
probe or a never-catalogued site, and on a shadow-tree marker file, which
means a shadow copy was committed or the check is being run on one.

MEASURED at authoring (7e170d62): every one of the 34 mutants' and 3
controls' `after` blocks occurs 0 times in the clean tree, so the check has no
standing false positive. A legitimate future edit CAN equal an `after` (a BOUND
mutant is one character from plausible code): the failure then names the
site, and the remedy is to re-survey or `retire` that site, not to weaken
this check.

usage: python3 scripts/mutant_residue_check.py [--root DIR] [--ledger PATH]
       python3 scripts/mutant_residue_check.py --self-test
exit 0 clean, 1 residue found, 2 the ledger is unusable (a catalogue this
check cannot read must not read as "no residue").
"""
import argparse
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = "docs/status/mutation_survey.json"
MARKERS = ("SYNTH-MUTANT-REACHED", "/* MUTANT:")
SHADOW_MARKER = ".synth-mutation-shadow"
SCAN_DIRS = ("crates",)


def catalogue(ledger):
    """[(id, file, after)] for every mutant and control the ledger records.
    `retired` entries carry no file (the code they mutated is gone)."""
    out = []
    for key in ("mutants", "controls"):
        for m in ledger.get(key) or []:
            if m.get("file") and m.get("after", "").strip():
                out.append((m["id"], m["file"], m["after"]))
    return out


def find_block(text, block):
    """1-based line numbers where `block` occurs as whole consecutive lines."""
    lines = text.split("\n")
    want = block.split("\n")
    n = len(want)
    return [i + 1 for i in range(len(lines) - n + 1) if lines[i:i + n] == want]


def check(root, ledger_path):
    """Returns (problems, n_sites, n_files_scanned); raises ValueError when the
    ledger cannot be used."""
    root = Path(root)
    try:
        ledger = json.loads(Path(ledger_path).read_text())
    except (OSError, ValueError) as e:
        raise ValueError(f"cannot read the mutation ledger {ledger_path}: {e}")
    sites = catalogue(ledger)
    if not sites:
        raise ValueError(f"{ledger_path} catalogues no mutant: nothing to check against")
    problems = []
    cache = {}
    for sid, rel, after in sites:
        p = root / rel
        if not p.is_file():
            continue  # a deleted file holds no mutant; reanchor reports the site
        text = cache.setdefault(rel, p.read_text(errors="replace"))
        for line in find_block(text, after):
            problems.append(f"{rel}:{line}: the `after` text of mutant {sid} is in the tree: "
                            f"{after.strip()[:90]!r}")
    scanned = 0
    for d in SCAN_DIRS:
        for dirpath, dirnames, filenames in os.walk(root / d):
            dirnames[:] = [x for x in dirnames if x not in ("target", ".git")]
            for f in filenames:
                if not f.endswith(".rs"):
                    continue
                p = Path(dirpath) / f
                scanned += 1
                for i, line in enumerate(p.read_text(errors="replace").split("\n"), 1):
                    for mk in MARKERS:
                        if mk in line:
                            problems.append(f"{p.relative_to(root)}:{i}: survey marker {mk!r}: {line.strip()[:90]!r}")
    if (root / SHADOW_MARKER).exists():
        problems.append(f"{SHADOW_MARKER}: this tree is a mutation-survey SHADOW copy, not a checkout")
    return problems, len(sites), scanned


def report(root, ledger_path):
    try:
        problems, n_sites, scanned = check(root, ledger_path)
    except ValueError as e:
        print(f"MUTANT-RESIDUE UNUSABLE: {e}")
        return 2
    for p in problems:
        print(f"RESIDUE: {p}")
    print(f"MUTANT-RESIDUE sites={n_sites} rs-files={scanned} residue={len(problems)}")
    if problems:
        print("A mutation-survey mutant is in this tree. Restore the named lines "
              "(`git diff` shows them; `git checkout -- <file>` if the file has no other "
              "change) before committing. If the text is a LEGITIMATE edit that happens "
              "to equal a recorded mutant, re-survey or `mutation_survey.py retire` that "
              "site — do not weaken this check (RQ-89-SWEEPMUTANT, #1611).")
        return 1
    if scanned == 0:
        print("VACUOUS: no .rs file scanned")
        return 2
    return 0


OPS = ("REG", "COND", "DROPMOV", "IMM", "GUARD", "BOUND")


def _site_key(m):
    return (m.get("file", ""), m.get("before", ""), m.get("after", ""))


def select_plants(ledger, root):
    """The self-test's plant cases, chosen STRUCTURALLY from the live catalogue
    and never by id: every control, plus the first mutant of each
    operator kind (ordered by file and `before` text, so the choice is
    independent of ids too), each kept only if its `before` text resolves in the tree as
    whole lines (a site the tree no longer holds cannot be planted). Ids move:
    a re-anchor renames a site by its line number (#1602 moved
    arm_backend.rs:1805:36 to :1807:36), so naming one here reds a required
    job on an unrelated PR. Returns (plants, problems)."""
    def resolves(m):
        f = Path(root) / m.get("file", "")
        return (f.is_file() and m.get("before") and m.get("after", "").strip()
                and m["before"] != m["after"]
                and find_block(f.read_text(errors="replace"), m["before"]))

    problems = []
    controls = [c for c in sorted(ledger.get("controls") or [], key=_site_key) if resolves(c)]
    if not controls:
        problems.append("no control in the ledger resolves in this tree")
    by_op = {}
    for m in sorted(ledger.get("mutants") or [], key=_site_key):
        if m.get("op") in OPS and m["op"] not in by_op and resolves(m):
            by_op[m["op"]] = m
    if not by_op:
        problems.append("no mutant of any operator kind resolves in this tree")
    return controls + [by_op[o] for o in OPS if o in by_op], problems


def self_test():
    """Red-first on a throwaway copy: every selected control and per-operator
    mutant planted -> 1 each, a reach-probe marker -> 1, a DROPMOV marker -> 1,
    the clean and restored copies -> 0, an empty catalogue -> 2. Exit 2 with a
    plain message (never a traceback) when the catalogue cannot supply a case."""
    try:
        ledger = json.loads((ROOT / LEDGER).read_text())
    except (OSError, ValueError) as e:
        print(f"MUTANT-RESIDUE-SELFTEST UNUSABLE: cannot read {LEDGER}: {e}")
        return 2
    plants, problems = select_plants(ledger, ROOT)
    if problems:
        for p in problems:
            print(f"MUTANT-RESIDUE-SELFTEST UNUSABLE: {p}")
        print("The self-test plants cases drawn from the ledger's own catalogue; with none "
              "resolvable it cannot show the check still bites. Re-anchor the ledger "
              "(`mutation_survey.py reanchor`) rather than weakening this test.")
        return 2
    files = sorted({p["file"] for p in plants})
    failures = []
    cases = 0
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        for rel in files:
            (td / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, td / rel)
        (td / LEDGER).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / LEDGER, td / LEDGER)
        clean = {rel: (td / rel).read_text() for rel in files}

        def plant(site, text_lines):
            # the same whole-line replacement mutation_survey's Edit makes, by
            # content (the controls' recorded line numbers are stale)
            p = td / site["file"]
            text = p.read_text()
            lines = text.split("\n")
            at = find_block(text, site["before"])[0]
            n = len(site["before"].split("\n"))
            lines[at - 1:at - 1 + n] = text_lines
            p.write_text("\n".join(lines))

        def run(label, want):
            nonlocal cases
            cases += 1
            got = report(td, td / LEDGER)
            ok = got == want
            print(f"self-test {label}: rc={got} want={want} {'ok' if ok else 'FAIL'}")
            if not ok:
                failures.append(label)

        run("clean copy", 0)
        for site in plants:
            plant(site, site["after"].split("\n"))
            run(f"planted {site['id']}", 1)
            (td / site["file"]).write_text(clean[site["file"]])
        run("restored copy", 0)
        host = plants[0]
        for label, marker in (("reach probe", '{ eprintln!("SYNTH-MUTANT-REACHED"); }'),
                              ("DROPMOV marker", "/* MUTANT: Mov dropped */ ();")):
            plant(host, host["before"].split("\n") + [marker])
            run(f"planted {label}", 1)
            (td / host["file"]).write_text(clean[host["file"]])
        (td / LEDGER).write_text(json.dumps({"mutants": [], "controls": []}))
        run("empty catalogue", 2)
    print(f"MUTANT-RESIDUE-SELFTEST cases={cases} planted={len(plants)} failures={len(failures)}")
    return 1 if failures else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--ledger", type=Path)
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        sys.exit(self_test())
    sys.exit(report(a.root, a.ledger or a.root / LEDGER))


if __name__ == "__main__":
    main()
