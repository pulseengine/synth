#!/usr/bin/env python3
"""Strict structural check for the workflow files — and a note about WHERE it
can be asked, which is the point.

WHY IT EXISTS. v0.87 pushed a `ci.yml` that `yaml.safe_load` accepted and GitHub
Actions REFUSED. The cause: a splice rewrote a step's comment block and its
`run:` line and DROPPED THE `- name:` LINE BETWEEN THEM, so that `run:` attached
to the PRECEDING step, which then carried TWO `run:` keys. PyYAML keeps the LAST
value on a duplicate key and reports nothing; Actions fails the whole workflow.
The run is then named by FILE PATH rather than by the workflow's `name:`, which
is the visible symptom, and it has NO JOBS at all.

A PERMISSIVE PARSER IS NOT A TYPED ORACLE. `safe_load` returning a dict proves
the bytes are YAML, not that they are a workflow.

AND THE PLACEMENT IS THE LESSON, not the check. A step inside `ci.yml` that
validates `ci.yml` HAS AN EMPTY WINDOW FOR THIS EXACT FAILURE: a workflow that
does not parse never runs, so the validator never executes and says nothing. It
is potent and it cannot block — the shape this release is named after. So this
script is written to be run BEFORE THE PUSH, by hand or by a hook, and a CI step
calling it can only ever cover the OTHER workflow files. Both halves are stated
so nobody installs it in the one position where it is mute.
"""
import argparse
import glob
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent


class Strict(yaml.SafeLoader):
    """SafeLoader that REFUSES a duplicate mapping key instead of keeping the last."""


def _no_dupes(loader, node, deep=False):
    mapping = {}
    for k, v in node.value:
        key = loader.construct_object(k, deep=deep)
        if key in mapping:
            raise yaml.YAMLError(
                f"DUPLICATE KEY {key!r} at line {k.start_mark.line + 1} — "
                f"safe_load would keep the LAST value silently; Actions refuses "
                f"the file"
            )
        mapping[key] = loader.construct_object(v, deep=deep)
    return mapping


Strict.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _no_dupes)


def check(path: Path) -> list[str]:
    out = []
    try:
        text = path.read_text()
    except OSError as e:
        # An unreadable file is a REPORTED failure, not a crash that takes the
        # rest of the population with it — and not a silent pass either.
        return [f"{path.name}: unreadable ({e.__class__.__name__})"]
    try:
        d = yaml.load(text, Strict)
    except yaml.YAMLError as e:
        return [f"{path.name}: {e}"]
    if not isinstance(d, dict):
        return [f"{path.name}: top level is {type(d).__name__}, not a mapping"]
    if "jobs" not in d:
        out.append(f"{path.name}: no `jobs` key")
    for job, spec in (d.get("jobs") or {}).items():
        if not isinstance(spec, dict):
            out.append(f"{path.name}: job {job} is not a mapping")
            continue
        for i, st in enumerate(spec.get("steps") or []):
            if not isinstance(st, dict):
                out.append(f"{path.name}: {job} step {i} is not a mapping")
            elif not ("run" in st or "uses" in st):
                out.append(f"{path.name}: {job} step {i} "
                           f"({st.get('name', '<unnamed>')!r}) has neither "
                           f"`run` nor `uses` — a dropped `- name:` above a "
                           f"`run:` produces exactly this")
    return out


def report() -> int:
    files = sorted(glob.glob(str(ROOT / ".github/workflows/*.yml"))) + \
            sorted(glob.glob(str(ROOT / ".github/workflows/*.yaml")))
    if not files:
        print("no workflow files found — a derived population of zero is a refusal")
        return 1
    fails = []
    for f in files:
        fails += check(Path(f))
    print(f"workflow files checked: {len(files)}")
    for m in fails:
        print(f"  FAIL {m}")
    print(f"failures: {len(fails)}")
    if not fails:
        print("\nNOTE ON PLACEMENT: a CI step running this can only cover the OTHER\n"
              "workflow files. For the workflow it lives in, a parse error means the\n"
              "workflow never runs, so the step never executes — run this BEFORE THE PUSH.")
    return 1 if fails else 0


def self_test() -> int:
    fails = 0

    def ok(cond, what):
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    # POSITIVE CONTROL: the real tree must pass, or the check is just noisy.
    live = []
    for f in sorted(glob.glob(str(ROOT / ".github/workflows/*.yml"))):
        live += check(Path(f))
    ok(not live, f"the live workflow tree passes ({len(live)} failure(s))")

    # NEGATIVE CONTROL 1 — the exact defect that shipped: a dropped `- name:`
    # leaves two `run:` keys in one step.
    dup = ("name: x\njobs:\n  j:\n    steps:\n"
           "      - name: a\n        run: one\n        run: two\n")
    try:
        yaml.load(dup, Strict); caught = False
    except yaml.YAMLError as e:
        caught = "DUPLICATE KEY" in str(e)
    ok(caught, "NEGATIVE CONTROL: a duplicate `run:` key is REFUSED (the defect "
               "that shipped — safe_load accepts it silently)")
    ok(yaml.safe_load(dup)["jobs"]["j"]["steps"][0]["run"] == "two",
       "and plain safe_load really does keep the LAST value, which is why it "
       "could not have caught this")

    # NEGATIVE CONTROL 2: a step with neither run nor uses.
    orphan = "name: x\njobs:\n  j:\n    steps:\n      - name: a\n"
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".yml", delete=False) as fh:
        fh.write(orphan); tmp = Path(fh.name)
    msgs = check(tmp)
    ok(any("neither" in m for m in msgs),
       "NEGATIVE CONTROL: a step with neither `run` nor `uses` is reported")
    tmp.unlink()

    # The empty-population refusal.
    ok(check(Path("/nonexistent.yml")) != [],
       "an unreadable file yields a failure rather than a silent pass")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else report()


if __name__ == "__main__":
    sys.exit(main())
