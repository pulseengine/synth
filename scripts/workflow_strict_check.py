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


# FORK GUARD (security, 2026-11-20). A pull-request job may reach a self-hosted
# runner only through the fail-CLOSED guard below: the event is not a pull
# request, or the PR's head repo IS this repo. The fail-OPEN form
# `head.repo.fork && 'ubuntu-24.04' || <self-hosted>` sends fork code to the
# self-hosted pool whenever the fork flag is null (a fork PR whose head repo was
# deleted), so any mention of `head.repo.fork` is refused outright.
FAIL_CLOSED_GUARD = ("(github.event_name != 'pull_request' || "
                     "github.event.pull_request.head.repo.full_name == "
                     "github.repository) && ")
PR_EVENTS = {"pull_request", "pull_request_target"}


def _triggers(d) -> set:
    # YAML 1.1 reads a bare `on:` key as boolean True.
    on = d.get("on", d.get(True))
    if isinstance(on, str):
        return {on}
    if isinstance(on, (list, dict)):
        return set(on)
    return set()


def fork_guard(name: str, text: str, d: dict) -> list[str]:
    out = []
    for n, line in enumerate(text.splitlines(), 1):
        if "head.repo.fork" in line:
            out.append(f"{name}:{n}: fail-open fork guard (`head.repo.fork`); use "
                       f"the fail-closed form {FAIL_CLOSED_GUARD.strip()} ...")
    if not (_triggers(d) & PR_EVENTS):
        return out
    for job, spec in (d.get("jobs") or {}).items():
        if not isinstance(spec, dict):
            continue
        ro = spec.get("runs-on")
        if ro is None:
            continue
        if isinstance(ro, str) and "${{" in ro:
            if "self-hosted" in ro and FAIL_CLOSED_GUARD not in ro:
                out.append(f"{name}: job {job}: `runs-on` can pick a self-hosted "
                           f"runner without the fail-closed guard")
        elif "self-hosted" in str(ro):
            out.append(f"{name}: job {job}: unconditional self-hosted `runs-on` in "
                       f"a workflow that pull requests trigger")
    return out


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
    out += fork_guard(path.name, text, d)
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

    # NEGATIVE CONTROLS 3-5: the fork guard.
    sh = "fromJSON('[\"self-hosted\",\"linux\",\"x64\",\"rust-cpu\"]')"
    head = "name: x\non: [pull_request]\njobs:\n  j:\n    runs-on: "
    tail = "\n    steps:\n      - run: true\n"
    cases = {
        "fail-open `head.repo.fork` form":
            "${{ github.event.pull_request.head.repo.fork && 'ubuntu-24.04' || "
            + sh + " }}",
        "self-hosted expression without the guard":
            "${{ github.event_name == 'push' && " + sh + " || 'ubuntu-24.04' }}",
        "unconditional self-hosted list": "[self-hosted, linux, x64, rust-cpu]",
    }
    for what, ro in cases.items():
        with tempfile.NamedTemporaryFile("w", suffix=".yml", delete=False) as fh:
            fh.write(head + ro + tail); tmp = Path(fh.name)
        ok(check(tmp) != [], f"NEGATIVE CONTROL: {what} is refused")
        tmp.unlink()
    good = "${{ " + FAIL_CLOSED_GUARD + sh + " || 'ubuntu-24.04' }}"
    alias = (f"name: x\non: [pull_request]\njobs:\n  a:\n    runs-on: &g {good}"
             f"{tail}  b:\n    runs-on: *g{tail}")
    with tempfile.NamedTemporaryFile("w", suffix=".yml", delete=False) as fh:
        fh.write(alias); tmp = Path(fh.name)
    ok(check(tmp) == [], "POSITIVE CONTROL: the fail-closed guard, also through "
                         "a YAML alias, passes")
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
