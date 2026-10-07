#!/usr/bin/env python3
"""release_trigger_check — a workflow whose only trigger CANNOT FIRE is not a gate.

RQ-81-COMPLIANCE (#1453). `compliance.yml` produces the compliance report an
assessor consumes, and it had not run for FORTY-FOUR consecutive releases with no
red check anywhere. Not a failing assertion — a workflow that never started, and
a workflow that never starts has no conclusion to be red.

THE MECHANISM, and it is a property of THIS REPO rather than of that workflow:
`release.yml` publishes with `gh release create` under the default
`GITHUB_TOKEN`, and **GitHub does not start workflow runs for events raised by
`GITHUB_TOKEN`** — a deliberate recursion guard, and a silent one. So any
workflow whose only automatic trigger is `release:` can never run here.

MEASURED over all 148 releases before the fix, via the paginated API because
`gh run list` under-reports: `compliance.yml` has run 19 times EVER — 1
`workflow_dispatch` and 18 `release` events, and all 18 correspond to releases a
USER published. Zero runs since 2026-07-15. 129 of 148 releases carry no report.
The one bot-published release that HAS a report (v0.11.31) got it from that
single manual dispatch on the day the workflow landed, so the recursion guard has
no counterexample in the whole history.

THE RULE, stated as the class and not the instance: a workflow that declares a
`release:` trigger must ALSO be reachable from `release.yml` — a job with
`uses: ./.github/workflows/<it>` — or it is dead wiring. `workflow_dispatch`
does NOT satisfy this: a trigger a human must remember is what this gate exists
to replace.

WHY A SEPARATE GATE rather than an addition to `oracle_wiring_check`: that one
polices `scripts/repro/*` against workflow references, a different population.
This is one level further out — the workflow itself, not what a workflow runs.

`--self-test` drives the rule over synthetic workflow sets, including the
pre-fix shape, so the gate's own power does not rest on the live tree being
broken. A derived population of ZERO workflows is a REFUSAL, not a pass.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import yaml

WF_DIR = Path(".github/workflows")
RELEASE_WF = "release.yml"


def triggers(doc) -> dict:
    """A workflow's `on:` block. PyYAML parses the bare key `on` as the BOOLEAN
    True (YAML 1.1 treats on/off/yes/no as booleans), which is the kind of
    silent miss this programme keeps finding, so both spellings are read."""
    if not isinstance(doc, dict):
        return {}
    on = doc.get("on", doc.get(True))
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {k: None for k in on}
    return on or {}


def _cannot_run(job: dict) -> bool:
    """Is this job's `if:` a literal falsehood?

    (v0.81 round-1 cold review, finding 6.) `called_workflows` read only `uses`,
    so `if: false` on the calling job satisfied this gate while guaranteeing the
    job never runs — and a SKIPPED job does not red a workflow run either, so the
    evasion was invisible at both layers. That is the same "produces nothing,
    nothing is red" shape the gate exists to detect, one level up.

    Deliberately narrow: only a LITERAL false is detected (`if: false`, and the
    `${{ false }}` spelling YAML hands over as a string). An arbitrary expression
    cannot be evaluated here, and pretending otherwise would be a checker that
    claims more than it does.
    """
    cond = job.get("if")
    if cond is False:
        return True
    return str(cond).strip().lower().replace(" ", "") in {
        "false", "${{false}}", "${{!true}}"}


def called_workflows(doc) -> set[str]:
    """Workflow files this one invokes with `uses: ./.github/workflows/x.yml`,
    EXCLUDING jobs that cannot run. See `_cannot_run`."""
    out: set[str] = set()
    for job in (doc or {}).get("jobs", {}).values():
        if not isinstance(job, dict) or _cannot_run(job):
            continue
        uses = str(job.get("uses", ""))
        if uses.startswith("./.github/workflows/"):
            out.add(uses.rsplit("/", 1)[-1])
    return out


def uploads_to_a_release(text: str) -> bool:
    """Does this workflow's TEXT upload an asset to a GitHub Release?

    (v0.81 round-1 cold review, finding 5.) THE POPULATION USED TO BE KEYED ON
    THE `release:` TRIGGER, which is the one thing the defect removes. Measured:
    deleting `compliance.yml`'s release trigger AND release.yml's caller job left
    this gate at rc=0 with "0 failures" — a two-line edit that restores the exact
    v0.80 state of forty-four releases with no compliance report, invisible to the
    gate built to prevent it.
    
    So membership is derived from what the workflow DOES instead: a workflow that
    uploads an asset to a release must run per release, and you cannot produce a
    release asset without uploading one. The trigger is a hint; the upload is the
    capability.
    """
    return "gh release upload" in text


def check(workflows: dict[str, dict], texts: dict[str, str] | None = None) -> list[str]:
    """Findings. `workflows` maps filename -> parsed doc; `texts` maps filename ->
    raw source, used to derive the population by what a workflow DOES."""
    if not workflows:
        return ["REFUSED: zero workflows parsed. A derived population of zero is "
                "a refusal, not a pass — this is a path or parse failure"]
    if RELEASE_WF not in workflows:
        return [f"REFUSED: {RELEASE_WF} not among the parsed workflows, so "
                f"reachability cannot be derived at all"]
    reachable = called_workflows(workflows[RELEASE_WF])
    findings: list[str] = []
    for name, doc in sorted(workflows.items()):
        if name == RELEASE_WF:
            continue
        tr = triggers(doc)
        src = (texts or {}).get(name, "")
        # IN POPULATION if it declares a `release:` trigger OR if it uploads an
        # asset to a release. The second is what survives the defect: see
        # `uploads_to_a_release`.
        if "release" not in tr and not uploads_to_a_release(src):
            continue
        auto = {k for k in tr if k not in ("workflow_dispatch", "workflow_call")}
        if auto - {"release"}:
            # it has another automatic trigger (push, schedule, ...) and can run
            continue
        if name in reachable:
            continue
        why_in = ("declares a `release:` trigger and no other automatic one"
                  if "release" in tr else
                  "UPLOADS AN ASSET TO A RELEASE (`gh release upload`) and has no "
                  "automatic trigger at all")
        findings.append(
            f"DEAD TRIGGER: {name} {why_in}, and {RELEASE_WF} does not call it "
            f"(`uses: ./.github/workflows/{name}`). This repo publishes releases "
            f"with GITHUB_TOKEN, and GitHub raises no workflow runs for that "
            f"token's events — so this workflow can NEVER run. It will produce "
            f"nothing, and nothing will be red. #1453: that state lasted 44 "
            f"consecutive releases. `workflow_dispatch` does not count; a "
            f"trigger a human must remember is the defect, not the fix")
    return findings


def load(root: Path) -> tuple[dict[str, dict], dict[str, str]]:
    """(parsed docs, raw texts). The TEXTS are what the population is derived
    from, so a workflow whose YAML changes shape is still measured by what it
    does."""
    out: dict[str, dict] = {}
    texts: dict[str, str] = {}
    d = root / WF_DIR
    for f in sorted(d.glob("*.yml")) + sorted(d.glob("*.yaml")):
        raw = f.read_text()
        texts[f.name] = raw
        try:
            out[f.name] = yaml.safe_load(raw)
        except yaml.YAMLError as why:
            out[f.name] = {"__parse_error__": str(why)}
    return out, texts


def self_test() -> int:
    fails = 0

    def ck(name, cond, detail=""):
        nonlocal fails
        if cond:
            print(f"  ok   {name}")
        else:
            fails += 1
            print(f"  FAIL {name}{(' — ' + detail) if detail else ''}")

    rel_calling = {"jobs": {"a": {}, "z": {"uses": "./.github/workflows/compliance.yml"}}}
    rel_bare = {"jobs": {"a": {}}}
    comp = {"on": {"release": {"types": ["published"]}, "workflow_dispatch": {}}}

    # (RED pre-fix) exactly the v0.80 state: compliance has a release trigger and
    # release.yml does not call it.
    f = check({RELEASE_WF: rel_bare, "compliance.yml": comp})
    ck("the PRE-FIX shape is reported as a DEAD TRIGGER",
       any("DEAD TRIGGER: compliance.yml" in x for x in f), str(f))
    ck("...and the finding names the GITHUB_TOKEN mechanism, not just 'unwired'",
       any("GITHUB_TOKEN" in x for x in f), str(f))

    # POSITIVE CONTROL: with the caller job present it is silent. Without this,
    # the gate above is satisfied by one that flags everything.
    ck("CONTROL: once release.yml CALLS it, there is no finding",
       check({RELEASE_WF: rel_calling, "compliance.yml": comp}) == [],
       str(check({RELEASE_WF: rel_calling, "compliance.yml": comp})))

    # workflow_dispatch must NOT rescue it — the whole point.
    ck("CONTROL: workflow_dispatch alone does NOT satisfy the rule",
       any("DEAD TRIGGER" in x for x in
           check({RELEASE_WF: rel_bare,
                  "compliance.yml": {"on": {"release": {}, "workflow_dispatch": {}}}})))

    # a workflow with ANOTHER automatic trigger can run, so it is out of scope
    ck("CONTROL: a `push` trigger beside `release` is out of scope",
       check({RELEASE_WF: rel_bare,
              "x.yml": {"on": {"release": {}, "push": {"branches": ["main"]}}}}) == [])
    ck("CONTROL: a workflow with NO release trigger is out of scope",
       check({RELEASE_WF: rel_bare, "x.yml": {"on": {"push": {}}}}) == [])

    # THE YAML 1.1 TRAP: `on:` parses as the boolean True. A gate that reads only
    # the string key silently sees no triggers and passes everything.
    ck("the boolean-True spelling of `on:` is read",
       any("DEAD TRIGGER" in x for x in
           check({RELEASE_WF: rel_bare,
                  "c.yml": {True: {"release": {"types": ["published"]}}}})),
       "PyYAML turns a bare `on` key into True; missing that makes this vacuous")

    # (v0.81 round-1 cold review, findings 4, 5 and 6.) Each of these three
    # evasions left the gate at rc=0 with "0 failures" on the REAL tree.
    up = {"gh release upload": None}  # marker: texts carry the capability
    TEXT = {"compliance.yml": 'run: gh release upload "$TAG" "$A" --clobber'}

    # F5 — the population must survive DELETING the trigger it used to key on.
    no_trigger = {"on": {"workflow_dispatch": {}}}
    ck("F5: a workflow that UPLOADS to a release is in population without a release trigger",
       any("DEAD TRIGGER: compliance.yml" in x for x in
           check({RELEASE_WF: rel_bare, "compliance.yml": no_trigger}, TEXT)),
       "deleting the trigger must not delete the finding")
    ck("F5 CONTROL: with the caller present it is silent even then",
       check({RELEASE_WF: rel_calling, "compliance.yml": no_trigger}, TEXT) == [])
    ck("F5 CONTROL: a workflow that uploads NOTHING stays out of population",
       check({RELEASE_WF: rel_bare, "x.yml": no_trigger}, {"x.yml": "run: echo hi"}) == [])

    # F6 — a job that cannot run does not count as calling the workflow.
    rel_if_false = {"jobs": {"z": {"if": False,
                                   "uses": "./.github/workflows/compliance.yml"}}}
    ck("F6: `if: false` on the calling job does NOT satisfy the rule",
       any("DEAD TRIGGER" in x for x in
           check({RELEASE_WF: rel_if_false, "compliance.yml": comp}, TEXT)))
    ck("F6: the `${{ false }}` spelling is caught too",
       _cannot_run({"if": "${{ false }}"}) and _cannot_run({"if": "false"}))
    ck("F6 CONTROL: a REAL condition is not treated as always-false",
       not _cannot_run({"if": "github.event_name == 'push'"})
       and not _cannot_run({}),
       "an unevaluable expression must not be read as false")

    # vacuity
    ck("VACUITY: zero workflows is a REFUSAL",
       any("REFUSED" in x for x in check({})))
    ck("VACUITY: a missing release.yml is a REFUSAL, not a pass",
       any("REFUSED" in x for x in check({"compliance.yml": comp})))

    print(f"release-trigger-self-test: {fails} failure(s)")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".", type=Path)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    wfs, texts = load(args.root)
    bad = [n for n, d in wfs.items() if isinstance(d, dict) and "__parse_error__" in d]
    print(f"  workflows parsed: {len(wfs)} ({len(bad)} unparseable)")
    # (v0.81 round-1 cold review, finding 4.) An unparseable workflow used to be
    # FILTERED OUT of the population and the gate exited 0. Measured: making
    # `compliance.yml` unparseable AND deleting the caller job gave
    # "1 unparseable / 0 failures / rc=0". `check()` already refused a ZERO
    # population and a missing release.yml, so unreadable input was considered —
    # and the non-release.yml case was missed. An unreadable workflow is a gate
    # that cannot be audited, which is a refusal, not a pass.
    findings = [
        f"UNPARSEABLE: {n} could not be parsed ({(d or {})['__parse_error__'][:90]}), "
        f"so whether it needs to be reachable from {RELEASE_WF} cannot be derived. "
        f"An unreadable workflow is a refusal, not a pass"
        for n, d in sorted(wfs.items()) if "__parse_error__" in (d or {})
    ]
    findings += check({n: d for n, d in wfs.items() if "__parse_error__" not in (d or {})},
                      texts)
    for f in findings:
        print(f"FAIL {f}")
    rel = wfs.get(RELEASE_WF) or {}
    print(f"release-trigger: {len(wfs)} workflow(s), "
          f"{len(called_workflows(rel))} called from {RELEASE_WF}, "
          f"{len(findings)} failure(s)")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
