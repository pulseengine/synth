#!/usr/bin/env python3
"""oracle_wiring_check — gate the EXECUTION-ORACLE surface against CI wiring.

The problem this exists to kill (#890): `scripts/repro/*.py` are synth's
execution oracles — the differentials that catch silent miscompiles. Writing an
oracle and WIRING an oracle are two steps, and the second is the one that gets
dropped under release pressure. Before this gate, 69 of 150 repro scripts were
referenced by no workflow at all, and nothing in the tree distinguished

    "manual by design — needs gale's pinned drop / real silicon / a toolchain
     CI does not install"

from

    "somebody forgot".

A forgotten gate is indistinguishable from an intentional one, so the only way
to tell was to read all 150 and reason about each — an audit that kept
rediscovering the same defect one instance at a time. v0.53 hand-wired three
and the unwired count still went UP: instances were fixed, the factory was not.

THE MECHANISM — a declared status per script, in a header comment
--------------------------------------------------------------------------
Each `scripts/repro/*.py` (and `*.sh`) carries EXACTLY ONE declaration line:

    # ci-status: wired
    # ci-status: manual (hardware) — needs a real STM32H743; no emulator path
    # ci-status: unwired — needs a compile line + ELF arg; no blocker

Chosen over a central manifest deliberately:

  * LOCALITY. The declaration lives in the file it describes, so it shows up in
    the diff of the PR that adds the script — the author cannot add an oracle
    without meeting the convention. A manifest is edited far from the script and
    goes stale on rename/delete.
  * NO SECOND SOURCE OF TRUTH. A manifest entry can disagree with reality
    (script deleted, entry left behind); a header cannot outlive its file.
  * The repo already reserves the central-ledger shape (`claims.yaml`) for
    claims that have NO natural home (prose spread across many docs). A script's
    CI status has a natural home: the script.

THREE STATUSES, on purpose
--------------------------------------------------------------------------
  wired    — at least one `.github/workflows/*.yml` STEP runs the file.
             VERIFIED here: declaring `wired` without one is a hard failure —
             the exact "green board, inert gate" defect. "References" is derived
             from the PARSED workflow (a step's `run:` body plus its
             `with:`/`env:` values), never a raw grep: a mention in a COMMENT
             would otherwise satisfy the gate, and a gate satisfiable by prose
             is the very shape this check exists to reject.
  manual   — legitimately NOT CI-runnable. Requires a CATEGORY from the fixed
             list below plus a reason. Categories are a closed set so the manual
             surface stays groupable and arguable, not a free-text dumping
             ground.
  unwired  — KNOWN DEBT: no blocker, simply not wired yet. Separated from
             `manual` so honest blockers and backlog cannot hide in each other.
             This is the count that must ratchet DOWN (pinned in claims.yaml).

Undeclared = failure. New scripts are FORCED to choose.

Exit: 0 = every script declared and consistent · 1 = drift
"""

import argparse
import glob
import json
import os
import pathlib
import re
import sys

try:
    import yaml
except ImportError:  # pragma: no cover - the claim-check job installs PyYAML
    sys.exit("oracle_wiring_check: needs PyYAML  (pip install pyyaml)")

# The closed set of `manual` categories. Adding one is a deliberate code change
# (and a review conversation), not a free-text escape hatch.
MANUAL_CATEGORIES = {
    "hardware": "needs real silicon / a board CI does not have",
    "toolchain": "needs a toolchain CI does not install (cross binutils, qemu, ...)",
    "external-input": "needs an input that is not in-tree (a pinned vendor drop, a gist)",
    "network": "fetches over the network at run time",
    "measurement": "produces a REPORT, not a pass/fail verdict — nothing to gate on",
    "superseded": "the behaviour is gated elsewhere; kept as historical repro only",
    "red-first": "asserts a defect that is still OPEN — expected to fail today",
    "scratch": "ad-hoc probe kept for provenance; carries no assertions",
    "slow": "runtime is prohibitive for per-PR CI",
}

DECL_RE = re.compile(
    r"^#\s*ci-status:\s*(?P<status>[A-Za-z-]+)"
    r"(?:\s*\((?P<category>[a-z-]+)\))?"
    r"\s*(?:[-—:]+\s*(?P<reason>.*))?$",
    re.MULTILINE,
)

PLACEHOLDER_RE = re.compile(r"^\s*(todo|tbd|t\.b\.d\.?|n/?a|xxx|fixme|-+)\s*$", re.I)

MIN_REASON_CHARS = 20


def repo_root():
    return pathlib.Path(__file__).resolve().parent.parent


def collect(root):
    scripts = sorted(
        glob.glob(str(root / "scripts/repro/*.py"))
        + glob.glob(str(root / "scripts/repro/*.sh"))
    )
    workflows = sorted(
        glob.glob(str(root / ".github/workflows/*.yml"))
        + glob.glob(str(root / ".github/workflows/*.yaml"))
    )
    return scripts, workflows


def executable_surface(workflows):
    """Map workflow filename -> the text a runner would actually EXECUTE.

    A raw grep of the .yml would count a mention in a COMMENT as "wired" — a
    gate satisfied by prose, which is the failure shape this whole check exists
    to reject. So references are derived from the PARSED workflow: each step's
    `run:` body plus its `with:`/`env:` values. A workflow that will not parse
    is a hard error, never a silent pass.
    """
    surface, raw = {}, {}
    for w in workflows:
        name = os.path.basename(w)
        raw[name] = pathlib.Path(w).read_text(errors="ignore")
        try:
            doc = yaml.safe_load(raw[name]) or {}
        except yaml.YAMLError as exc:
            raise RuntimeError(f"workflow {name} does not parse: {exc}") from exc
        chunks = []
        for job in (doc.get("jobs") or {}).values():
            if not isinstance(job, dict):
                continue
            for st in job.get("steps") or []:
                if not isinstance(st, dict):
                    continue
                if isinstance(st.get("run"), str):
                    # Strip SHELL comments before counting a reference.
                    #
                    # The gate's whole point is that a mention must be something
                    # that RUNS. YAML eats `#` only in a single-line plain scalar;
                    # in a `run: |` block — which is nearly every oracle step here
                    # — the `#` survives into the script body, so commenting the
                    # body out left the script still "referenced" and the gate
                    # GREEN while the step executed nothing. Commenting out a
                    # flaky step is the most common way a gate goes inert, i.e.
                    # precisely the #890 failure this exists to reject.
                    # Found by the v0.54 cold review; the earlier
                    # comment-demotion mutation passed only because it happened
                    # to target a single-line `run:`.
                    for line in st["run"].splitlines():
                        code = line.split("#", 1)[0]
                        if code.strip():
                            chunks.append(code)
                for block in ("with", "env"):
                    for v in (st.get(block) or {}).values():
                        chunks.append(str(v))
            for v in (job.get("env") or {}).values():
                chunks.append(str(v))
        surface[name] = "\n".join(chunks)
    return surface, raw


def classify(root, scripts, workflows):
    """Return (records, failures). One record per script; failures are strings."""
    wf_text, wf_raw = executable_surface(workflows)

    records, fails = [], []
    for path in scripts:
        rel = os.path.relpath(path, root)
        name = os.path.basename(path)
        text = pathlib.Path(path).read_text(errors="ignore")
        refs = sorted(w for w, t in wf_text.items() if name in t)

        decls = list(DECL_RE.finditer(text))
        if not decls:
            fails.append(
                f"{rel}: UNDECLARED — add a `# ci-status:` header line "
                f"(wired | manual (<category>) — reason | unwired — reason). "
                f"An oracle nothing runs must SAY so."
            )
            records.append({"script": rel, "status": "undeclared", "workflows": refs})
            continue
        if len(decls) > 1:
            fails.append(
                f"{rel}: {len(decls)} `# ci-status:` lines — exactly one is allowed"
            )
        m = decls[0]
        status = m.group("status").lower()
        category = (m.group("category") or "").lower() or None
        reason = (m.group("reason") or "").strip()

        rec = {
            "script": rel,
            "status": status,
            "category": category,
            "reason": reason,
            "workflows": refs,
        }
        records.append(rec)

        if status == "wired":
            if not refs:
                mentioned = [w for w, t in wf_raw.items() if name in t]
                where = (
                    f" It IS mentioned in {', '.join(mentioned)}, but only in a "
                    f"COMMENT — prose does not run an oracle."
                    if mentioned
                    else ""
                )
                fails.append(
                    f"{rel}: declares `wired` but NO workflow STEP runs it — "
                    f"the gate is INERT.{where} Wire it in .github/workflows/, "
                    f"or downgrade the declaration to `unwired`/`manual`."
                )
            if category:
                fails.append(f"{rel}: `wired` takes no category (got {category!r})")
        elif status in ("manual", "unwired"):
            if refs:
                fails.append(
                    f"{rel}: declares `{status}` but IS referenced by "
                    f"{', '.join(refs)} — flip the declaration to `wired`."
                )
            if not reason or PLACEHOLDER_RE.match(reason) or len(reason) < MIN_REASON_CHARS:
                fails.append(
                    f"{rel}: `{status}` needs a REAL reason (>= {MIN_REASON_CHARS} "
                    f"chars, not a placeholder); got {reason!r}"
                )
            if status == "manual":
                if not category:
                    fails.append(
                        f"{rel}: `manual` needs a category: "
                        f"{', '.join(sorted(MANUAL_CATEGORIES))}"
                    )
                elif category not in MANUAL_CATEGORIES:
                    fails.append(
                        f"{rel}: unknown manual category {category!r} — "
                        f"allowed: {', '.join(sorted(MANUAL_CATEGORIES))}"
                    )
            elif category:
                fails.append(f"{rel}: `unwired` takes no category (got {category!r})")
        else:
            fails.append(
                f"{rel}: unknown ci-status {status!r} — "
                f"expected wired | manual | unwired"
            )

    # Reverse direction: a workflow STEP may not run a repro script that is gone
    # (a rename that half-landed leaves a step that can never run). Scoped to the
    # executable surface on purpose — a stale mention in a comment is untidy
    # prose, not a broken gate, and calling it one would be a false red.
    on_disk = {os.path.basename(p) for p in scripts} | {
        os.path.basename(p) for p in glob.glob(str(root / "scripts/repro/*"))
    }
    exec_blob = "\n".join(wf_text.values())
    for ref in sorted(set(re.findall(r"scripts/repro/([\w.\-]+)", exec_blob))):
        if ref not in on_disk:
            fails.append(
                f".github/workflows: references scripts/repro/{ref}, which does "
                f"NOT exist — dangling CI step"
            )

    return records, fails


def summarize(records):
    out = {"total": len(records), "wired": 0, "manual": 0, "unwired": 0, "undeclared": 0}
    by_cat = {}
    for r in records:
        s = r["status"]
        out[s] = out.get(s, 0) + 1
        if s == "manual" and r.get("category"):
            by_cat[r["category"]] = by_cat.get(r["category"], 0) + 1
    out["manual_by_category"] = dict(sorted(by_cat.items()))
    # The INERT-GATE count, carried in the summary on purpose: a consumer must
    # be able to reach the verdict from the summary ALONE, without trusting an
    # exit status. (Found by mutation: with only `pipefail` and no `-e`, a shell
    # wrapper whose last command was the summary check greened this very case.)
    out["wired_unreferenced"] = sum(
        1 for r in records if r["status"] == "wired" and not r["workflows"]
    )
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--json", metavar="PATH", help="write the summary as JSON")
    ap.add_argument("--list", action="store_true", help="print every script + status")
    args = ap.parse_args()

    root = repo_root()
    scripts, workflows = collect(root)

    # ------------------------------------------------------------------
    # ANTI-VACUITY. This gate must not become the thing it polices: a check
    # that measures nothing and exits 0. If the globs come up empty (moved
    # directory, renamed workflows, run from the wrong root) that is a HARD
    # failure, never a silent pass.
    # ------------------------------------------------------------------
    if not scripts:
        sys.exit("oracle_wiring_check: VACUOUS — scripts/repro/*.py matched NO files")
    if not workflows:
        sys.exit("oracle_wiring_check: VACUOUS — .github/workflows/*.yml matched NO files")

    records, fails = classify(root, scripts, workflows)
    summary = summarize(records)

    if summary["wired"] == 0:
        fails.append(
            "VACUOUS — zero scripts classify as `wired`; the reference "
            "derivation is broken (did the workflow layout move?)"
        )

    if args.list:
        for r in sorted(records, key=lambda r: (r["status"], r["script"])):
            tag = r["status"] + (f"({r['category']})" if r.get("category") else "")
            where = ",".join(r["workflows"]) or "-"
            print(f"  {tag:<22} {os.path.basename(r['script']):<52} {where}")
        print()

    print(
        f"oracle wiring: {summary['total']} repro scripts — "
        f"{summary['wired']} wired, {summary['manual']} manual, "
        f"{summary['unwired']} unwired(debt), {summary['undeclared']} UNDECLARED"
    )
    if summary["manual_by_category"]:
        print(
            "  manual by category: "
            + ", ".join(f"{k}={v}" for k, v in summary["manual_by_category"].items())
        )

    summary["failures"] = len(fails)

    if args.json:
        pathlib.Path(args.json).write_text(
            json.dumps(
                {"summary": summary, "scripts": records}, indent=2, sort_keys=True
            )
            + "\n"
        )

    # A GitHub step summary keeps the manual/unwired backlog visible on every
    # run instead of only in a log nobody opens.
    step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary:
        with open(step_summary, "a") as fh:
            fh.write("### Oracle wiring (#890)\n\n")
            fh.write(
                f"| total | wired | manual | unwired (debt) | undeclared |\n"
                f"|---|---|---|---|---|\n"
                f"| {summary['total']} | {summary['wired']} | {summary['manual']} "
                f"| {summary['unwired']} | {summary['undeclared']} |\n\n"
            )
            debt = [r for r in records if r["status"] == "unwired"]
            if debt:
                fh.write("**Unwired debt** (wire these; the count must ratchet down):\n\n")
                for r in sorted(debt, key=lambda r: r["script"]):
                    fh.write(f"- `{os.path.basename(r['script'])}` — {r['reason']}\n")
                fh.write("\n")

    if fails:
        print()
        for f in fails:
            print(f"FAIL {f}")
        print(f"\n{len(fails)} oracle-wiring failure(s).")
        return 1
    print("all repro scripts declare a CI status, and every `wired` one is wired.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
