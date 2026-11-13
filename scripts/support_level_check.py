#!/usr/bin/env python3
"""support_level_check — RQ-91-SUPPORTLEVELS: a backend's support level is
held by its EVIDENCE, so a demotion reds CI and a promotion cannot be asserted.

THE LEVELS (cumulative: L1 must also meet L2)
  L1 verified          Rocq proofs for the covered ops, a wasmtime execution
                       differential in a REQUIRED check, a WCET gate in a
                       required check, and an acceptance-ladder rung that
                       measures THIS backend.
  L2 execution-tested  wasmtime execution differentials that the oracle-wiring
                       gate classifies as `wired`, and named loud-decline
                       evidence. "EVERY unsupported shape declines loudly" is
                       NOT mechanically checkable; what is checked is that the
                       named decline tripwires exist and run. The residual is
                       stated in the table, not implied away.
  L3 experimental      no correctness claim, so nothing to hold.

"Support level", never "tier": T1/T2/T3 are the Rocq proof tiers.

WHERE EACH FACT LIVES (one source each, nothing hand-copied)
  * the LEVEL and the evidence NAMES: `support_levels:` in claims.yaml;
  * whether an oracle RUNS: `oracle_wiring_check.classify` (imported, not
    re-implemented), and which JOB runs it: `oracle_wiring_check.step_chunks`;
  * which jobs are REQUIRED: `ci_pool_tripwire.REQUIRED_CONTEXTS`, resolved by
    `ci_pool_tripwire.resolve_required_contexts` (imported);
  * which backend a piece of evidence is ABOUT: `BACKENDS` below. It is code,
    not ledger data, ON PURPOSE: a backend absent from it can only be L3, so
    promoting one (x86-64, say) needs a reviewed change here plus evidence
    that passes, never an edited level string.
  * the published level: the `## Support levels` table of the generated
    docs/status/FEATURE_MATRIX.md, which must EQUAL the ledger row for row and
    name every piece of evidence the ledger cites.

An L1 criterion may be declared OPEN only where this file can verify the CAUSE
of the gap (today: one — the acceptance ladder's census invocation selects no
Cortex-M target, so its `arm` rung measures the A32 encoder). A declared gap
whose cause no longer holds is red, so it cannot outlive its reason; a gap on
any other criterion is red, so "open" is not a way to promote.

The table copies NO number from docs/status/ACCEPTANCE_LADDER.md (#1286): a
percentage in the section is red.

Usage:  support_level_check.py [claims.yaml]   |   --self-test
Exit 0 clean, 1 findings.
"""
from __future__ import annotations

import ast
import importlib.util
import pathlib
import re
import shutil
import sys
import tempfile

try:
    import yaml
except ImportError:  # pragma: no cover - the claim-check job installs PyYAML
    sys.exit("support_level_check: needs PyYAML  (pip install pyyaml)")

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
LEVELS = ("L1", "L2", "L3")
DOC = "docs/status/FEATURE_MATRIX.md"
LADDER_DOC = "docs/status/ACCEPTANCE_LADDER.md"
LADDER_SCRIPT = "scripts/repro/partial_census_1017.py"
SECTION = "## Support levels"

# Which backend a piece of evidence is ABOUT.
#   invocation — must match a wasmtime differential's own text or the text of a
#                workflow step that runs it (where the compile line usually is)
#   identity   — must match a decline tripwire's path or text
#   ladder     — must match a string constant of the census invocation for the
#                ladder rung to measure this backend
BACKENDS = {
    "cortex-m-thumb2": {
        "invocation": r"cortex-m(?:3|4|4f|7|7dp)\b|--cortex-m\b",
        "identity": r"cortex-m|Thumb",
        "ladder": r"^--cortex-m$|^cortex-m",
    },
    "rv32": {
        "invocation": r"\briscv\b|\brv32",
        "identity": r"riscv|rv32|RV32",
        "ladder": r"^riscv$",
    },
    "aarch64": {
        "invocation": r"\baarch64\b",
        "identity": r"aarch64",
        "ladder": r"^aarch64$",
    },
    "cortex-r5-relocatable": {
        "invocation": r"cortex-r5\b[^\n]*--relocatable",
        "identity": r"cortex-r5|\bA32\b",
        "ladder": r"^cortex-r5$",
    },
}

# The only L1 criterion that may be declared open, and the verifier of its cause.
OPENABLE = {"ladder"}


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


OWC = _load("oracle_wiring_check", HERE / "oracle_wiring_check.py")
CPT = _load("ci_pool_tripwire", HERE / "ci_pool_tripwire.py")


def load_workflows(root):
    out = {}
    wf = root / ".github/workflows"
    for p in sorted(list(wf.glob("*.yml")) + list(wf.glob("*.yaml"))):
        out[str(p.relative_to(root))] = yaml.safe_load(p.read_text()) or {}
    return out


def job_surface(job):
    chunks = []
    for st in (job or {}).get("steps") or []:
        chunks.extend(OWC.step_chunks(st))
    return "\n".join(chunks)


def required_surfaces(workflows, required):
    """{context: executable text of the job that reports it} — a job gated by a
    job-level `if:` is left out, since it may report SKIPPED."""
    resolved, _fails = CPT.resolve_required_contexts(required, workflows)
    out = {}
    for ctx, (_path, job) in resolved.items():
        if job.get("if") is None:
            out[ctx] = job_surface(job)
    return out


def all_step_texts(workflows):
    for doc in workflows.values():
        for job in ((doc or {}).get("jobs") or {}).values():
            if isinstance(job, dict):
                for st in job.get("steps") or []:
                    yield "\n".join(OWC.step_chunks(st))


def parse_table(doc_text):
    """{row name: (level, row text)} from the `## Support levels` section, and
    the section text itself."""
    if SECTION not in doc_text:
        return None, ""
    sec = doc_text.split(SECTION, 1)[1]
    nxt = re.search(r"^## ", sec, re.M)
    sec = sec[: nxt.start()] if nxt else sec
    rows = {}
    for line in sec.splitlines():
        if not line.startswith("|") or re.match(r"^\|\s*-", line):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 3 or cells[0] == "Backend":
            continue
        m = re.match(r"(L[123])\b", cells[1])
        rows[cells[0]] = (m.group(1) if m else cells[1], line)
    return rows, sec


def census_constants(root):
    """String constants of the ladder census's compile invocation: `run_synth`
    and `LADDER_RUNGS`."""
    tree = ast.parse((root / LADDER_SCRIPT).read_text())
    consts = []
    for node in tree.body:
        hit = (isinstance(node, ast.FunctionDef) and node.name == "run_synth") or (
            isinstance(node, ast.Assign)
            and any(isinstance(t, ast.Name) and t.id == "LADDER_RUNGS" for t in node.targets)
        )
        if hit:
            consts += [n.value for n in ast.walk(node)
                       if isinstance(n, ast.Constant) and isinstance(n.value, str)]
    return consts


def ladder_rows(root):
    text = (root / LADDER_DOC).read_text()
    if "## The ladder" not in text:
        return set()
    sec = text.split("## The ladder", 1)[1]
    nxt = re.search(r"^## ", sec, re.M)
    sec = sec[: nxt.start()] if nxt else sec
    return set(re.findall(r"^\|\s*\*\*(\w+)\*\*\s*\|", sec, re.M))


def check(root, ledger, required):
    fails = []
    root = pathlib.Path(root)
    entries = (ledger or {}).get("backends") or []
    if not entries:
        return ["support_levels.backends is EMPTY — the table would hold vacuously"]

    scripts, wf_paths = OWC.collect(root)
    records, _ = OWC.classify(root, scripts, wf_paths)
    wired = {r["script"] for r in records if r["status"] == "wired" and r["workflows"]}
    workflows = load_workflows(root)
    req = required_surfaces(workflows, required)
    steps = list(all_step_texts(workflows))

    rows, section = parse_table((root / DOC).read_text())
    if rows is None:
        return [f"{DOC} has no `{SECTION}` section"]
    if re.search(r"\d\s*%", section):
        fails.append(f"{DOC} `{SECTION}` carries a percentage — cite "
                     f"{LADDER_DOC}, never copy its numbers (#1286)")
    if LADDER_DOC.split("/")[-1] not in section:
        fails.append(f"{DOC} `{SECTION}` does not cite {LADDER_DOC}")

    seen = set()
    for e in entries:
        bid, row, level = e.get("id"), e.get("row"), e.get("level")
        where = f"backend {bid!r}"
        if level not in LEVELS:
            fails.append(f"{where}: level {level!r} is not one of {LEVELS}")
            continue
        seen.add(row)
        if row not in rows:
            fails.append(f"{where}: no table row named {row!r} in {DOC}")
            continue
        tlevel, rtext = rows[row]
        if tlevel != level:
            fails.append(f"{where}: table says {tlevel}, ledger says {level} — "
                         f"DRIFT; move both together, and only through this gate")

        def named(item, what):
            if item and item not in rtext:
                fails.append(f"{where}: {what} {item!r} is not named in its table row")

        if level == "L3":
            continue
        spec = BACKENDS.get(bid)
        if spec is None:
            fails.append(f"{where}: is {level} but has no entry in BACKENDS — a "
                         f"backend above L3 must be registered in "
                         f"scripts/support_level_check.py with its evidence "
                         f"(promotion by assertion is refused)")
            continue
        inv, ident = re.compile(spec["invocation"]), re.compile(spec["identity"])

        # --- L2: wired wasmtime differentials about this backend ----------
        diffs = e.get("differentials") or []
        if not diffs:
            fails.append(f"{where}: {level} needs >=1 wasmtime differential; none named")
        good_diffs = []
        for d in diffs:
            p = root / d
            if not p.exists():
                fails.append(f"{where}: differential {d} does not exist")
                continue
            text = p.read_text(errors="ignore")
            if "wasmtime" not in text:
                fails.append(f"{where}: {d} is not a wasmtime differential")
                continue
            if d not in wired:
                fails.append(f"{where}: {d} is not WIRED (oracle_wiring_check "
                             f"finds no workflow step that runs it) — DEMOTION")
                continue
            base = p.name
            about = inv.search(text) or any(
                base in s and inv.search(s) for s in steps)
            if not about:
                fails.append(f"{where}: {d} never invokes this backend "
                             f"(/{spec['invocation']}/ in neither the script nor "
                             f"the step that runs it)")
                continue
            named(base, "differential")
            good_diffs.append(base)

        declines = e.get("declines") or []
        if not declines:
            fails.append(f"{where}: {level} needs >=1 named loud-decline tripwire")
        for d in declines:
            p = root / d
            if not p.exists():
                fails.append(f"{where}: decline tripwire {d} does not exist")
                continue
            text = p.read_text(errors="ignore")
            if not (ident.search(d) or ident.search(text)):
                fails.append(f"{where}: decline tripwire {d} is not about this backend")
            if d.endswith(".rs"):
                if "#[test]" not in text:
                    fails.append(f"{where}: {d} holds no #[test]")
                if not any("cargo test --workspace" in s for s in req.values()):
                    fails.append(f"{where}: no required check runs `cargo test "
                                 f"--workspace`, so {d} runs nowhere required")
            elif d not in wired:
                fails.append(f"{where}: decline oracle {d} is not WIRED — DEMOTION")
            named(p.name, "decline tripwire")

        if level != "L1":
            if e.get("open"):
                fails.append(f"{where}: only an L1 criterion may be declared open")
            continue

        # --- L1 -----------------------------------------------------------
        open_ = {o.get("criterion"): o for o in (e.get("open") or [])}
        for c in open_:
            if c not in OPENABLE:
                fails.append(f"{where}: criterion {c!r} declared open, but this "
                             f"checker can verify the cause of no such gap — an "
                             f"open L1 criterion is not a way to promote")
        in_req = [(ctx, b) for b in good_diffs for ctx, s in req.items() if b in s]
        if not in_req:
            fails.append(f"{where}: L1 needs a wasmtime differential in a REQUIRED "
                         f"check; none of {good_diffs} runs in one of "
                         f"{sorted(req)} — DEMOTION")
        for ctx, _b in in_req[:1]:
            named(ctx, "required check")

        proofs = e.get("proofs") or []
        if not proofs:
            fails.append(f"{where}: L1 needs Rocq proofs; none named")
        for v in proofs:
            p = root / v
            if not p.exists() or "Qed." not in p.read_text(errors="ignore"):
                fails.append(f"{where}: proof file {v} is missing or holds no Qed.")
            named(v, "proof file")
        pctx = [c for c, s in req.items() if "//coq:verify_proofs" in s]
        if not pctx:
            fails.append(f"{where}: no required check runs `bazel test "
                         f"//coq:verify_proofs` — the proofs are compiled nowhere required")
        else:
            named(pctx[0], "required check")

        wcet = e.get("wcet_gate")
        stem = pathlib.Path(wcet).stem if wcet else None
        if not wcet or not (root / wcet).exists():
            fails.append(f"{where}: L1 needs a WCET gate test file; got {wcet!r}")
        else:
            wctx = [c for c, s in req.items()
                    if re.search(r"--test\s+" + re.escape(stem) + r"\b", s)]
            if not wctx:
                fails.append(f"{where}: no required check runs `--test {stem}` — "
                             f"the WCET gate runs nowhere required — DEMOTION")
            else:
                named(stem, "WCET gate")
                named(wctx[0], "required check")

        rung = e.get("ladder_rung")
        met, why = False, ""
        if not rung:
            why = "no ladder rung named"
        elif rung not in ladder_rows(root):
            why = f"{LADDER_DOC} has no `**{rung}**` row under `## The ladder`"
        else:
            lad = re.compile(spec["ladder"])
            if any(lad.search(c) for c in census_constants(root)):
                met = True
            else:
                why = (f"the `{rung}` rung is measured by {LADDER_SCRIPT}, whose "
                       f"compile invocation selects no constant matching "
                       f"/{spec['ladder']}/ — it measures a different target")
        if met and "ladder" in open_:
            fails.append(f"{where}: ladder criterion declared OPEN but it is now "
                         f"MET — the cause is gone; delete the open entry")
        elif not met and "ladder" not in open_:
            fails.append(f"{where}: L1 ladder criterion NOT MET: {why}")
        elif not met:
            if len((open_["ladder"].get("reason") or "").strip()) < 40:
                fails.append(f"{where}: open ladder criterion needs a >=40-char reason")
            if "not met" not in rtext:
                fails.append(f"{where}: the ladder criterion is open, and its "
                             f"table row does not say `not met`")
            named(LADDER_SCRIPT.split("/")[-1], "ladder census")

    for r in rows:
        if r not in seen:
            fails.append(f"{DOC} `{SECTION}` row {r!r} has no ledger entry in "
                         f"claims.yaml support_levels")
    return fails


# ---------------------------------------------------------------------------
# --self-test: a synthetic tree, one GREEN baseline, and one mutation per way
# a level can lie. Each mutation must red with its own reason.
# ---------------------------------------------------------------------------

_DIFF = ("#!/usr/bin/env python3\n# ci-status: wired\n# ci-checks: emulations >= 1\n"
         "# executes {inv} against wasmtime\n")
_CI = """on:
  pull_request:
jobs:
  test:
    name: Test
    steps:
      - run: cargo test --workspace
      - run: cargo test -p synth-cli --test wcet_gate
  bazel:
    name: Bazel
    steps:
      - run: bazel test //coq:verify_proofs
  spec:
    name: Spec Exec
    steps:
      - run: python3 scripts/oracle_run.py scripts/repro/m_diff.py
  other:
    name: Other
    steps:
      - run: python3 scripts/oracle_run.py scripts/repro/rv_diff.py
"""
_CENSUS = ('def run_synth(synth, module, backend, extra, timeout):\n'
           '    cmd = [synth, "compile", "-b", backend, "--relocatable"]\n'
           'LADDER_RUNGS = [("default", [])]\n')
_LADDER = "# L\n\n## The ladder\n\n| backend | default |\n|---|---|\n| **arm** | x |\n\n## Next\n"
_TABLE = ("# M\n\n" + SECTION + "\n\nCites ACCEPTANCE_LADDER.md.\n\n"
          "| Backend | Level | Evidence |\n|---|---|---|\n"
          "| CM | L1 verified | m_diff.py in Spec Exec; P.v in Bazel; wcet_gate in "
          "Test; m_decl.rs; coq/P.v; ladder not met: partial_census_1017.py |\n"
          "| RV | L2 execution-tested | rv_diff.py; rv_decl.rs |\n"
          "| X | L3 experimental | none |\n\n## After\n")


def _ledger():
    return {"backends": [
        {"id": "cortex-m-thumb2", "row": "CM", "level": "L1",
         "differentials": ["scripts/repro/m_diff.py"],
         "declines": ["crates/c/tests/m_decl.rs"],
         "proofs": ["coq/P.v"], "wcet_gate": "crates/c/tests/wcet_gate.rs",
         "ladder_rung": "arm",
         "open": [{"criterion": "ladder", "reason": "the arm rung is measured "
                   "with no Cortex-M target, so it measures A32"}]},
        {"id": "rv32", "row": "RV", "level": "L2",
         "differentials": ["scripts/repro/rv_diff.py"],
         "declines": ["crates/c/tests/rv_decl.rs"]},
        {"id": "x86-64", "row": "X", "level": "L3"},
    ]}


def _tree(tmp):
    files = {
        "scripts/repro/m_diff.py": _DIFF.format(inv="--target cortex-m4"),
        "scripts/repro/rv_diff.py": _DIFF.format(inv="-b riscv"),
        "crates/c/tests/m_decl.rs": "// Thumb decline\n#[test]\nfn t() {}\n",
        "crates/c/tests/rv_decl.rs": "// riscv decline\n#[test]\nfn t() {}\n",
        "crates/c/tests/wcet_gate.rs": "#[test]\nfn w() {}\n",
        "coq/P.v": "Theorem t : True. Proof. exact I. Qed.\n",
        ".github/workflows/ci.yml": _CI,
        LADDER_SCRIPT: _CENSUS,
        LADDER_DOC: _LADDER,
        DOC: _TABLE,
    }
    for rel, body in files.items():
        p = tmp / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body)


def _edit(tmp, rel, old, new):
    p = tmp / rel
    t = p.read_text()
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new))


def self_test():
    required = ["Test", "Bazel", "Spec Exec"]
    bad = 0

    def case(name, mutate, needle, ledger_mut=None):
        nonlocal bad
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="slc-"))
        try:
            _tree(tmp)
            led = _ledger()
            if mutate:
                mutate(tmp)
            if ledger_mut:
                ledger_mut(led)
            fails = check(tmp, led, required)
        finally:
            shutil.rmtree(tmp)
        if needle is None:
            ok = fails == []
        else:
            ok = any(needle in f for f in fails)
        print(f"  {'ok  ' if ok else 'FAIL'} {name}: "
              f"{'green' if not fails else fails[0][:110]}")
        if not ok:
            bad += 1
            for f in fails:
                print(f"         {f}")

    case("baseline is GREEN", None, None)
    case("demote: the L2 differential's CI step removed",
         lambda t: _edit(t, ".github/workflows/ci.yml",
                         "      - run: python3 scripts/oracle_run.py scripts/repro/rv_diff.py\n",
                         "      - run: true\n"),
         "is not WIRED")
    case("demote: the step is commented out",
         lambda t: _edit(t, ".github/workflows/ci.yml",
                         "run: python3 scripts/oracle_run.py scripts/repro/rv_diff.py",
                         "run: true # scripts/repro/rv_diff.py"),
         "is not WIRED")
    case("drift: the table's level for one backend changed",
         lambda t: _edit(t, DOC, "| RV | L2 ", "| RV | L3 "), "DRIFT")
    case("promotion by assertion: x86-64 marked L2, no evidence",
         lambda t: _edit(t, DOC, "| X | L3 ", "| X | L2 "),
         "promotion by assertion is refused",
         lambda led: led["backends"][2].update(level="L2"))
    case("promotion by borrowed evidence: x86-64 L2 citing RV's differential",
         lambda t: _edit(t, DOC, "| X | L3 experimental | none |",
                         "| X | L2 | rv_diff.py; rv_decl.rs |"),
         "promotion by assertion is refused",
         lambda led: led["backends"][2].update(
             id="x86-64", level="L2",
             differentials=["scripts/repro/rv_diff.py"],
             declines=["crates/c/tests/rv_decl.rs"]))
    case("evidence about ANOTHER backend",
         lambda t: _edit(t, "scripts/repro/rv_diff.py", "-b riscv", "-b arm"),
         "never invokes this backend")
    case("L1 differential moved out of every required check",
         lambda t: _edit(t, ".github/workflows/ci.yml", "name: Spec Exec", "name: Spec Exec (advisory)"),
         "in a REQUIRED check")
    case("L1 WCET gate dropped from the required check",
         lambda t: _edit(t, ".github/workflows/ci.yml",
                         "      - run: cargo test -p synth-cli --test wcet_gate\n", ""),
         "WCET gate runs nowhere required")
    case("L1 proofs no longer compiled in a required check",
         lambda t: _edit(t, ".github/workflows/ci.yml",
                         "bazel test //coq:verify_proofs", "bazel build //crates:synth"),
         "compiled nowhere required")
    case("L1 proof file holds no Qed",
         lambda t: _edit(t, "coq/P.v", "Qed.", "Admitted."), "holds no Qed")
    case("open ladder gap whose cause is GONE (census now passes --cortex-m)",
         lambda t: _edit(t, LADDER_SCRIPT, '"--relocatable"]', '"--relocatable", "--cortex-m"]'),
         "now MET")
    case("ladder gap not declared",
         None, "ladder criterion NOT MET",
         lambda led: led["backends"][0].pop("open"))
    case("an L1 criterion other than the ladder declared open",
         None, "an open L1 criterion is not a way to promote",
         lambda led: led["backends"][0]["open"].append({"criterion": "wcet"}))
    case("a ladder number copied into the table",
         lambda t: _edit(t, DOC, "| X | L3 experimental | none |",
                         "| X | L3 experimental | none (arm 11.1 %) |"),
         "carries a percentage")
    case("a table row with no ledger entry",
         lambda t: _edit(t, DOC, "| X | L3 experimental | none |\n",
                         "| X | L3 experimental | none |\n| Y | L3 | none |\n"),
         "has no ledger entry")
    case("evidence the row does not name",
         lambda t: _edit(t, DOC, "rv_diff.py; ", ""),
         "is not named in its table row")
    case("empty ledger", None, "EMPTY", lambda led: led.update(backends=[]))
    print(f"support_level_check self-test: {bad} failure(s)")
    return 1 if bad else 0


def main(argv):
    if "--self-test" in argv:
        return self_test()
    args = [a for a in argv if not a.startswith("--")]
    path = pathlib.Path(args[0]) if args else ROOT / "claims.yaml"
    data = yaml.safe_load(path.read_text()) or {}
    ledger = data.get("support_levels")
    if ledger is None:
        print(f"FAIL {path} has no `support_levels:` section")
        return 1
    fails = check(path.resolve().parent, ledger, CPT.REQUIRED_CONTEXTS)
    for e in ledger.get("backends") or []:
        print(f"  {e.get('level')}  {e.get('id')}")
    for f in fails:
        print(f"FAIL {f}")
    print(f"support-levels: {len(fails)} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
