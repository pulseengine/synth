#!/usr/bin/env python3
"""support_level_check — RQ-91-SUPPORTLEVELS: a backend's support level is
held by its EVIDENCE, so a demotion reds CI and a promotion cannot be asserted.

THE LEVELS (cumulative: L1 must also meet L2)
  L1 verified          Rocq proofs for the covered ops, a wasmtime execution
                       differential in a REQUIRED check, a WCET gate in a
                       required check, and an acceptance-ladder rung that
                       measures THIS backend.
  L2 execution-tested  execution differentials that RUN in CI, and named
                       loud-decline evidence. A differential is either a
                       wasmtime differential under scripts/repro that the
                       oracle-wiring gate classifies as `wired`, or a Rust
                       oracle under crates/synth-oracle/tests (kiln reference
                       against unicorn; new oracles are Rust since
                       2026-11-18) that a workflow step runs AND pins by an
                       exact `ORACLE <tag>:` result line (`rust_differential`). "EVERY unsupported shape declines loudly" is
                       NOT mechanically checkable; what is checked is that the
                       named decline tripwires exist and run. The residual is
                       stated in the table, not implied away.
  L3 experimental      no correctness claim, so nothing to hold.

"Support level", never "tier": T1/T2/T3 are the Rocq proof tiers.

WHERE EACH FACT LIVES (one source each, nothing hand-copied)
  * the LEVEL and the evidence NAMES: `support_levels:` in claims.yaml;
  * whether an oracle RUNS: `oracle_wiring_check.classify` (imported, not
    re-implemented), and which JOB runs it: `oracle_wiring_check.step_chunks`;
    for a Rust oracle, `rust_differential` below, over the same
    `step_chunks` reading of a workflow step (the wiring gate collects
    scripts/repro only, so it has no record of a `.rs` oracle to import);
  * which jobs are REQUIRED: `ci_pool_tripwire.REQUIRED_CONTEXTS`, resolved by
    `ci_pool_tripwire.resolve_required_contexts` (imported);
  * which backend a piece of evidence is ABOUT: `BACKENDS` below. It is code,
    not ledger data, ON PURPOSE: a backend absent from it can only be L3, so
    promoting one (x86-64, say) needs a reviewed change here plus evidence
    that passes, never an edited level string.
  * that L1 evidence is ABOUT the row's backend (RQ-91-LEVELGATE): a proof
    file must `Require` the backend's Rocq ISA model (`proof_isa`) outside a
    (nested) comment, and hold a `Qed.` outside one; a WCET gate must pass
    the backend's target in a compile-TARGET position (`rust_target_literals`:
    a `compile*` call argument or the literal after `-t`/`--target`/`-b`);
    a ladder rung measures the backend only if the census command's
    backend-flag POSITION holds run_synth's unrebound `backend` parameter
    (`census_invocation`). Residual: a gate that compiles for a target only to
    assert WCET declines there still binds. Before RQ-91-LEVELGATE an
    RV32 row could cite Thumb-2's proofs and WCET gate, and no rung could
    meet the ladder criterion for any backend.
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
#   ladder     — must match one token of the rung's EFFECTIVE census
#                invocation (`census_invocation`): run_synth's command with the
#                `backend` parameter bound to the rung's own name, plus the
#                rung flags — so a rung measures this backend only if the
#                command it really runs selects it
#   proof_isa  — must match a module the Rocq proof file itself
#                `Require`s: the ISA semantics its theorems are stated over.
#                A proof about another ISA's model cannot be cited (RQ-91-LEVELGATE).
#                None = no Rocq ISA model exists for this backend, so NO proof
#                file can be bound and L1 is unreachable until one is written.
#   emu_cpu    — must match the CODE (comments and strings blanked) of a Rust
#                oracle cited as a differential: the unicorn CPU model the
#                oracle executes on. Compiling for a target and emulating on
#                another core's model is not a differential about this
#                backend. Absent = no Rust oracle can be bound to the backend.
# The WCET gate is bound by `invocation`, matched against the gate's string
# literals in a compile-TARGET position (`rust_target_literals`): an argument
# of a `compile*` helper call, or the literal after `-t`/`--target`/`-b`. A
# comment, an attribute, an assert message or an unused `let` cannot bind it.
# RESIDUAL, stated rather than implied away: a gate that compiles for the
# target only to assert that WCET DECLINES there still binds — position says
# the gate compiles for the backend, not that it bounds it.
BACKENDS = {
    "cortex-m-thumb2": {
        "invocation": r"cortex-m(?:3|4|4f|7|7dp)\b|--cortex-m\b",
        "identity": r"cortex-m|Thumb",
        "ladder": r"^--cortex-m$|^cortex-m",
        "proof_isa": r"^Synth\.ARM\.ArmSemantics$",
    },
    "rv32": {
        "invocation": r"\briscv\b|\brv32",
        "identity": r"riscv|rv32|RV32",
        "ladder": r"^riscv$",
        "proof_isa": None,
    },
    "aarch64": {
        "invocation": r"\baarch64\b",
        "identity": r"aarch64",
        "ladder": r"^aarch64$",
        "proof_isa": None,
    },
    # The A32 encoder consumes the same ArmOp stream as Thumb-2, but no Rocq
    # file models A32 ENCODING; binding it to ArmSemantics would let it borrow
    # Thumb-2's proofs, so it binds to nothing until an A32 model exists.
    "cortex-r5-relocatable": {
        "invocation": r"cortex-r5\b[^\n]*--relocatable",
        "identity": r"cortex-r5|\bA32\b",
        "ladder": r"^cortex-r5$",
        "proof_isa": None,
    },
    # RQ-92-WDGTHIN (#1741): ARMv6-M. Its differentials are Rust oracles that
    # execute on unicorn's Cortex-M0 model. No Rocq file models ARMv6-M
    # encoding, and no WCET model covers the core, so L1 is unreachable.
    "cortex-m0-armv6m": {
        "invocation": r"\bcortex-m0(?:plus)?\b",
        "identity": r"cortex-m0|ARMv6-M",
        "ladder": r"^cortex-m0(?:plus)?$",
        "proof_isa": None,
        "emu_cpu": r"\bCpu::CortexM0\b",
    },
}

RUST_ORACLE_DIR = "crates/synth-oracle/tests/"
# The command that runs the oracle crate WITH its engines; without
# `--features exec` every oracle file is `#![cfg]`-ed out and runs nothing.
RUST_ORACLE_RUN = re.compile(
    r"cargo\s+test\b[^\n]*-p\s+synth-oracle\b[^\n]*--features\s+exec\b")

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


BACKEND_FLAGS = ("-b", "--backend", "-t", "--target")


def census_invocation(root, rung):
    """Tokens of the command the ladder census runs for the rung `rung`.

    The `## The ladder` row name is the value the census was run with
    (`--backend <rung>`), which reaches `run_synth` as its `backend` parameter.
    Every string constant of `run_synth` and `LADDER_RUNGS` is a token. The
    rung name is a token ONLY BY POSITION: a list element that is the bare
    name `backend`, directly after a backend-selecting flag constant
    (`BACKEND_FLAGS`), where `backend` is a parameter of `run_synth` that the
    function never rebinds. A mention elsewhere (a log line) adds nothing; a
    hard-coded `"-b", "arm"` measures arm; `backend = "arm"` before the command
    measures arm. Before RQ-91-LEVELGATE this matched the constants alone,
    where the backend is a variable, so no rung could ever measure any backend."""
    tree = ast.parse((root / LADDER_SCRIPT).read_text())
    toks = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == "run_synth":
            a = node.args
            params = {x.arg for x in a.posonlyargs + a.args + a.kwonlyargs}
            rebound = any(
                isinstance(n, ast.Name) and n.id == "backend"
                and isinstance(n.ctx, (ast.Store, ast.Del))
                for n in ast.walk(node))
            bound = "backend" in params and not rebound
            for n in ast.walk(node):
                if isinstance(n, ast.Constant) and isinstance(n.value, str):
                    toks.append(n.value)
                elif bound and isinstance(n, (ast.List, ast.Tuple)):
                    for prev, cur in zip(n.elts, n.elts[1:]):
                        if (isinstance(prev, ast.Constant) and prev.value in BACKEND_FLAGS
                                and isinstance(cur, ast.Name) and cur.id == "backend"):
                            toks.append(rung)
        elif isinstance(node, ast.Assign) and any(
                isinstance(t, ast.Name) and t.id == "LADDER_RUNGS" for t in node.targets):
            toks += [n.value for n in ast.walk(node)
                     if isinstance(n, ast.Constant) and isinstance(n.value, str)]
    return toks


def _rust_lex(text):
    """(literals, masked): each string literal — plain, byte and raw
    (`r#"..."#`) — as (content, start, end) offsets of its delimiters, and the
    source with every comment (`//`, nested `/* */`) and every string or char
    literal blanked to spaces (newlines kept), so brackets can be matched on
    code alone. A quote inside a raw string, a comment or a char literal
    cannot shift the pairing. A lexer, not a parser: tokens only."""
    out, i, n = [], 0, len(text)
    masked = list(text)

    def blank(a, b):
        for k in range(a, min(b, n)):
            if masked[k] != "\n":
                masked[k] = " "

    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif text.startswith("/*", i):
            s, depth, i = i, 1, i + 2
            while i < n and depth:
                if text.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            blank(s, i)
        elif (m := re.match(r'b?r(#*)"', text[i:i + 300])) and (
                i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            close = '"' + m.group(1)
            start = i + m.end()
            j = text.find(close, start)
            j = n if j < 0 else j
            out.append((text[start:j], i, j + len(close)))
            blank(i, j + len(close))
            i = j + len(close)
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append((text[i + 1:j], i, j + 1))
            blank(i, j + 1)
            i = j + 1
        elif c == "'" and (m := re.match(r"'(?:\\.[^']*|[^\\'])'", text[i:i + 12])):
            blank(i, i + m.end())
            i += m.end()
        else:
            i += 1
    return out, "".join(masked)


def rust_string_literals(text):
    """Contents of a Rust source's string literals (see `_rust_lex`)."""
    return [s for s, _a, _b in _rust_lex(text)[0]]


# A literal is a compile TARGET when it is a direct argument of a call whose
# callee is a `compile*` helper, or directly follows a target-selecting flag
# literal in an argument list (`"-t", "cortex-m4"`). Nothing else counts: not
# an attribute (`#[cfg(feature = "riscv")]`), not a message argument of
# `assert!`/`panic!`/a decline check, not a `let` that is never passed on.
TARGET_CALLEE = re.compile(r"^compile\w*$")


def _enclosing_call(masked, pos):
    """Callee name of the innermost bracket that encloses `pos`, if it is a
    call's `(`; None for `[`, `{` or top level."""
    depth = 0
    for k in range(pos - 1, -1, -1):
        ch = masked[k]
        if ch in ")]}":
            depth += 1
        elif ch in "([{":
            if depth:
                depth -= 1
                continue
            if ch != "(":
                return None
            m = re.search(r"([A-Za-z_][\w]*)\s*!?\s*$", masked[:k])
            return m.group(1) if m else None
    return None


def rust_target_literals(text):
    """Contents of the string literals that are in a compile-TARGET position."""
    lits, masked = _rust_lex(text)
    out = []
    for idx, (s, a, _b) in enumerate(lits):
        callee = _enclosing_call(masked, a)
        flagged = idx > 0 and lits[idx - 1][0] in BACKEND_FLAGS and re.fullmatch(
            r"\s*,\s*", masked[lits[idx - 1][2]:a]) is not None
        if flagged or (callee and TARGET_CALLEE.match(callee)):
            out.append(s)
    return out


# What makes a Rust block or item DEAD for `rust_differential`: it is behind
# `#[ignore]` (cargo does not run the test), behind a `#[cfg(..)]` attribute
# (it may not be compiled; the file-level `#![cfg(feature = "exec")]` is an
# inner attribute and is not matched), or the body of `if false` / `if cfg!(..)`.
_DEAD_HEADER = re.compile(
    r"#\s*\[\s*(?:ignore|cfg|cfg_attr)\b|\bif\s+false\s*$|\bif\s+!?\s*cfg\s*!\s*\([^{]*$")


def rust_dead_at(code, pos):
    """Whether offset `pos` of the lexed Rust `code` (comments and literals
    blanked, see `_rust_lex`) sits in a block that does not run: any enclosing
    `{` whose HEADER — the text between the previous `;`, `{` or `}` at that
    nesting and the brace, which holds an item's attributes — matches
    `_DEAD_HEADER`. A lexical walk, not a parser."""
    depth, k = 0, pos - 1
    while k >= 0:
        ch = code[k]
        if ch == "}":
            depth += 1
        elif ch == "{":
            if depth:
                depth -= 1
            else:
                h, paren = k - 1, 0
                while h >= 0 and not (code[h] in ";{}" and paren == 0):
                    if code[h] in ")]":
                        paren += 1
                    elif code[h] in "([":
                        paren -= 1
                    h -= 1
                if _DEAD_HEADER.search(code[h + 1:k]):
                    return True
        k -= 1
    return False


def rust_oracle_tags(text, live_only=False):
    """The `ORACLE <tag>:` result lines a Rust oracle prints: the tag of every
    string literal that begins `ORACLE <tag>:`. With `live_only`, only the
    literals outside dead blocks (`rust_dead_at`)."""
    lits, code = _rust_lex(text)
    tags = set()
    for s, a, _b in lits:
        m = re.match(r"ORACLE ([^:{}\n]+):", s)
        if m and not (live_only and rust_dead_at(code, a)):
            tags.add(m.group(1))
    return tags


def rust_differential(root, d, spec, steps):
    """Why the Rust oracle `d` is NOT a wired execution differential about the
    backend `spec`, or None when it is one.

    * a kiln-vs-unicorn differential: under RUST_ORACLE_DIR, compiled only
      with the engines (`#![cfg(feature = "exec")]`), and its CODE calls the
      harness's judged comparison (`run_case` / `run_hosted`);
    * ABOUT the backend: a string literal in a compile-TARGET position
      matches `invocation`, and the code names the backend's emulator model
      (`emu_cpu`);
    * WIRED: some workflow step runs the oracle crate with `--features exec`
      (and, if it filters with `--test`, selects this file) and the SAME step
      greps, exactly (`grep -qx`), an `ORACLE <tag>:` line whose tag this file
      prints and no other oracle file does. A step that runs the crate but
      pins no result line of this file would stay green with the file's
      tests deleted, so it does not count.
    * NOT HOLLOW IN THE TWO WAYS THAT CAN BE READ LEXICALLY (cold review of
      v092-m0-l2, F2): at least one `run_case` / `run_hosted` call, and the
      pinned `ORACLE` line, sit outside dead blocks (`rust_dead_at`: an
      `#[ignore]`d test, a `#[cfg]`-gated item, the body of `if false` or
      `if cfg!(..)`).

    RESIDUAL, a REVIEW-TIME obligation and not a caught one: this reads text,
    not control flow or data flow. It does not show that the comparison is
    REACHED (a helper nobody calls, an early `return`, `if 1 == 2`), that its
    verdict is ASSERTED, or that the count in the pinned line comes from the
    comparison rather than a literal. The wasmtime path is weaker still (the
    word `wasmtime` plus wiring). What holds those is the oracle's own red
    evidence, recorded with the lane that adds it: red on the base binary, a
    planted wrong reference that must disagree, exact counts."""
    if not d.startswith(RUST_ORACLE_DIR):
        return (f"is a Rust file outside {RUST_ORACLE_DIR} — only an oracle of the "
                f"synth-oracle harness can be cited as a differential")
    text = (root / d).read_text(errors="ignore")
    _lits, code = _rust_lex(text)
    if not re.search(r'^#!\[cfg\(feature\s*=\s*"exec"\)\]', text, re.M):
        return 'is not gated on `#![cfg(feature = "exec")]`, so it runs no engine'
    runs = [m.start() for m in re.finditer(r"\b(?:run_case|run_hosted)\s*\(", code)]
    if not runs:
        return ("is not a kiln-vs-unicorn execution differential (its code calls "
                "neither `run_case` nor `run_hosted`)")
    if all(rust_dead_at(code, p) for p in runs):
        return ("is a HOLLOW differential: every `run_case` / `run_hosted` call sits "
                "in a block that does not run (an `#[ignore]`d or `#[cfg]`-gated "
                "item, or the body of `if false` / `if cfg!(..)`)")
    if not any(re.search(spec["invocation"], s) for s in rust_target_literals(text)):
        return (f"never compiles for this backend (no compile-target literal "
                f"matches /{spec['invocation']}/)")
    emu = spec.get("emu_cpu")
    if not emu:
        return ("cannot be bound to this backend — no emulator model is "
                "registered for it (BACKENDS emu_cpu)")
    if not re.search(emu, code):
        return (f"never executes on this backend's emulator model (its code "
                f"names nothing matching /{emu}/)")
    stem = pathlib.Path(d).stem
    others = set()
    for p in sorted((root / RUST_ORACLE_DIR).glob("*.rs")):
        if p.name != pathlib.Path(d).name:
            others |= rust_oracle_tags(p.read_text(errors="ignore"))
    if not rust_oracle_tags(text) - others:
        return "prints no `ORACLE <tag>:` result line of its own to pin"
    own = rust_oracle_tags(text, live_only=True) - others
    if not own:
        return ("is a HOLLOW differential: it prints its `ORACLE <tag>:` result "
                "line only from a block that does not run (an `#[ignore]`d or "
                "`#[cfg]`-gated item, or the body of `if false` / `if cfg!(..)`)")
    for s in steps:
        if not RUST_ORACLE_RUN.search(s):
            continue
        only = re.findall(r"--test\s+([\w-]+)", s)
        if only and stem not in only:
            continue
        if any(re.search(r"grep\s+-qx\s+'ORACLE " + re.escape(t) + ":", s) for t in own):
            return None
    return ("is not WIRED (no workflow step runs `cargo test -p synth-oracle "
            "--features exec` and pins one of its `ORACLE <tag>:` lines with "
            "`grep -qx`) — DEMOTION")


def rocq_strip_comments(text):
    """Rocq source with its comments removed. Rocq comments NEST, so the
    innermost `(* ... *)` is removed until none is left; a non-greedy single
    pass would end the outer comment at the inner `*)`."""
    inner = re.compile(r"\(\*(?:(?!\(\*|\*\)).)*\*\)", re.S)
    while True:
        new = inner.sub(" ", text)
        if new == text:
            return text
        text = new


def rocq_requires(text):
    """Module paths a Rocq file `Require`s (Import/Export), comments stripped."""
    text = rocq_strip_comments(text)
    mods = []
    for m in re.finditer(r"\bRequire\s+(?:(?:Import|Export)\s+)?(.+?)\.(?=\s|$)",
                         text, re.S):
        mods += m.group(1).split()
    return mods


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

        # --- L2: wired execution differentials about this backend ---------
        diffs = e.get("differentials") or []
        if not diffs:
            fails.append(f"{where}: {level} needs >=1 execution differential; none named")
        good_diffs = []
        for d in diffs:
            p = root / d
            if not p.exists():
                fails.append(f"{where}: differential {d} does not exist")
                continue
            if d.endswith(".rs"):
                why = rust_differential(root, d, spec, steps)
                if why:
                    fails.append(f"{where}: {d} {why}")
                    continue
                named(p.name, "differential")
                good_diffs.append(p.name)
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
        isa = spec.get("proof_isa")
        for v in proofs:
            p = root / v
            ptext = p.read_text(errors="ignore") if p.exists() else ""
            if not re.search(r"\bQed\.", rocq_strip_comments(ptext)):
                fails.append(f"{where}: proof file {v} is missing or holds no Qed.")
            elif isa is None:
                fails.append(f"{where}: proof file {v} cannot be bound to this "
                             f"backend — no Rocq ISA model exists for it "
                             f"(BACKENDS proof_isa is None); a proof about "
                             f"another ISA is BORROWED evidence")
            elif not any(re.search(isa, m) for m in rocq_requires(ptext)):
                fails.append(f"{where}: proof file {v} Requires no module matching "
                             f"/{isa}/ — its theorems are not about this "
                             f"backend's ISA (BORROWED evidence)")
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
        elif not any(inv.search(s) for s in
                     rust_target_literals((root / wcet).read_text(errors="ignore"))):
            fails.append(f"{where}: WCET gate {wcet} never compiles for this "
                         f"backend (no compile-target literal matches "
                         f"/{spec['invocation']}/) — BORROWED evidence")
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
            if any(lad.search(c) for c in census_invocation(root, rung)):
                met = True
            else:
                why = (f"the `{rung}` rung is measured by {LADDER_SCRIPT}, whose "
                       f"compile invocation for that rung selects no token matching "
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
_ORACLE_WF = """on:
  pull_request:
jobs:
  oracle:
    name: Oracle
    steps:
      - run: |
          cargo test -p synth-oracle --features exec -- --nocapture | tee log
          grep -qx 'ORACLE m0-diff: 7 cases agree' log
"""
_M0_ORACLE = ('//! An ARMv6-M oracle.\n#![cfg(feature = "exec")]\n'
              'use synth_oracle::emulate::Cpu;\n'
              '#[test]\nfn agree() {\n'
              '    let obj = compile_probes("cortex-m0");\n'
              '    let c = run_case(&obj, Cpu::CortexM0);\n'
              '    eprintln!("ORACLE m0-diff: {} cases agree", c);\n}\n')
_CENSUS = ('def run_synth(synth, module, backend, extra, timeout):\n'
           '    cmd = [synth, "compile", "-b", backend, "--relocatable"]\n'
           'LADDER_RUNGS = [("default", [])]\n')
_LADDER = "# L\n\n## The ladder\n\n| backend | default |\n|---|---|\n| **arm** | x |\n\n## Next\n"
_TABLE = ("# M\n\n" + SECTION + "\n\nCites ACCEPTANCE_LADDER.md.\n\n"
          "| Backend | Level | Evidence |\n|---|---|---|\n"
          "| CM | L1 verified | m_diff.py in Spec Exec; P.v in Bazel; wcet_gate in "
          "Test; m_decl.rs; coq/P.v; ladder not met: partial_census_1017.py |\n"
          "| RV | L2 execution-tested | rv_diff.py; rv_decl.rs |\n"
          "| M0 | L2 execution-tested | m0_oracle.rs; m0_decl.rs |\n"
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
        {"id": "cortex-m0-armv6m", "row": "M0", "level": "L2",
         "differentials": [RUST_ORACLE_DIR + "m0_oracle.rs"],
         "declines": ["crates/c/tests/m0_decl.rs"]},
    ]}


def _tree(tmp):
    files = {
        "scripts/repro/m_diff.py": _DIFF.format(inv="--target cortex-m4"),
        "scripts/repro/rv_diff.py": _DIFF.format(inv="-b riscv"),
        "crates/c/tests/m_decl.rs": "// Thumb decline\n#[test]\nfn t() {}\n",
        "crates/c/tests/rv_decl.rs": "// riscv decline\n#[test]\nfn t() {}\n",
        "crates/c/tests/m0_decl.rs": "// cortex-m0 decline\n#[test]\nfn t() {}\n",
        RUST_ORACLE_DIR + "m0_oracle.rs": _M0_ORACLE,
        # A second oracle file, about another backend, in the same crate.
        RUST_ORACLE_DIR + "m3_oracle.rs": _M0_ORACLE.replace("m0-diff", "m3-diff")
        .replace("cortex-m0", "cortex-m3").replace("CortexM0", "CortexM3"),
        ".github/workflows/oracle.yml": _ORACLE_WF,
        # The raw string holds an ODD number of quotes before the target
        # literal: a quote-pairing regex mis-pairs everything after it (as it
        # did on the real wcet_bound_gate.rs), so the green baseline itself
        # holds the lexer.
        "crates/c/tests/wcet_gate.rs": ('const W: &str = r#"(module (; a lone " ;))"#;\n'
                                        '#[test]\nfn w() { compile_wcet(W, "cortex-m4"); }\n'),
        "coq/P.v": ("Require Import Synth.ARM.ArmSemantics.\n"
                    "Theorem t : True. Proof. exact I. Qed.\n"),
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

    def case(name, mutate, needle, ledger_mut=None, absent=None):
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
        if absent is not None:
            ok = not any(absent in f for f in fails)
        elif needle is None:
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

    # --- RQ-91-LEVELGATE: L1 evidence must be ABOUT the row's backend --------
    def rv_l1(**kw):
        def m(led):
            led["backends"][1].update(level="L1", **kw)
        return m
    case("BORROWED proofs: RV32 L1 citing the ARM-model proof file",
         None, "'rv32': proof file coq/P.v cannot be bound",
         rv_l1(proofs=["coq/P.v"]))
    case("proof file that Requires no ArmSemantics (named in a comment only)",
         lambda t: _edit(t, "coq/P.v", "Require Import Synth.ARM.ArmSemantics.\n",
                         "(* Require Import Synth.ARM.ArmSemantics. *)\n"),
         "Requires no module matching")
    case("BORROWED WCET gate: RV32 L1 citing a gate that compiles cortex-m4 only",
         None, "'rv32': WCET gate crates/c/tests/wcet_gate.rs never compiles",
         rv_l1(wcet_gate="crates/c/tests/wcet_gate.rs"))
    # The target, QUOTED and in a compile-call position, but inside a comment
    # or behind a char literal that holds a quote. Each one binds if the
    # lexer stops skipping that construct, so each holds one lexer branch.
    W_CALL = 'compile_wcet(W, "cortex-m4");'
    for label, repl in (
            ("a `//` line comment", 'compile_wcet(W, "x"); // compile_wcet(W, "cortex-m4");'),
            ("a `/* */` block comment", 'compile_wcet(W, "x"); /* compile_wcet(W, "cortex-m4"); */'),
            ("a quote held in a char literal", 'compile_wcet(W, \'"\', "x"); // ", "cortex-m4");')):
        case(f"WCET target quoted in a compile call inside {label} does not bind",
             lambda t, r=repl: _edit(t, "crates/c/tests/wcet_gate.rs", W_CALL, r),
             "never compiles for this backend")
    case("WCET target after a `-t` flag literal BINDS (the flag position)",
         lambda t: _edit(t, "crates/c/tests/wcet_gate.rs", W_CALL,
                         'run(&["compile", "-t", "cortex-m4"]);'),
         None, absent="never compiles for this backend")
    case("WCET target only in a #[cfg(feature)] attribute: RV32 L1 cites the gate",
         lambda t: _edit(t, "crates/c/tests/wcet_gate.rs", "#[test]\nfn w()",
                         '#[cfg(feature = "riscv")]\n#[test]\nfn w()'),
         "'rv32': WCET gate crates/c/tests/wcet_gate.rs never compiles",
         rv_l1(wcet_gate="crates/c/tests/wcet_gate.rs"))
    case("WCET target only in an assert message: RV32 L1 cites the gate",
         lambda t: _edit(t, "crates/c/tests/wcet_gate.rs", W_CALL,
                         W_CALL + ' assert!(declines(W), "wcet must decline on riscv");'),
         "'rv32': WCET gate crates/c/tests/wcet_gate.rs never compiles",
         rv_l1(wcet_gate="crates/c/tests/wcet_gate.rs"))
    case("WCET target only in a `let` never passed to the compiler",
         lambda t: _edit(t, "crates/c/tests/wcet_gate.rs", W_CALL,
                         'let _doc = "todo: cortex-m4";'),
         "never compiles for this backend")
    case("Require inside a NESTED Rocq comment does not bind",
         lambda t: _edit(t, "coq/P.v", "Require Import Synth.ARM.ArmSemantics.\n",
                         "(* old (* inner *) Require Import Synth.ARM.ArmSemantics. *)\n"),
         "Requires no module matching")
    case("`Qed.` only inside a Rocq comment is no Qed",
         lambda t: _edit(t, "coq/P.v", "Theorem t : True. Proof. exact I. Qed.", "(* Qed. *)"),
         "holds no Qed")
    case("`Qed.` only inside a NESTED Rocq comment is no Qed",
         lambda t: _edit(t, "coq/P.v", "Theorem t : True. Proof. exact I. Qed.",
                         "(* a (* b *) Qed. *)"),
         "holds no Qed")
    lad_rv = (lambda t: _edit(t, LADDER_DOC, "| **arm** | x |\n",
                              "| **arm** | x |\n| **riscv** | x |\n"))
    case("a real rung MEETS the ladder: RV32 L1 on the `riscv` rung",
         lad_rv, None, rv_l1(ladder_rung="riscv"),
         absent="'rv32': L1 ladder criterion NOT MET")
    case("a real rung MEETS the ladder: an open gap on it reds as now MET",
         lad_rv, "'rv32': ladder criterion declared OPEN but it is now MET",
         rv_l1(ladder_rung="riscv", open=[{"criterion": "ladder",
                                           "reason": "x" * 40}]))
    case("the rung does not measure it when the census hard-codes `-b arm`",
         lambda t: (lad_rv(t), _edit(t, LADDER_SCRIPT, '"-b", backend', '"-b", "arm"')),
         "'rv32': L1 ladder criterion NOT MET", rv_l1(ladder_rung="riscv"))
    case("ladder by POSITION: `-b arm` hard-coded while a log line mentions backend",
         lambda t: (lad_rv(t), _edit(t, LADDER_SCRIPT,
                    'cmd = [synth, "compile", "-b", backend, "--relocatable"]',
                    'cmd = [synth, "compile", "-b", "arm", "--relocatable"]\n'
                    '    print("measuring", backend)')),
         "'rv32': L1 ladder criterion NOT MET", rv_l1(ladder_rung="riscv"))
    case("ladder: `backend` REBOUND to \"arm\" before the command",
         lambda t: (lad_rv(t), _edit(t, LADDER_SCRIPT, "    cmd = [",
                                     '    backend = "arm"\n    cmd = [')),
         "'rv32': L1 ladder criterion NOT MET", rv_l1(ladder_rung="riscv"))
    case("ladder: `backend` is a module GLOBAL, not run_synth's parameter",
         lambda t: (lad_rv(t),
                    _edit(t, LADDER_SCRIPT, "def run_synth(synth, module, backend,",
                          'backend = "arm"\ndef run_synth(synth, module, target,')),
         "'rv32': L1 ladder criterion NOT MET", rv_l1(ladder_rung="riscv"))
    case("a rung named for ANOTHER backend does not measure this one",
         lad_rv, "'cortex-m-thumb2': L1 ladder criterion NOT MET",
         lambda led: (led["backends"][0].pop("open"),
                      led["backends"][0].update(ladder_rung="riscv")))
    # --- RQ-92-WDGTHIN: a Rust kiln oracle as an L2 differential ---------------
    M0 = RUST_ORACLE_DIR + "m0_oracle.rs"
    WF = ".github/workflows/oracle.yml"
    GREP = "          grep -qx 'ORACLE m0-diff: 7 cases agree' log\n"
    case("Rust oracle: its exact result line is no longer grepped",
         lambda t: _edit(t, WF, GREP, ""), "m0_oracle.rs is not WIRED")
    case("Rust oracle: the grep is commented out",
         lambda t: _edit(t, WF, GREP, "          # " + GREP.lstrip()),
         "m0_oracle.rs is not WIRED")
    case("Rust oracle: the step greps ANOTHER oracle file's line",
         lambda t: _edit(t, WF, "ORACLE m0-diff: 7", "ORACLE m3-diff: 7"),
         "m0_oracle.rs is not WIRED")
    case("Rust oracle: the crate is run without `--features exec`",
         lambda t: _edit(t, WF, " --features exec", ""), "m0_oracle.rs is not WIRED")
    case("Rust oracle: the step filters to another `--test` file",
         lambda t: _edit(t, WF, "--features exec --", "--features exec --test m3_oracle --"),
         "m0_oracle.rs is not WIRED")
    case("Rust oracle: a `--test` filter that selects it stays GREEN",
         lambda t: _edit(t, WF, "--features exec --", "--features exec --test m0_oracle --"),
         None)
    case("Rust oracle: its tag is also printed by another oracle file",
         lambda t: _edit(t, RUST_ORACLE_DIR + "m3_oracle.rs", "m3-diff", "m0-diff"),
         "prints no `ORACLE <tag>:` result line of its own")
    case("Rust oracle: emulates on ANOTHER core's model",
         lambda t: _edit(t, M0, "run_case(&obj, Cpu::CortexM0)", "run_case(&obj, Cpu::CortexM3)"),
         "never executes on this backend's emulator model")
    case("Rust oracle: the emulator model is named in a comment only",
         lambda t: _edit(t, M0, "run_case(&obj, Cpu::CortexM0)",
                         "run_case(&obj, Cpu::CortexM3) // Cpu::CortexM0"),
         "never executes on this backend's emulator model")
    case("Rust oracle: compiles for ANOTHER target",
         lambda t: _edit(t, M0, 'compile_probes("cortex-m0")', 'compile_probes("cortex-m3")'),
         "never compiles for this backend")
    case("Rust oracle: no judged comparison (run_case only in a comment)",
         lambda t: _edit(t, M0, "let c = run_case(&obj, Cpu::CortexM0);",
                         "let c = emu(&obj, Cpu::CortexM0); // run_case(&obj)"),
         "is not a kiln-vs-unicorn execution differential")
    # Cold review F2: the reviewer's two hollow variants, and their kin.
    RUN = "    let c = run_case(&obj, Cpu::CortexM0);\n"
    PRINT = '    eprintln!("ORACLE m0-diff: {} cases agree", c);\n'
    case("HOLLOW (review variant 1): the comparison is inside `if false`",
         lambda t: _edit(t, M0, RUN, "    let c = 7;\n    if false {\n    " + RUN + "    }\n"),
         "HOLLOW differential: every `run_case`")
    case("HOLLOW (review variant 2): the comparison is in an #[ignore]d test, "
         "the line printed by a trivial one",
         lambda t: _edit(t, M0, "#[test]\nfn agree() {\n" + '    let obj = compile_probes("cortex-m0");\n' + RUN + PRINT + "}\n",
                         '#[test]\n#[ignore = "slow"]\nfn agree() {\n'
                         '    let obj = compile_probes("cortex-m0");\n' + RUN + "}\n"
                         "#[test]\nfn line() {\n    let c = 7;\n" + PRINT + "}\n"),
         "HOLLOW differential: every `run_case`")
    case("HOLLOW: the comparison is in a #[cfg]-gated test",
         lambda t: _edit(t, M0, "#[test]\nfn agree()", '#[cfg(feature = "never")]\n#[test]\nfn agree()'),
         "HOLLOW differential: every `run_case`")
    case("HOLLOW: the comparison is inside `if cfg!(..)`",
         lambda t: _edit(t, M0, RUN, "    let c = 7;\n    if cfg!(feature = \"never\") {\n    " + RUN + "    }\n"),
         "HOLLOW differential: every `run_case`")
    case("HOLLOW: the comparison runs, the pinned line is printed only by an #[ignore]d test",
         lambda t: _edit(t, M0, PRINT + "}\n",
                         "    let _ = c;\n}\n#[test]\n#[ignore]\nfn line() {\n    let c = 7;\n" + PRINT + "}\n"),
         "it prints its `ORACLE <tag>:` result line only from a block that does not run")
    case("not hollow: `if false` around something ELSE, the comparison in its `else`",
         lambda t: _edit(t, M0, RUN, "    let c = if false { 7 } else {\n    " + RUN.replace("let c = ", "").replace(";\n", "\n") + "    };\n"),
         None)
    case("Rust oracle: not gated on the exec feature",
         lambda t: _edit(t, M0, '#![cfg(feature = "exec")]\n', ""),
         "is not gated on")
    case("Rust file outside the oracle crate cited as a differential",
         None, "is a Rust file outside",
         lambda led: led["backends"][3].update(differentials=["crates/c/tests/m0_decl.rs"]))
    case("BORROWED Rust oracle: RV32 cites the ARMv6-M oracle",
         lambda t: _edit(t, DOC, "rv_diff.py; rv_decl.rs", "rv_diff.py; m0_oracle.rs; rv_decl.rs"),
         "'rv32': crates/synth-oracle/tests/m0_oracle.rs never compiles for this backend",
         lambda led: led["backends"][1]["differentials"].append(M0))
    case("promotion by assertion: ARMv6-M L2 with no differential",
         None, "needs >=1 execution differential",
         lambda led: led["backends"][3].update(differentials=[]))
    case("ARMv6-M declared L1: no Rocq ISA model, so no proof can be bound",
         lambda t: _edit(t, DOC, "| M0 | L2 execution-tested |", "| M0 | L1 verified |"),
         "'cortex-m0-armv6m': L1 needs Rocq proofs",
         lambda led: led["backends"][3].update(level="L1"))
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
