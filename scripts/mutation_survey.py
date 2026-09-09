#!/usr/bin/env python3
"""mutation_survey — what share of synth's emitted-code DECISIONS would an
oracle catch being wrong? Measured by mutation (RQ-65-MUTANTS, #1189).

THE QUESTION (v0.65). #1189 was a silent miscompile that survived every oracle
because the then-arm was correct BY ACCIDENT. synth has ~19,740 selector lines,
~190 repro scripts, 61 CI jobs and 645 Qed, and until this survey nobody had
measured what fraction of the code generator's decisions that apparatus would
notice being wrong. This harness flips one decision at a time, rebuilds, and
asks the oracles.

THE METHOD — cost-shaped, because every mutant is a build.

  1. SAMPLING FRAME (stated, never invented per run): five regions the
     RQ-65-PARITY oracle (#197, PR #1216) ranked by where the two shipped
     selectors disagree, located by FUNCTION ANCHOR (not line number, so the
     frame survives unrelated edits):
       R1 routing   arm_backend.rs   has_value_carrying_branch + compile_wasm_to_arm
                                     (the optimized-vs-direct gate, its predicates,
                                     the select_direct retry ladder)
       R2 ir_to_arm optimizer_bridge  ir_to_arm_impl + fold_mem_offset +
                                     push_software_bounds_guard
       R3 direct    select_with_stack the hand-written operand plumbing around the
                                     Rocq-proved sel_dsl rules
       R4 shared    the post-merge tail BOTH paths flow through — arm_backend.rs
                    finish_allocated_stream / classify_arm_branch /
                    resolve_label_branches / validate_branch_targets, the
                    liveness.rs passes (dead-frame, callee-saved, cmp-select
                    fusion), and the encoder's i64_effective_base
       R5 startup   generate_minimal_startup — the R9/R10/R11 register contract
     The inventory behind R4 (measured, not assumed): the two selectors share
     NO lowering code inside synth-synthesis; `sel_dsl` has zero call sites in
     optimizer_bridge.rs. What they share is downstream of the merge point.

  2. OPERATORS — mechanical, regex-applied, one site per mutant, the exact
     text diff recorded in the ledger:
       REG      Reg::Rn            -> Reg::R((n+1) mod 13)
       COND     Condition::X       -> its inverse (EQ<->NE, LT<->GE, LE<->GT,
                                      LO<->HS, LS<->HI)
       DROPMOV  a `push(... ArmOp::Mov ...)` statement -> deleted
       IMM      Operand2::Imm(e)   -> Imm((e).wrapping_add(1));
                MemAddr::imm(b, o) -> imm(b, (o).wrapping_add(4));
                imm16: e           -> (e).wrapping_add(1);
                encode_thumb2_mov{w,t}(n, ..) -> register (n+1) mod 13
       GUARD    `if COND {`        -> `if !(COND) {`;  a `|| term` / `&& term`
                continuation line  -> negated term
       BOUND    ` < ` <-> ` <= `, ` > ` <-> ` >= `;  `.len() - 1` -> `.len()`
     Sites are enumerated deterministically (sorted by file, line, column) and
     sampled with a SEEDED RNG, stratified per region and per operator. A
     mutant rustc rejects is UNCOMPILABLE — excluded from every denominator
     (stillborn), and the next sample in seed order takes its place.

  3. TRIAGE BY EMITTED BYTES before spending an oracle run. The corpus —
     every scripts/repro/*.wat and *.wasm, three ARM configurations
     (`--relocatable`, self-contained default, self-contained `--no-optimize`)
     — is compiled once with the unmutated binary and hashed per module
     (.text/.data/.rodata bytes + symtab names/values/sizes). Each mutant
     recompiles it (~10 s) and diffs the hashes.
       identical everywhere -> EQUIVALENT or DEAD, told apart by a REACH
         PROBE: the ORIGINAL token is rebuilt wrapped in
         `{ eprintln!(MARK); token }`; the corpus compile is re-run; the
         marker on stderr means the decision was EVALUATED (EQUIVALENT for
         this corpus), no marker means it never ran (DEAD for this corpus —
         a deletion CANDIDATE, not a proof of unreachability). A probe rustc
         rejects (pattern position, const context) is UNRESOLVED.
         No oracle is run for these; that is where the affordability lives.
       changed anywhere    -> the bounded oracle suite runs.

  4. THE BOUNDED ORACLE SUITE is DERIVED FROM .github/workflows/ci.yml, not
     hand-listed ("derive what you check against from the artifact you
     ship"):
       L1 execution  every `run:` step of every ARM oracle job (a job whose
                     steps reference scripts/repro/), executed verbatim with
                     `bash -eo pipefail`, the binary path substituted, minus
                     install/ledger/tree-mutating steps and the RV32/AArch64
                     jobs (separate backend crates the frame cannot reach).
                     Steps red on the UNMUTATED binary are excluded and
                     listed. Runs fastest-first (baseline timing), stops at
                     the first red: KILLED / execution.
       L2 structure  the `test` job's cargo commands (the workspace unit and
                     integration tests, frozen-byte goldens included), run
                     only when L1 is green: red -> KILLED / structure (a
                     kill by frozen-byte tests ALONE is sub-classified
                     `freeze-only` — a change detector, not a wrongness
                     detector). Green -> SURVIVED: classification UNTESTED.
     Lints are not oracles: mutants build without -Dwarnings.

  5. RED-FIRST CONTROLS. Mutants KNOWN to be caught (the #1189 aliasing copy
     disabled; the select operand order swapped) run through the same
     pipeline and MUST come back KILLED, or the survey reports nothing and
     says so (exit 1 on a control that survives).

  6. THE CI PIN is the harness's DISCRIMINATION, not a re-run of the survey:
     `--ci` replays a small fixed subset from the ledger — known-KILLED
     controls (their recorded killer step must go red), known-SURVIVED,
     known-EQUIVALENT and known-DEAD cases (their recorded byte-triage and
     reach verdicts must reproduce exactly) — and fails on any disagreement
     in either direction. The published survival numbers are pinned in
     claims.yaml against the committed ledger (docs/status/mutation_survey.json).

WHAT THE NUMBER SUPPORTS. "Survival rate" = UNTESTED / (byte-changing
compilable mutants), for THIS frame, THIS corpus, THIS suite, at the recorded
commit. It is not a property of the whole selector, not exhaustive, and not
stable under a different seed — the ledger records seed, frame and suite so a
re-run is a comparison, not a new claim.

Usage:
  python3 scripts/mutation_survey.py sites                 # candidate counts
  python3 scripts/mutation_survey.py sample [--seed N] [--per-region N]
  python3 scripts/mutation_survey.py baseline              # corpus hashes + suite timing
  python3 scripts/mutation_survey.py run [--per-region N] [--only ID,ID]
  python3 scripts/mutation_survey.py controls              # red-first controls
  python3 scripts/mutation_survey.py ci                    # replay the pinned subset
  python3 scripts/mutation_survey.py reach [--write]       # RQ-66-DELETE: DEAD sites under REACH_CFGS
  python3 scripts/mutation_survey.py report                # markdown tables
Env: CARGO_TARGET_DIR (default target/), SYNTH_MUTANTS_LEDGER (default
docs/status/mutation_survey.json).
"""

import argparse
import datetime as _dt
import glob
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("mutation_survey: needs PyYAML (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MARK = "SYNTH-MUTANT-REACHED"
CI_YML = ROOT / ".github/workflows/ci.yml"
DEFAULT_LEDGER = ROOT / "docs/status/mutation_survey.json"
TARGET_DIR = Path(os.environ.get("CARGO_TARGET_DIR") or (ROOT / "target")).resolve()
BIN = TARGET_DIR / "debug" / "synth"

# ---------------------------------------------------------------------------
# The frame: five regions, located by function anchor.
# ---------------------------------------------------------------------------
REGIONS = {
    "R1-routing": [
        ("crates/synth-backend/src/arm_backend.rs", "fn", "has_value_carrying_branch"),
        ("crates/synth-backend/src/arm_backend.rs", "fn", "compile_wasm_to_arm"),
    ],
    "R2-ir_to_arm": [
        ("crates/synth-synthesis/src/optimizer_bridge.rs", "fn", "fold_mem_offset"),
        ("crates/synth-synthesis/src/optimizer_bridge.rs", "fn", "push_software_bounds_guard"),
        ("crates/synth-synthesis/src/optimizer_bridge.rs", "fn", "ir_to_arm_impl"),
    ],
    "R3-direct": [
        (
            "crates/synth-synthesis/src/instruction_selector/select_with_stack.rs",
            "fn",
            "select_with_stack",
        ),
    ],
    "R4-shared": [
        ("crates/synth-backend/src/arm_backend.rs", "fn", "finish_allocated_stream"),
        ("crates/synth-backend/src/arm_backend.rs", "fn", "classify_arm_branch"),
        ("crates/synth-backend/src/arm_backend.rs", "fn", "resolve_label_branches"),
        ("crates/synth-backend/src/arm_backend.rs", "fn", "validate_branch_targets"),
        ("crates/synth-synthesis/src/liveness.rs", "before-tests", None),
        ("crates/synth-backend/src/arm_encoder.rs", "fn", "i64_effective_base"),
    ],
    "R5-startup": [
        ("crates/synth-cli/src/main.rs", "fn", "generate_minimal_startup"),
    ],
}

OPS = ("REG", "COND", "DROPMOV", "IMM", "GUARD", "BOUND")

COND_INVERSE = {
    "EQ": "NE", "NE": "EQ", "LT": "GE", "GE": "LT", "LE": "GT", "GT": "LE",
    "LO": "HS", "HS": "LO", "LS": "HI", "HI": "LS",
}

# Jobs the frame cannot reach (separate backend crates / other hosts) or that
# rebuild the tree themselves, and steps that install, ledger, or diff.
EXCLUDE_JOB_RE = re.compile(
    r"^(rv32-|aarch64|arm64-linux|macho-host|instrument-independence|mcdc|"
    r"repro-sweep-rv32|vcr-ra-003-rv32|vcr-sel-005|claim-check$|rivet$)"
)
ORACLE_INVOCATION_RE = re.compile(
    r"oracle_run\.py|python3? scripts/repro/\S+\.py|bash scripts/repro/\S+\.sh"
)
EXCLUDE_STEP_RE = re.compile(
    r"apt-get|pip install|brew install|gh release download|oracle_evidence\.py|"
    r"git diff|target-275probe|EXPORTS_ONLY_275|witness|actions/"
)

CORPUS_CFGS = {
    "reloc": ["--all-exports", "--relocatable", "--target", "cortex-m4"],
    "self": ["--all-exports", "--target", "cortex-m4"],
    "self-noopt": ["--all-exports", "--target", "cortex-m4", "--no-optimize"],
}

# RQ-66-DELETE (#242): configurations the survey's corpus does NOT compile.
# v0.65 classified four sites DEAD ("never evaluated during the corpus
# compiles") and v0.66 set out to delete them under the byte-identity gate.
# Every one of them is REACHED here. Three are the GI-FPU-002 VFP retry ladder
# in `compile_wasm_to_arm` (#881 / #1069), which only a HARD-FLOAT target can
# enter — CORPUS_CFGS compiles `cortex-m4` (no FPU) and nothing else, while the
# two fixtures written to exercise that ladder (`vfp_spill_881.wat`,
# `vfp_local_pressure_1069.wat`) sit IN the corpus and are compiled by their
# own CI oracles on `cortex-m7dp`. The fourth is the graph-colouring arbiter's
# literal-pool sizing, behind the flag-off `SYNTH_GRAPH_ALLOC` spike that the
# `vcr_dec_001_graph_alloc_differential` job turns on. So "DEAD" was a property
# of the corpus CONFIGURATION, not of the code — an honest verdict for the
# frame the ledger states, and a wrong deletion list.
#
# These run in the `reach` subcommand and, for `ci_subset` entries carrying
# `want_reach_wide`, in `ci`: every pinned witness module must still print the
# marker under its configuration. A site that stops being reached is red (the
# code became unreachable, or the probe went blind — either needs a human), and
# a deletion removes the site and is red the same way. They are deliberately
# NOT added to CORPUS_CFGS: the byte-triage baseline and every `changed` set in
# the ledger are relative to CORPUS_CFGS, and widening that is a re-survey.
# name -> (synth flags, extra environment)
REACH_CFGS = {
    # falcon's exact flags — what the #881 / #1069 execution oracles compile
    "m7dp-reloc": (["--all-exports", "--relocatable", "--target", "cortex-m7dp"], {}),
    "m7dp-self": (["--all-exports", "--target", "cortex-m7dp"], {}),
    # the VCR-DEC-001 spike, flag-on (the vcr_dec_001 differential's setting)
    "graph-alloc-reloc": (
        ["--all-exports", "--relocatable", "--target", "cortex-m4"],
        {"SYNTH_GRAPH_ALLOC": "1"},
    ),
    "graph-alloc-self": (["--all-exports", "--target", "cortex-m4"], {"SYNTH_GRAPH_ALLOC": "1"}),
}

# Seconds per corpus compile. The unmutated compiler needs ~17 ms per module
# (600 pairs in 10 s), so 60 s is >3000x headroom; a mutant that hangs the
# compiler on MANY modules (the 38th draw of the v0.65 survey hung on dozens)
# is stopped at the FIRST hang — the verdict is already KILLED/timeout and the
# remaining corpus would only add hours of identical evidence.
COMPILE_TIMEOUT = int(os.environ.get("SYNTH_MUTANTS_COMPILE_TIMEOUT", "60"))

FREEZE_TEST_BINARIES = {
    "frozen_codegen_bytes", "base_cse_flip_468", "const_cse_reduction_242",
    "flag_flip_wave_242", "rv32_cmp_select_flip_472", "rv32_local_promo_flip_472",
}


def log(msg):
    print(f"[mutants {time.strftime('%H:%M:%S')}] {msg}", flush=True)


# ---------------------------------------------------------------------------
# Region location
# ---------------------------------------------------------------------------
def fn_range(lines, name):
    """1-based inclusive (start, end) of `fn name` — end is the closing brace
    at the fn's own indentation (rustfmt guarantees it)."""
    pat = re.compile(rf"^(\s*)(?:pub(?:\([a-z]+\))?\s+)?fn\s+{re.escape(name)}\b")
    for i, line in enumerate(lines):
        m = pat.match(line)
        if not m:
            continue
        indent = m.group(1)
        for j in range(i + 1, len(lines)):
            if lines[j].rstrip("\n") == indent + "}":
                return (i + 1, j + 1)
        raise RuntimeError(f"unterminated fn {name}")
    raise KeyError(f"fn {name} not found")


def region_spans(region):
    """[(relpath, start, end)] for the region, resolved on the live tree."""
    spans = []
    for rel, kind, name in REGIONS[region]:
        lines = (ROOT / rel).read_text().splitlines()
        if kind == "fn":
            s, e = fn_range(lines, name)
        elif kind == "before-tests":
            s = 1
            e = next(
                (i for i, l in enumerate(lines) if l.startswith("#[cfg(test)]")),
                len(lines),
            )
        else:
            raise ValueError(kind)
        spans.append((rel, s, e))
    return spans


# ---------------------------------------------------------------------------
# Operators: each yields sites as dicts with the exact multi-line edit.
#   {id, region, op, file, start, end, before, after, probe}
# `before` is the original text of lines start..end (joined with \n, no
# trailing newline); `after` the mutated text; `probe` the reach-probed text
# (original semantics + a marker print), or None when no probe shape exists.
# ---------------------------------------------------------------------------
def _is_comment(line):
    return line.lstrip().startswith("//")


def _wrap(tok):
    return f'{{ eprintln!("{MARK}"); {tok} }}'


def _in_string(line, pos):
    """Crude but sufficient: an odd number of quotes before `pos` means the
    match sits inside a string literal (a format-string `<` is not code)."""
    return line[:pos].count('"') % 2 == 1


def _single_line_sites(op, lines, rel, s, e, pattern, mutate, probe, skip=None):
    out = []
    for ln in range(s, e + 1):
        line = lines[ln - 1]
        if _is_comment(line) or (skip and skip(line)):
            continue
        for k, m in enumerate(pattern.finditer(line)):
            if _in_string(line, m.start()):
                continue
            mut = mutate(m)
            if mut is None:
                continue
            after = line[: m.start()] + mut + line[m.end():]
            pr = probe(m)
            probed = (line[: m.start()] + pr + line[m.end():]) if pr else None
            out.append(
                {
                    "op": op,
                    "file": rel,
                    "start": ln,
                    "end": ln,
                    "col": m.start(),
                    "before": line,
                    "after": after,
                    "probe": probed,
                }
            )
    return out


def op_reg(lines, rel, s, e):
    pat = re.compile(r"\bReg::R(\d{1,2})\b")

    def mut(m):
        n = int(m.group(1))
        return f"Reg::R{(n + 1) % 13}"

    return _single_line_sites(
        "REG", lines, rel, s, e, pat, mut, lambda m: _wrap(m.group(0)),
        skip=lambda l: l.lstrip().startswith("use "),
    )


def op_cond(lines, rel, s, e):
    pat = re.compile(r"\bCondition::(EQ|NE|LT|LE|GT|GE|LO|LS|HI|HS)\b")
    return _single_line_sites(
        "COND", lines, rel, s, e, pat,
        lambda m: f"Condition::{COND_INVERSE[m.group(1)]}",
        lambda m: _wrap(m.group(0)),
    )


def op_imm(lines, rel, s, e):
    out = []
    pat_skip = lambda l: (" => " in l or l.rstrip().endswith("=>") or "if let " in l
                          or "let Operand2" in l or l.lstrip().startswith("|"))
    imm = re.compile(r"Operand2::Imm\(((?:[^()]|\([^()]*\))+)\)")
    out += _single_line_sites(
        "IMM", lines, rel, s, e, imm,
        lambda m: f"Operand2::Imm(({m.group(1)}).wrapping_add(1))",
        lambda m: f"Operand2::Imm({_wrap(m.group(1))})",
        skip=pat_skip,
    )
    mem = re.compile(r"MemAddr::imm\(([^,()]+), ((?:[^()]|\([^()]*\))+)\)")
    out += _single_line_sites(
        "IMM", lines, rel, s, e, mem,
        lambda m: f"MemAddr::imm({m.group(1)}, ({m.group(2)}).wrapping_add(4))",
        lambda m: f"MemAddr::imm({m.group(1)}, {_wrap(m.group(2))})",
        skip=pat_skip,
    )
    imm16 = re.compile(r"imm16: ([^,}]+?)(?=[,}]|$)")
    out += _single_line_sites(
        "IMM", lines, rel, s, e, imm16,
        lambda m: f"imm16: ({m.group(1)}).wrapping_add(1)",
        lambda m: f"imm16: {_wrap(m.group(1))}",
        skip=pat_skip,
    )
    movwt = re.compile(r"encode_thumb2_mov([wt])\((\d+),")
    out += _single_line_sites(
        "IMM", lines, rel, s, e, movwt,
        lambda m: f"encode_thumb2_mov{m.group(1)}({(int(m.group(2)) + 1) % 13},",
        lambda m: f"encode_thumb2_mov{m.group(1)}({_wrap(m.group(2))},",
    )
    return out


def op_guard(lines, rel, s, e):
    out = []
    ifpat = re.compile(r"^(\s*)((?:\} )?else if |if )(?!let )(.+?) \{\s*$")
    out += _single_line_sites(
        "GUARD", lines, rel, s, e, ifpat,
        lambda m: f"{m.group(1)}{m.group(2)}!({m.group(3)}) {{",
        lambda m: f"{m.group(1)}{m.group(2)}{_wrap(m.group(3))} {{",
    )
    # A `|| term` / `&& term` continuation line is a site only when the term
    # is COMPLETE on that line: balanced parens, no closure opener, and the
    # next line does not continue a method chain (`.foo()`).
    cont = re.compile(r"^(\s*)(\|\||&&) (?!let )([^{]+?)(\s*\{)?\s*$")
    for ln in range(s, e + 1):
        line = lines[ln - 1]
        if _is_comment(line):
            continue
        m = cont.match(line)
        if not m:
            continue
        term = m.group(3)
        nxt = lines[ln].lstrip() if ln < len(lines) else ""
        if (term.count("(") != term.count(")") or term.count("[") != term.count("]")
                or re.search(r"\|[^|]*\|\s*$", term) or nxt.startswith((".", "?"))):
            continue
        tail = m.group(4) or ""
        out.append(
            {"op": "GUARD", "file": rel, "start": ln, "end": ln, "col": m.start(2),
             "before": line, "after": f"{m.group(1)}{m.group(2)} !({term}){tail}",
             "probe": f"{m.group(1)}{m.group(2)} {_wrap(term)}{tail}"}
        )
    return out


def op_bound(lines, rel, s, e):
    out = []
    rel_pat = re.compile(r"(?<=[\w)\]] )(<=|>=|<|>)(?= [\w(&*!\-'\"])")
    flip = {"<": "<=", "<=": "<", ">": ">=", ">=": ">"}
    lhs_pat = re.compile(r"[\w.:()\[\]*&!?]+ $")

    def probe(m):
        # wrap the operand immediately left of the operator
        line = m.string
        left = line[: m.start()]
        lm = lhs_pat.search(left)
        if not lm:
            return None
        tok = lm.group(0)[:-1]
        return None if not tok else "__LHS__"

    for ln in range(s, e + 1):
        line = lines[ln - 1]
        if _is_comment(line) or "->" in line and " if " not in line and not line.lstrip().startswith(("if ", "while ", "let ", "||", "&&")):
            continue
        for m in rel_pat.finditer(line):
            if _in_string(line, m.start()):
                continue
            after = line[: m.start()] + flip[m.group(1)] + line[m.end():]
            left = line[: m.start()]
            lm = lhs_pat.search(left)
            probed = None
            if lm and lm.group(0)[:-1]:
                tok = lm.group(0)[:-1]
                probed = left[: lm.start()] + f"({_wrap(tok)}) " + line[m.start():]
            out.append(
                {"op": "BOUND", "file": rel, "start": ln, "end": ln, "col": m.start(),
                 "before": line, "after": after, "probe": probed}
            )
    len1 = re.compile(r"\.len\(\) - 1\b")
    out += _single_line_sites(
        "BOUND", lines, rel, s, e, len1,
        lambda m: ".len()",
        lambda m: f".len() - {_wrap('1')}",
    )
    return out


def op_dropmov(lines, rel, s, e):
    out = []
    head = re.compile(r"^\s*\w+\.push\((ArmInstruction \{|ArmOp::Mov \{)")
    for ln in range(s, e + 1):
        line = lines[ln - 1]
        if _is_comment(line):
            continue
        m = head.match(line)
        if not m:
            continue
        if m.group(1).startswith("ArmInstruction"):
            nxt = lines[ln] if ln < len(lines) else ""
            if "op: ArmOp::Mov {" not in nxt and "ArmOp::Mov {" not in line:
                continue
        depth = 0
        end = None
        for j in range(ln - 1, min(len(lines), ln + 40)):
            for ch in lines[j]:
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
            if depth == 0 and lines[j].rstrip().endswith(");"):
                end = j + 1
                break
        if end is None:
            continue
        block = "\n".join(lines[ln - 1:end])
        indent = re.match(r"^\s*", line).group(0)
        out.append(
            {"op": "DROPMOV", "file": rel, "start": ln, "end": end, "col": 0,
             "before": block, "after": f"{indent}/* MUTANT: Mov dropped */ ();",
             "probe": f'{indent}eprintln!("{MARK}");\n{block}'}
        )
    return out


OP_FNS = {
    "REG": op_reg, "COND": op_cond, "DROPMOV": op_dropmov,
    "IMM": op_imm, "GUARD": op_guard, "BOUND": op_bound,
}


def enumerate_sites():
    """All candidate sites, deterministic order, ids assigned."""
    sites = {}
    for region in REGIONS:
        for rel, s, e in region_spans(region):
            lines = (ROOT / rel).read_text().splitlines()
            for op in OPS:
                for site in OP_FNS[op](lines, rel, s, e):
                    site["region"] = region
                    sid = f"{region}/{op}/{Path(rel).name}:{site['start']}:{site['col']}"
                    site["id"] = sid
                    if sid in sites and sites[sid]["after"] != site["after"]:
                        # two patterns on one column: keep first, deterministic
                        continue
                    sites[sid] = site
    return sites


def sample_sites(sites, seed, per_region, oversample):
    """Stratified per region, then per operator, seeded; returns an ordered
    list of `per_region * oversample` candidates per region."""
    rng = random.Random(seed)
    per_region_order = {}
    for region in REGIONS:
        pools = {op: sorted((s for s in sites.values() if s["region"] == region and s["op"] == op),
                            key=lambda s: (s["file"], s["start"], s["col"]))
                 for op in OPS}
        order = []
        for _ in range(per_region * oversample):
            avail = [op for op in OPS if pools[op]]
            if not avail:
                break
            op = rng.choice(avail)
            pick = rng.randrange(len(pools[op]))
            order.append(pools[op].pop(pick))
        per_region_order[region] = order
    # Round-robin across regions so ANY time-boxed prefix of the run is
    # balanced — a survey cut short still covers all five regions.
    merged = []
    for i in range(per_region * oversample):
        for region in REGIONS:
            if i < len(per_region_order[region]):
                merged.append(per_region_order[region][i])
    return merged


# ---------------------------------------------------------------------------
# Applying and restoring edits
# ---------------------------------------------------------------------------
class Edit:
    def __init__(self, site, text_key):
        self.site = site
        self.path = ROOT / site["file"]
        self.original = None
        self.text = site[text_key]

    def __enter__(self):
        self.original = self.path.read_text()
        lines = self.original.split("\n")
        s, e = self.site["start"], self.site["end"]
        have = "\n".join(lines[s - 1:e])
        if have != self.site["before"]:
            raise RuntimeError(f"site drifted: {self.site['id']}\n--have--\n{have}\n--want--\n{self.site['before']}")
        lines[s - 1:e] = self.text.split("\n")
        self.path.write_text("\n".join(lines))
        return self

    def __exit__(self, *exc):
        self.path.write_text(self.original)
        return False


def git_clean(rel):
    r = subprocess.run(["git", "diff", "--quiet", "--", rel], cwd=ROOT)
    return r.returncode == 0


# ---------------------------------------------------------------------------
# Build, corpus triage, reach probe
# ---------------------------------------------------------------------------
def cargo_env(extra=None):
    env = dict(os.environ)
    env["CARGO_TARGET_DIR"] = str(TARGET_DIR)
    env.pop("RUSTFLAGS", None)  # lints are not oracles
    if extra:
        env.update(extra)
    return env


def build_synth():
    t0 = time.time()
    r = subprocess.run(
        ["cargo", "build", "-p", "synth-cli"],
        cwd=ROOT, env=cargo_env(), capture_output=True, text=True,
    )
    dt = time.time() - t0
    if r.returncode != 0:
        err = next((l for l in r.stderr.splitlines() if l.startswith("error")), r.stderr[-300:])
        return False, err, dt
    return True, "", dt


def ensure_symlink():
    """Scripts default to ./target/debug/synth; when the lane builds elsewhere
    point that path at the live binary so no step can pick up a stale one."""
    default = ROOT / "target" / "debug" / "synth"
    if BIN == default.resolve():
        return
    default.parent.mkdir(parents=True, exist_ok=True)
    if default.is_symlink() or default.exists():
        default.unlink()
    default.symlink_to(BIN)


def corpus_modules():
    return sorted(glob.glob(str(ROOT / "scripts/repro/*.wat")) + glob.glob(str(ROOT / "scripts/repro/*.wasm")))


def digest_elf(path):
    from elftools.elf.elffile import ELFFile

    h = hashlib.sha256()
    with open(path, "rb") as f:
        elf = ELFFile(f)
        for name in (".text", ".data", ".rodata"):
            sec = elf.get_section_by_name(name)
            if sec is not None:
                h.update(name.encode())
                h.update(sec.data())
        sym = elf.get_section_by_name(".symtab")
        if sym is not None:
            for s in sym.iter_symbols():
                h.update(f"{s.name}:{s['st_value']}:{s['st_size']}".encode())
    return h.hexdigest()[:16]


def compile_corpus(outdir, capture_marker=False, cfgs=None, env=None, reached_out=None):
    """{(module, cfg): digest | 'DECLINE'} plus whether MARK appeared.

    `cfgs` (default CORPUS_CFGS) and `env` (extra environment variables) let
    the reach probe run configurations the corpus does not (REACH_CFGS);
    `reached_out`, when a set, collects every `module|cfg` key whose compile
    printed the marker, so a verdict can name its witnesses."""
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    cfgs = CORPUS_CFGS if cfgs is None else cfgs
    run_env = None
    if env:
        run_env = dict(os.environ)
        run_env.update(env)
    result = {}
    reached = False
    for mod in corpus_modules():
        if any(v == "TIMEOUT" for v in result.values()):
            result["__triage__"] = "aborted-after-first-compiler-hang"
            break
        for cfg, flags in cfgs.items():
            o = outdir / f"{Path(mod).name}.{cfg}.elf"
            if o.exists():
                o.unlink()
            key = f"{Path(mod).name}|{cfg}"
            try:
                r = subprocess.run(
                    [str(BIN), "compile", mod, *flags, "-o", str(o)],
                    capture_output=True, text=True, timeout=COMPILE_TIMEOUT, cwd=ROOT, env=run_env,
                )
            except subprocess.TimeoutExpired as ex:
                # A mutant that makes the COMPILER hang is a behaviour change
                # every CI job would catch by its own timeout — loudly. It is
                # recorded as such, never dropped (it crashed the first run).
                if capture_marker and MARK in (ex.stderr or b"").decode(errors="ignore"):
                    reached = True
                    if reached_out is not None:
                        reached_out.add(key)
                result[key] = "TIMEOUT"
                continue
            if capture_marker and MARK in r.stderr:
                reached = True
                if reached_out is not None:
                    reached_out.add(key)
            if r.returncode == 0 and o.exists():
                result[key] = digest_elf(o)
            else:
                result[key] = "DECLINE"
    return result, reached


def diff_corpus(base, mut):
    changed = []
    for key in sorted(base):
        if key not in mut:
            continue  # never compiled: the triage short-circuited after a hang
        b, m = base[key], mut[key]
        if b == m:
            continue
        if m == "TIMEOUT":
            kind = "compile-timeout"
        elif b == "DECLINE":
            kind = "newly-accepted"
        elif m == "DECLINE":
            kind = "newly-declined"
        else:
            kind = "bytes"
        changed.append({"module": key, "kind": kind})
    return changed


# ---------------------------------------------------------------------------
# The oracle suite, derived from ci.yml
# ---------------------------------------------------------------------------
def _subst(text):
    text = text.replace("${{ github.workspace }}/target/debug/synth", str(BIN))
    text = text.replace("${{ github.workspace }}", str(ROOT))
    text = re.sub(r"(?<![\w/.\-])(?:\./)?target/debug/synth\b", str(BIN), text)
    if shutil.which("python") is None:
        text = re.sub(r"(?<![\w/])python(?=\s)", "python3", text)
    return text


def derive_suite(jobs=None):
    """Derive the suite from ci.yml. `jobs` (a list of job ids) restricts L1
    to a NAMED subset — the published rate is then relative to exactly those
    jobs, and the ledger records the name list and the jobs it left out. A
    broader suite can only move survival DOWN (an oracle cannot un-kill a
    mutant), so a subset rate is an UPPER bound on survival."""
    wf = yaml.safe_load(CI_YML.read_text())
    wf_env = {k: str(v) for k, v in (wf.get("env") or {}).items()}
    l1, excluded_jobs, excluded_steps, unselected_jobs = [], [], [], []
    for jid, job in wf["jobs"].items():
        steps = job.get("steps") or []
        # POSITIVE rule: a job is an oracle job when a step INVOKES an oracle
        # (the driver, or a repro script as a command). "Mentions the
        # directory" was tried first and admitted `coverage` (an echo of a
        # comment) and `claim-check` (the wiring gate's argument) — a job that
        # rebuilds the whole workspace instrumented is not an oracle.
        refs_repro = any(ORACLE_INVOCATION_RE.search(str(s.get("run", ""))) for s in steps)
        if not refs_repro:
            continue
        if EXCLUDE_JOB_RE.search(jid):
            excluded_jobs.append({"job": jid, "reason": "out of frame: other backend / other host / rebuilds the tree / documentation gate, not an execution oracle"})
            continue
        if jobs is not None and jid not in jobs:
            unselected_jobs.append(jid)
            continue
        env = dict(wf_env)
        env.update({k: str(v) for k, v in (job.get("env") or {}).items()})
        for k, s in enumerate(steps):
            run = s.get("run")
            if not run:
                continue
            name = s.get("name") or f"step-{k}"
            if EXCLUDE_STEP_RE.search(run):
                excluded_steps.append({"job": jid, "step": name, "reason": "install / ledger / diff / probe-build step"})
                continue
            senv = dict(env)
            senv.update({k2: str(v) for k2, v in (s.get("env") or {}).items()})
            l1.append({"job": jid, "step": name, "run": run, "env": senv})
    test_job = wf["jobs"]["test"]
    l2 = []
    for s in test_job.get("steps") or []:
        run = s.get("run")
        if run and run.strip().startswith("cargo test"):
            l2.append({"job": "test", "step": s.get("name") or "cargo test", "run": run.strip()})
    return {"l1": l1, "l2": l2, "selected_jobs": sorted(jobs) if jobs is not None else "all",
            "unselected_jobs": unselected_jobs,
            "excluded_jobs": excluded_jobs, "excluded_steps": excluded_steps}


def run_step(step, timeout=1800):
    body = _subst(step["run"])
    env = cargo_env({k: _subst(v) for k, v in step["env"].items()})
    env["SYNTH"] = str(BIN)
    before = {p.name for p in ROOT.iterdir() if p.is_file()}
    t0 = time.time()
    try:
        r = subprocess.run(
            ["bash", "-eo", "pipefail", "-c", body], cwd=ROOT, env=env,
            capture_output=True, text=True, timeout=timeout,
        )
        code, out = r.returncode, (r.stdout + "\n" + r.stderr)
    except subprocess.TimeoutExpired as ex:
        code, out = 124, f"TIMEOUT after {timeout}s\n" + str(ex.stdout or "")[-2000:]
    # CI steps `tee` their transcripts into the checkout (ja1189.txt, …);
    # remove the plain files a step created at the root so none is committed.
    for p in ROOT.iterdir():
        if p.is_file() and p.name not in before:
            p.unlink()
    return code, out, time.time() - t0


def run_l2(l2):
    """Run the test job's cargo commands; returns (green, failing_tests,
    failing_binaries, seconds)."""
    t0 = time.time()
    failing, binaries = [], set()
    for step in l2:
        cmd = step["run"]
        if cmd.startswith("cargo test --workspace"):
            cmd = cmd + " --no-fail-fast"
        r = subprocess.run(
            ["bash", "-eo", "pipefail", "-c", cmd], cwd=ROOT, env=cargo_env(),
            capture_output=True, text=True, timeout=3600,
        )
        if r.returncode != 0:
            out = r.stdout + r.stderr
            current_bin = None
            for line in out.splitlines():
                # cargo prints `Running tests/x.rs (…/deps/x-HASH)` and
                # `Running unittests src/lib.rs (…/deps/crate-HASH)`.
                m = re.search(r"Running .*?/deps/([A-Za-z0-9_]+)-[0-9a-f]+\)?\s*$", line)
                if m:
                    current_bin = m.group(1)
                m = re.match(r"^test (\S+) \.\.\. FAILED", line)
                if m:
                    failing.append(f"{current_bin or '?'}::{m.group(1)}")
                    binaries.add(current_bin or "?")
            if not failing:
                failing.append(f"{step['step']}: exit {r.returncode}")
                binaries.add("?")
    return (not failing), failing[:40], sorted(binaries), time.time() - t0


# ---------------------------------------------------------------------------
# RQ-66-POTENCY (#1189): distinguish "the oracle ran and found something
# wrong" from "the oracle could not run" BEFORE any mutant is scored against
# it. scripts/mutation_survey.py used to score ANY non-zero step exit as a
# KILL; 147 of 196 ci.yml oracle steps invoke bare `python`, absent on this
# Mac, so a re-survey nearly published a fabricated 0 % survival (every
# mutant read as trivially killed by exit-127 steps in ~0.1 s each). The fix
# is to PROBE every suite step on the unmutated tree first and REFUSE to
# start when a step is UNRUNNABLE here — as opposed to a step that executes
# and legitimately finds the unmutated tree red (e.g.
# fact_spec_div_494_differential.py is red locally while green in CI; that is
# real evidence about this tree, not about the environment, and must not be
# refused into silence or it would become impossible to survey anywhere the
# environment differs even slightly from CI).
# ---------------------------------------------------------------------------
UNRUNNABLE_PATTERNS = (
    # (compiled regex over the tail of combined stdout+stderr, reason template)
    # Each pattern is a FIXED, environment-specific string a script would not
    # organically produce as its own deliberate result — deliberately NOT
    # matching generic `ImportError:` or a bare "No such file or directory"
    # (that is a Python FileNotFoundError's own `[Errno 2]` shape, which a
    # script can raise on purpose for a missing FIXTURE, not a missing tool —
    # the exact over-broad match that would misclassify a legitimate red as
    # unrunnable, or refuse the survey into never running anywhere).
    (re.compile(r"^(?:bash: (?:line \d+: )?)?(\S+): command not found\s*$", re.MULTILINE),
     "'{0}' not found on PATH"),
    (re.compile(r"^ModuleNotFoundError: No module named '([^']+)'", re.MULTILINE),
     "missing Python package '{0}'"),
    (re.compile(r"^env: [‘'\"]?([^’'\":\s]+)[’'\"]?: No such file or directory\s*$", re.MULTILINE),
     "interpreter '{0}' not found (env shebang)"),
)


def classify_unrunnable(code, out):
    """Pure. `code`/`out` are one step's (exit code, combined stdout+stderr).
    Returns a short human reason when the step could not EXECUTE in this
    environment (missing interpreter, missing binary, an import error for an
    uninstalled package — exactly the #1189 shape) or None when a non-zero
    exit is a step that actually RAN and is a different thing: a real
    assertion failure, a real diff, a real decline — evidence about the tree,
    not about the environment. `None` says nothing about pass/fail, only that
    a failure (if any) is not attributable to environment absence."""
    if code == 0:
        return None
    tail = out[-4000:]
    # Text patterns first: when one matches it names the actual missing
    # interpreter/package, a strictly more useful reason than the bare exit
    # code below. The exit-code fallback exists because bash's own
    # "command not found" message is not always on the LAST 4000 chars of a
    # noisy step, or a wrapper script can propagate 127 without repeating it.
    for pat, tmpl in UNRUNNABLE_PATTERNS:
        m = pat.search(tail)
        if m:
            return tmpl.format(m.group(1))
    if code == 127:
        return "exit 127 (command not found)"
    if code == 126:
        return "exit 126 (found but not executable)"
    return None


def probe_l1(l1_steps, log_prefix=""):
    """Run every L1 step ONCE on the (assumed unmutated) current tree.
    Returns (green, unrunnable, red): `green` is [(step, seconds)] for exit 0,
    `unrunnable` and `red` are [{job, step, exit, reason, tail}] — the same
    shape, split by `classify_unrunnable` so the caller can REFUSE on the
    former and merely EXCLUDE the latter (a step already red pre-mutation
    gives zero signal about a mutation either way, but only an unrunnable one
    is evidence the harness itself is broken here)."""
    green, unrunnable, red = [], [], []
    for step in l1_steps:
        code, out, dt = run_step(step)
        if code == 0:
            green.append((step, dt))
            log(f"{log_prefix}L1 {step['job']} / {step['step'][:50]}: ok ({dt:.0f}s)")
            continue
        reason = classify_unrunnable(code, out)
        tail = "\n".join(out.strip().splitlines()[-6:])[-600:]
        entry = {"job": step["job"], "step": step["step"], "exit": code,
                 "seconds": round(dt, 1), "tail": tail}
        if reason:
            entry["reason"] = reason
            unrunnable.append(entry)
            log(f"{log_prefix}UNRUNNABLE {step['job']} / {step['step'][:60]}: {reason}")
        else:
            entry["reason"] = "red on the unmutated binary"
            red.append(entry)
            log(f"{log_prefix}red-on-baseline (excluded, not unrunnable) {step['job']} / {step['step'][:60]}")
    return green, unrunnable, red




def l2_is_current(ledger, current_commit=None):
    """L2 (`cargo test --workspace` and friends) is NOT re-executed by
    `preflight_suite` — on an already-built target that is still real
    minutes of test EXECUTION (RQ-66-DELETE's own evidence: 278s green), and
    `run`/`controls` are RESUMABLE commands invoked many times per survey —
    unconditionally re-running the whole workspace suite on every resume
    would tax every one of those invocations for a risk `baseline` (and
    `cmd_l2`) already gate at the point L2 is actually validated. Instead,
    L2's validated-green status is trusted IFF `suite["l2_validated_at"]`
    (set by `baseline` and by `l2`, whichever last confirmed L2 green) equals
    the commit this tree is at NOW: a commit that moved since then means the
    ledger's L2 validation no longer describes this tree, and an L2 "kill"
    scored against it would repeat the #1189 false-kill shape for the same
    reason an unrunnable L1 step does. `current_commit` defaults to
    `head_commit()`; overridable so this decision is testable as a function
    of its inputs, independent of `baseline["commit"]` (which `l2` does not
    — and must not need to — update)."""
    suite = ledger.get("suite") or {}
    current_commit = head_commit() if current_commit is None else current_commit
    return bool(suite.get("l2_baseline_seconds")) and suite.get("l2_validated_at") == current_commit


def preflight_l1(suite, log_prefix=""):
    """RQ-66-POTENCY (#1189): re-probe a suite's L1 steps on the CURRENT tree
    before ANY mutant is evaluated against them. A ledger's `suite` may have
    been baselined elsewhere (CI) or a while ago; a step that cannot execute
    HERE must not be scored as evidence about a mutation — REFUSES (raises
    SystemExit) when anything is UNRUNNABLE. Returns the L1 list callers
    should score against: EITHER `suite["l1"]` unchanged, OR — when a step
    executed and is merely red on this tree (zero signal about a mutation
    either way, not evidence the harness is broken) — a COPY with that step
    dropped. `suite["l1"]` itself is deliberately left untouched (only
    `l1_excluded_at_preflight` is recorded on it, as an audit trail):
    mutating the persisted list would let one transiently-red step silently
    and permanently shrink the derived suite the next time the ledger is
    saved. Host-environment concern only — callers own any L2 check, which
    has a different right answer depending on whether the caller expects the
    tree to have moved since `baseline` (see `l2_is_current` vs. running `l2`
    directly)."""
    _green, unrunnable, red = probe_l1(suite["l1"], log_prefix=log_prefix)
    if unrunnable:
        lines = "\n".join(f"  L1 {e['job']} / {e['step']}: {e['reason']}" for e in unrunnable)
        sys.exit(
            f"REFUSING TO RUN: {len(unrunnable)} suite step(s) cannot execute on this "
            f"tree/environment. Scoring a mutant against a step that never ran would count a "
            f"dead oracle as a kill (#1189):\n{lines}\n"
            f"Fix the environment (missing interpreter / package / binary), or re-`baseline` "
            f"with a --jobs subset that excludes the unreachable jobs.")
    usable_l1 = suite["l1"]
    if red:
        excluded = {(e["job"], e["step"]) for e in red}
        usable_l1 = [s for s in suite["l1"] if (s["job"], s["step"]) not in excluded]
        suite.setdefault("l1_excluded_at_preflight", [])
        suite["l1_excluded_at_preflight"] = [
            e for e in suite["l1_excluded_at_preflight"] if (e["job"], e["step"]) not in excluded
        ] + red
        log(f"{log_prefix}{len(red)} L1 step(s) legitimately red on this tree — excluded from "
            f"this run's scoring (not unrunnable, but zero signal about a mutation either way)")
    return usable_l1


def preflight_suite(ledger, log_prefix=""):
    """`run`/`controls` variant: `preflight_l1` plus the CHEAP `l2_is_current`
    check (see its docstring — valid here because these commands resume a
    survey across MANY invocations against a tree that is not expected to
    move between them; re-running `cargo test --workspace` on every resume
    would tax every one of them for a risk `baseline`/`l2` already gate at
    the point L2 is actually validated). `cmd_ci` does NOT use this function:
    it inherently replays against a tree EXPECTED to have moved since
    `baseline`, so the cheap commit-match check would refuse it by design —
    it runs `l2` directly, once, when its subset actually needs it."""
    suite = ledger["suite"]
    if not l2_is_current(ledger):
        sys.exit(
            f"REFUSING TO RUN: L2 (cargo test) was last validated at commit "
            f"{suite.get('l2_validated_at')!r}, but this tree is at {head_commit()!r} (or L2 "
            f"was never validated at all). An L2 kill scored against an un-revalidated tree "
            f"risks the same false-kill shape as an unrunnable L1 step (#1189) — re-run "
            f"`baseline` or `l2` on this tree first.")
    return preflight_l1(suite, log_prefix=log_prefix)


# ---------------------------------------------------------------------------
# Ledger
# ---------------------------------------------------------------------------
def load_ledger(path):
    if path.exists():
        return json.loads(path.read_text())
    return {"meta": {}, "baseline": {}, "suite": {}, "mutants": [], "controls": [], "ci_subset": []}


def save_ledger(path, ledger):
    # A derived `summary` with UNIQUE `survey_*` keys so claims.yaml can pin
    # the published numbers by exact text against this file; the counts are
    # re-derived from the records on every save, never hand-edited.
    if ledger.get("mutants"):
        s = summarize(ledger)
        ledger["summary"] = {f"survey_{k}": v for k, v in s.items()}
        ledger["summary"]["survey_controls_killed"] = sum(
            1 for c in ledger.get("controls", []) if c.get("classification") == "KILLED")
        ledger["summary"]["survey_controls"] = len(ledger.get("controls", []))
    path.parent.mkdir(parents=True, exist_ok=True)
    # indent=2: the committed ledger's format (the v0.65 cold review
    # re-indented it by hand); writing anything else turns a 400-line
    # content change into a 28,000-line whitespace diff nobody can review.
    path.write_text(json.dumps(ledger, indent=2, sort_keys=False) + "\n")


def head_commit():
    return subprocess.run(["git", "rev-parse", "--short=8", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()


# RQ-66-POTENCY (#1189): the fields that describe HOW a sample was drawn —
# not `candidate_sites`, which is live tree-state context that legitimately
# drifts as the codebase changes and is refreshed every run regardless.
FRAME_FIELDS = ("seed", "per_region", "oversample")


def draw_frame(existing_meta, seed, per_region, oversample):
    """Pure. `cmd_run` used to unconditionally overwrite `ledger["meta"]`
    with its own argparse defaults on EVERY invocation, so re-running `run`
    against an existing ledger silently replaced the recorded description of
    how the survey was drawn — v0.65 shipped `per_region: 12` this way for a
    sample actually drawn at 8, and a coordinator check reading `meta` was
    fooled by it.

    The frame is written ONCE, when a survey is first drawn against a ledger
    that has none yet. A later `run` invocation must reproduce the SAME three
    numbers: if it does, there is nothing to write (not a "no-op overwrite" —
    literally no assignment happens); if any differs, refuse rather than let
    the ledger's own record of its sampling frame silently go wrong.

    Returns (fields_to_write: dict, ok: bool, message: str | None). Callers
    must `sys.exit(message)` when `ok` is False rather than proceed."""
    frame = {"seed": seed, "per_region": per_region, "oversample": oversample}
    have = {k: existing_meta.get(k) for k in FRAME_FIELDS}
    if all(v is None for v in have.values()):
        return frame, True, None
    if have == frame:
        return {}, True, None
    return {}, False, (
        f"refusing to run: this ledger's sampling frame is recorded as {have}, but this "
        f"invocation asked for {frame}. Re-running `run` against an existing ledger must not "
        f"silently rewrite the frame (#1189 — v0.65 shipped per_region:12 this way for a sample "
        f"drawn at 8) — pass the SAME --seed/--per-region/--oversample as the recorded draw, or "
        f"use a fresh --ledger for a genuinely different frame.")


# ---------------------------------------------------------------------------
# Pipeline per mutant
# ---------------------------------------------------------------------------
def evaluate(site, ledger, text_key="after", run_oracles=True, log_prefix="", wide=True, l1=None):
    """Run one mutant through: build -> triage -> (probe | suite). Returns the
    ledger record. The working tree is restored on every path. `wide` (default
    on since RQ-66-DELETE) makes a byte-identical mutant's reach probe also run
    REACH_CFGS, so no DEAD verdict is ever recorded without the wide evidence
    beside it. `l1`, when given, overrides the suite's L1 list for THIS
    mutant's scoring only (RQ-66-POTENCY's preflight-filtered list) — see
    `run_suite`."""
    rec = {k: site[k] for k in ("id", "region", "op", "file", "start", "end", "before", "after")}
    t0 = time.time()
    base = ledger["baseline"]["corpus"]
    with Edit(site, text_key):
        ok, err, bt = build_synth()
        if not ok:
            rec.update(status="uncompilable", classification="UNCOMPILABLE", build_error=err[:300])
            rec["seconds"] = round(time.time() - t0, 1)
            log(f"{log_prefix}{site['id']}: UNCOMPILABLE ({err[:80]})")
            return rec
        mut_corpus, _ = compile_corpus(TARGET_DIR / "mutant-corpus")
        changed = diff_corpus(base, mut_corpus)
        rec["changed"] = changed
        if "__triage__" in mut_corpus:
            rec["triage_note"] = mut_corpus["__triage__"]
        rec["bytes"] = "changed" if changed else "identical"
        hung = [c["module"] for c in changed if c["kind"] == "compile-timeout"]
        if hung:
            rec.update(status="killed", classification="KILLED",
                       killed_by={"layer": "timeout", "job": "(compiler hang)",
                                  "step": f"synth compile hung > {COMPILE_TIMEOUT}s on {hung[0]}"
                                          f"{' (+%d more)' % (len(hung) - 1) if len(hung) > 1 else ''}"
                                          " — every CI job times out"})
        elif changed and run_oracles:
            rec.update(run_suite(ledger, log_prefix, l1=l1))
    assert git_clean(site["file"]), f"tree not restored: {site['file']}"
    if not changed:
        rec.update(reach_probe(site, ledger, wide=wide))
    elif not run_oracles:
        rec.update(status="changed-unrun", classification="CHANGED")
    rec["seconds"] = round(time.time() - t0, 1)
    log(f"{log_prefix}{site['id']}: {rec['classification']} bytes={rec['bytes']} "
        f"changed={len(changed)} {rec.get('killed_by', {}).get('step', '')} ({rec['seconds']}s)")
    return rec


def run_suite(ledger, log_prefix="", l1=None):
    """`l1` overrides `ledger["suite"]["l1"]` for this call only — used by
    `preflight_suite` callers to score against the steps found runnable HERE
    without PERSISTING that narrower list as the ledger's own record of the
    derived suite (a step excluded for being red on one tree must not vanish
    from the suite forever the moment `save_ledger` next fires)."""
    suite = ledger["suite"]
    l1 = suite["l1"] if l1 is None else l1
    for step in l1:
        code, out, dt = run_step(step)
        if code != 0:
            tail = "\n".join(out.strip().splitlines()[-6:])
            return {
                "status": "killed", "classification": "KILLED",
                "killed_by": {"layer": "execution", "job": step["job"], "step": step["step"],
                              "exit": code, "seconds": round(dt, 1), "tail": tail[-800:]},
            }
    green, failing, binaries, dt = run_l2(suite["l2"])
    if not green:
        kind = "freeze-only" if binaries and all(b in FREEZE_TEST_BINARIES for b in binaries) else "structure"
        return {
            "status": "killed", "classification": "KILLED",
            "killed_by": {"layer": kind, "job": "test", "step": "cargo test",
                          "tests": failing, "binaries": binaries, "seconds": round(dt, 1)},
        }
    return {"status": "survived", "classification": "UNTESTED", "suite_seconds": round(dt, 1)}


def reach_probe(site, ledger, wide=False):
    """Classify a byte-identical mutant EQUIVALENT (its decision was evaluated
    on the corpus) or DEAD (never evaluated). DEAD is relative to CORPUS_CFGS;
    with `wide` the same probe binary is also run under REACH_CFGS and the
    reaching modules are recorded per configuration as `reach_wide` — the
    evidence that turned v0.65's four DEAD deletion candidates into four
    reachable sites (RQ-66-DELETE)."""
    if not site.get("probe"):
        return {"status": "identical", "reach": "no-probe", "classification": "UNRESOLVED"}
    with Edit(site, "probe"):
        ok, err, _ = build_synth()
        if not ok:
            res = {"status": "identical", "reach": "unknown", "classification": "UNRESOLVED", "probe_error": err[:200]}
        else:
            _, reached = compile_corpus(TARGET_DIR / "probe-corpus", capture_marker=True)
            res = {"status": "identical", "reach": "reached" if reached else "unreached"}
            wide_res = wide_reach() if wide else None
            cls, note = classify_identical(reached, wide_res)
            res["classification"] = cls
            if note:
                res["reach_note"] = note
            if wide:
                res["reach_wide"] = wide_res
                res["reach_wide_at"] = head_commit()
    assert git_clean(site["file"]), f"tree not restored after probe: {site['file']}"
    return res


def wide_reach():
    """With a probe binary built: {cfg: sorted module names that printed the
    marker} over every REACH_CFGS configuration."""
    out = {}
    for cfg, (flags, env) in REACH_CFGS.items():
        keys = set()
        compile_corpus(TARGET_DIR / f"reach-{cfg}", capture_marker=True,
                       cfgs={cfg: flags}, env=env, reached_out=keys)
        out[cfg] = sorted(k.split("|")[0] for k in keys)
    return out


def classify_identical(corpus_reached, wide):
    """The verdict for a byte-identical mutant, as a pure function (RQ-66-DELETE,
    #1238 — the salvage of DEAD as a category). EQUIVALENT: the decision was
    evaluated on the corpus and bytes did not move. DEAD: never evaluated under
    CORPUS_CFGS AND under every REACH_CFGS configuration — only then is it a
    deletion CANDIDATE (still not a proof). Reached ONLY under REACH_CFGS is
    neither: the byte triage was not run under those configurations, so it is
    UNRESOLVED with a note, never DEAD. v0.65 assigned DEAD from CORPUS_CFGS
    alone and published four deletion candidates that way; all four were
    reachable. `wide` is None when the wide probe did not run."""
    if corpus_reached:
        return "EQUIVALENT", None
    if wide is None:
        return "DEAD", "reach probed under CORPUS_CFGS only — not a deletion candidate until REACH_CFGS agree"
    hit = {cfg: mods for cfg, mods in wide.items() if mods}
    if hit:
        return "UNRESOLVED", ("reached only under REACH_CFGS (" + ", ".join(sorted(hit)) +
                              ") — byte triage was not run under those configurations; neither DEAD nor EQUIVALENT")
    return "DEAD", None


def reach_wide_failures(want, got):
    """The `want_reach_wide` check, as a pure function so it is unit-testable:
    every pinned witness module must still reach the site under its
    configuration (SUBSET semantics — reach may widen without a ledger edit,
    but a pinned witness going silent is red). Returns [(cfg, module)]."""
    got = got or {}
    return [(cfg, m) for cfg, mods in (want or {}).items() for m in mods if m not in set(got.get(cfg, []))]


# ---------------------------------------------------------------------------
# Red-first controls — mutations KNOWN to be caught. Located by anchor text.
# ---------------------------------------------------------------------------
def control_sites():
    rel = "crates/synth-synthesis/src/instruction_selector/select_with_stack.rs"
    lines = (ROOT / rel).read_text().splitlines()
    out = []
    # C1: disable the #1189 copy (the pre-fix behaviour, byte-for-byte). The
    # v0.64 merge moved the liveness gate into the shared helper
    # `copy_live_home_then_results` in the selector's root file.
    rel1 = "crates/synth-synthesis/src/instruction_selector.rs"
    lines1 = (ROOT / rel1).read_text().splitlines()
    for i, l in enumerate(lines1):
        if l.strip() == "if !live_home {":
            out.append({"id": "CONTROL/1189-copy-disabled", "region": "R3-direct", "op": "GUARD",
                        "file": rel1, "start": i + 1, "end": i + 1, "col": 0, "before": l,
                        "after": l.replace("if !live_home {", "if true {"), "probe": None,
                        "expect_killer": "join_alias_1189_differential.py"})
            break
    # C2: swap the select operands on the direct selector (PR #1216's plant).
    pat = re.compile(r"rule_i32_select\(dst, cond_reg, val1, val2\)")
    for i, l in enumerate(lines):
        if pat.search(l):
            out.append({"id": "CONTROL/select-operands-swapped", "region": "R3-direct", "op": "REG",
                        "file": rel, "start": i + 1, "end": i + 1, "col": 0, "before": l,
                        "after": pat.sub("rule_i32_select(dst, cond_reg, val2, val1)", l), "probe": None,
                        "expect_killer": None})
            break
    # C3: seed R10 (linear-memory size) into R9 in the startup blob.
    rel5 = "crates/synth-cli/src/main.rs"
    lines5 = (ROOT / rel5).read_text().splitlines()
    for i, l in enumerate(lines5):
        if "encode_thumb2_movw(10, (memory_size & 0xFFFF) as u16)" in l:
            out.append({"id": "CONTROL/startup-r10-seeded-into-r9", "region": "R5-startup", "op": "IMM",
                        "file": rel5, "start": i + 1, "end": i + 1, "col": 0, "before": l,
                        "after": l.replace("encode_thumb2_movw(10,", "encode_thumb2_movw(9,"), "probe": None,
                        "expect_killer": None})
            break
    if len(out) != 3:
        raise RuntimeError(f"control anchors not all found: {[c['id'] for c in out]}")
    return out


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------
def cmd_sites(args):
    sites = enumerate_sites()
    from collections import Counter

    c = Counter((s["region"], s["op"]) for s in sites.values())
    print(f"{'region':14} " + " ".join(f"{op:>8}" for op in OPS) + f" {'total':>7}")
    for region in REGIONS:
        row = [c[(region, op)] for op in OPS]
        print(f"{region:14} " + " ".join(f"{n:>8}" for n in row) + f" {sum(row):>7}")
        for rel, s, e in region_spans(region):
            print(f"    {rel}:{s}-{e} ({e - s + 1} lines)")
    print(f"{'TOTAL':14} " + " ".join(f"{sum(c[(r, op)] for r in REGIONS):>8}" for op in OPS) + f" {len(sites):>7}")


def cmd_sample(args):
    sites = enumerate_sites()
    order = sample_sites(sites, args.seed, args.per_region, args.oversample)
    for s in order:
        print(f"{s['id']}\n  - {s['before'].strip()[:110]}\n  + {s['after'].strip()[:110]}")


def cmd_baseline(args):
    ledger = load_ledger(args.ledger)
    ensure_symlink()
    ok, err, bt = build_synth()
    if not ok:
        sys.exit(f"baseline build failed: {err}")
    log(f"baseline build {bt:.0f}s")
    corpus, _ = compile_corpus(TARGET_DIR / "base-corpus")
    n_ok = sum(1 for v in corpus.values() if v != "DECLINE")
    log(f"baseline corpus: {len(corpus)} (module, config) pairs, {n_ok} compiled, {len(corpus) - n_ok} declined")
    jobs = [j.strip() for j in args.jobs.split(",")] if args.jobs else None
    suite = derive_suite(jobs)
    if jobs is not None:
        got = {s["job"] for s in suite["l1"]}
        missing = [j for j in jobs if j not in got]
        if missing:
            sys.exit(f"--jobs names jobs with no runnable steps in ci.yml: {missing}")
    log(f"derived suite: L1 {len(suite['l1'])} steps from ci.yml ({len({s['job'] for s in suite['l1']})} jobs, "
        f"selected={suite['selected_jobs']}), L2 {len(suite['l2'])} cargo commands; "
        f"unselected jobs {len(suite['unselected_jobs'])}, excluded jobs {len(suite['excluded_jobs'])}, "
        f"excluded steps {len(suite['excluded_steps'])}")
    # RQ-66-POTENCY (#1189): probe every L1 step on the unmutated tree BEFORE
    # it can ever be scored against a mutant. A step that cannot execute here
    # (missing interpreter/package/binary) is refused outright — scoring it
    # would count a dead oracle as a kill for every mutant that reaches it. A
    # step that executes and is simply red on this tree is excluded (as
    # always), which is a different and legitimate thing.
    green, unrunnable, red = probe_l1(suite["l1"], log_prefix="  ")
    if unrunnable:
        lines = "\n".join(f"  {e['job']} / {e['step']}: {e['reason']}" for e in unrunnable)
        sys.exit(
            f"REFUSING TO BASELINE: {len(unrunnable)} suite step(s) cannot execute on this "
            f"tree/environment (#1189 — an unrunnable step reads as a trivial kill for every "
            f"mutant that reaches it unless caught here):\n{lines}\n"
            f"Fix the environment (missing interpreter / package / binary), or pass --jobs to "
            f"exclude the unreachable jobs.")
    timed = sorted(green, key=lambda t: t[1])
    suite["l1"] = [dict(step, baseline_seconds=round(dt, 1)) for step, dt in timed]
    suite["l1_red_on_baseline"] = red
    if not args.skip_l2:
        green, failing, binaries, dt = run_l2(suite["l2"])
        log(f"  L2 cargo test: {'green' if green else 'RED ' + str(failing[:5])} ({dt:.0f}s)")
        if not green:
            sys.exit("baseline L2 is red — fix the tree before surveying")
        suite["l2_baseline_seconds"] = round(dt, 1)
        suite["l2_validated_at"] = head_commit()
    ledger["baseline"] = {"commit": head_commit(), "corpus": corpus,
                          "corpus_modules": len(corpus_modules()), "configs": CORPUS_CFGS}
    ledger["suite"] = suite
    ledger["meta"].update(date=_dt.date.today().isoformat(), commit=head_commit())
    save_ledger(args.ledger, ledger)
    log(f"baseline saved: L1 {len(timed)} green steps ({sum(t for t, _ in timed):.0f}s total), {len(red)} red-excluded")


def cmd_l2(args):
    """Time the structural layer on the unmutated tree and record it; a red
    baseline here would turn every L2 kill into noise, so it exits 1."""
    ledger = load_ledger(args.ledger)
    if not ledger.get("suite"):
        sys.exit("run `baseline` first")
    green, failing, binaries, dt = run_l2(ledger["suite"]["l2"])
    log(f"L2 baseline: {'green' if green else 'RED ' + str(failing[:5])} ({dt:.0f}s)")
    if not green:
        sys.exit(1)
    ledger["suite"]["l2_baseline_seconds"] = round(dt, 1)
    ledger["suite"]["l2_validated_at"] = head_commit()
    save_ledger(args.ledger, ledger)


def cmd_run(args):
    ledger = load_ledger(args.ledger)
    if not ledger.get("baseline"):
        sys.exit("run `baseline` first")
    ensure_symlink()
    l1 = preflight_suite(ledger)
    sites = enumerate_sites()
    fields, ok, msg = draw_frame(ledger["meta"], args.seed, args.per_region, args.oversample)
    if not ok:
        sys.exit(msg)
    ledger["meta"].update(fields)
    # candidate_sites is live tree-state context, not part of the locked
    # frame above — it is refreshed every run on purpose (RQ-66-POTENCY).
    ledger["meta"]["candidate_sites"] = {r: sum(1 for s in sites.values() if s["region"] == r) for r in REGIONS}
    done = {m["id"]: m for m in ledger["mutants"]}
    if args.only:
        order = [sites[i] for i in args.only.split(",")]
    else:
        order = sample_sites(sites, args.seed, args.per_region, args.oversample)
    counted = {r: sum(1 for m in ledger["mutants"] if m["region"] == r and m["classification"] != "UNCOMPILABLE") for r in REGIONS}
    for site in order:
        if site["id"] in done:
            continue
        if not args.only and counted[site["region"]] >= args.per_region:
            continue
        rec = evaluate(site, ledger, log_prefix=f"[{site['region']} {counted[site['region']]}/{args.per_region}] ", l1=l1)
        ledger["mutants"].append(rec)
        if rec["classification"] != "UNCOMPILABLE":
            counted[site["region"]] += 1
        save_ledger(args.ledger, ledger)
    log("run complete: " + ", ".join(f"{r}={counted[r]}" for r in REGIONS))


def cmd_controls(args):
    ledger = load_ledger(args.ledger)
    if not ledger.get("baseline"):
        sys.exit("run `baseline` first")
    ensure_symlink()
    l1 = preflight_suite(ledger)
    ledger["controls"] = []
    bad = 0
    for site in control_sites():
        rec = evaluate(site, ledger, log_prefix="[control] ", l1=l1)
        rec["expect"] = "KILLED"
        killer = rec.get("killed_by", {})
        rec["control_ok"] = rec["classification"] == "KILLED" and (
            not site.get("expect_killer") or site["expect_killer"] in json.dumps(killer))
        if not rec["control_ok"]:
            bad += 1
            log(f"CONTROL FAILED: {site['id']} came back {rec['classification']} (expected KILLED by {site.get('expect_killer') or 'any oracle'})")
        ledger["controls"].append(rec)
        save_ledger(args.ledger, ledger)
    if bad:
        sys.exit(f"{bad} control(s) not killed — the survey measures nothing; do not publish the rate")
    log("all controls KILLED")


def _test_binary_of(test_name):
    """Map a recorded failing test (`bin::path::name` or `?::path::name`) to
    the test binary that hosts it, by finding `fn name(` in the tree —
    `tests/x.rs` -> `x`; a `src/` file -> the crate's lib/bin unit tests."""
    name = test_name.split("::")[-1]
    r = subprocess.run(["git", "grep", "-l", f"fn {name}(", "--", "crates"], cwd=ROOT,
                       capture_output=True, text=True)
    files = [f for f in r.stdout.split() if f.endswith(".rs")]
    if len(files) != 1:
        return "?"
    p = Path(files[0])
    if p.parent.name == "tests":
        return p.stem
    crate = p.parts[1] if p.parts[0] == "crates" else "?"
    return f"{crate}(unit)"


def cmd_attribute(args):
    """Re-attribute structural kills from their recorded failing tests: set
    `binaries`, and sub-classify `freeze-only` when EVERY failing test lives
    in a frozen-byte golden. The first run recorded the test names but not
    their binaries (cargo's `Running …/deps/` line shape was missed)."""
    ledger = load_ledger(args.ledger)
    n = 0
    for m in ledger["mutants"] + ledger.get("controls", []):
        kb = m.get("killed_by") or {}
        if kb.get("layer") not in ("structure", "freeze-only") or not kb.get("tests"):
            continue
        bins = sorted({_test_binary_of(t) for t in kb["tests"]})
        kb["binaries"] = bins
        kb["layer"] = "freeze-only" if bins and all(b in FREEZE_TEST_BINARIES for b in bins) else "structure"
        n += 1
    save_ledger(args.ledger, ledger)
    log(f"re-attributed {n} structural kills")


def cmd_reanchor(args):
    """After the tree moves (a rebase), re-locate every recorded site by its
    `before` text — the id embeds the line number, so a shifted site must be
    re-resolved rather than trusted. Ambiguous or missing text is reported
    and left untouched (the CI replay then fails loudly on that entry)."""
    ledger = load_ledger(args.ledger)
    renamed = {}
    moved = ambiguous = 0
    for m in ledger["mutants"]:
        lines = (ROOT / m["file"]).read_text().split("\n")
        want = m["before"].split("\n")
        n = len(want)
        hits = [i for i in range(len(lines) - n + 1) if lines[i:i + n] == want]
        if len(hits) != 1:
            # fall back to the nearest hit to the old position
            if not hits:
                ambiguous += 1
                log(f"  NOT FOUND: {m['id']}")
                continue
            hits.sort(key=lambda i: abs(i + 1 - m["start"]))
        new_start = hits[0] + 1
        if new_start != m["start"]:
            old_id = m["id"]
            shift = new_start - m["start"]
            m["start"], m["end"] = new_start, m["end"] + shift
            m["id"] = re.sub(r":(\d+):(\d+)$", f":{new_start}:\\2", m["id"])
            renamed[old_id] = m["id"]
            moved += 1
    for e in ledger.get("ci_subset", []):
        if e["id"] in renamed:
            e["id"] = renamed[e["id"]]
    ledger["meta"]["reanchored_at"] = head_commit()
    save_ledger(args.ledger, ledger)
    log(f"reanchor: {moved} sites moved, {ambiguous} not found, tree {head_commit()}")
    if ambiguous:
        sys.exit(1)


def cmd_reach(args):
    """RQ-66-DELETE (#242): re-probe DEAD sites under REACH_CFGS — the
    hard-float / flag-on configurations the corpus never compiles — and name
    the modules that reach each one. Default: every DEAD mutant in the ledger.
    `--write` records `reach_wide` on the matching ledger records (then
    `pin-subset` pins the witnesses for `ci`). A site reached here is NOT a
    deletion candidate, whatever its `classification` says."""
    ledger = load_ledger(args.ledger)
    ensure_symlink()
    ok, err, _ = build_synth()
    if not ok:
        sys.exit(f"build failed: {err}")
    sites = enumerate_sites()
    recs = {m["id"]: m for m in ledger["mutants"]}
    ids = args.only.split(",") if args.only else [m["id"] for m in ledger["mutants"] if m["classification"] == "DEAD"]
    if not ids:
        sys.exit("no DEAD mutants in the ledger and no --only")
    reached_n = missing = 0
    for sid in ids:
        site = sites.get(sid)
        if site is None:
            log(f"{sid}: site no longer exists on this tree (re-anchor the ledger)")
            missing += 1
            continue
        t0 = time.time()
        res = reach_probe(site, ledger, wide=True)
        wide = res.get("reach_wide")
        if wide is None:
            log(f"{sid}: probe unusable ({res.get('reach')}: {res.get('probe_error', '')[:80]})")
            missing += 1
            continue
        any_reached = any(wide.values())
        reached_n += any_reached
        log(f"{sid}: corpus={res['reach']} wide={'REACHED' if any_reached else 'unreached'} "
            f"`{site['before'].strip()[:60]}` ({time.time() - t0:.0f}s)")
        for cfg, mods in wide.items():
            log(f"    {cfg:18s} {len(mods):3d}/{len(corpus_modules())}  " + "  ".join(mods[:5]) + (" ..." if len(mods) > 5 else ""))
        if args.write and sid in recs:
            recs[sid]["reach_wide"] = wide
            recs[sid]["reach_wide_at"] = res["reach_wide_at"]
            if any_reached:
                recs[sid]["reach_note"] = ("reached under REACH_CFGS — NOT a deletion candidate; the recorded "
                                          "classification is relative to CORPUS_CFGS only (RQ-66-DELETE, #1238)")
    if args.write:
        save_ledger(args.ledger, ledger)
    print(f"MUTANTS-REACH sites={len(ids)} reached-wide={reached_n} unreached-wide={len(ids) - reached_n - missing} unresolved={missing}")
    sys.exit(1 if missing else 0)


def cmd_pin_subset(args):
    """Write the ledger's `ci_subset`: every control (expected KILLED, with
    its recorded killer) plus the first N UNTESTED, EQUIVALENT and DEAD
    mutants in ledger order (expected to reproduce their byte-triage / reach
    verdicts). Deterministic, so the subset is a function of the ledger."""
    ledger = load_ledger(args.ledger)
    subset = []
    for c in ledger.get("controls", []):
        if c["classification"] != "KILLED":
            sys.exit(f"control {c['id']} is not KILLED in the ledger — nothing to pin")
        # `want_*` keys on purpose: the claims.yaml pins COUNT the mutant
        # records' `"classification":` lines, so an expectation must not
        # spell the same key.
        subset.append({"id": c["id"], "want_classification": "KILLED", "want_bytes": "changed",
                       "want_killed_by": {k: c["killed_by"][k] for k in ("layer", "job", "step")}})
    for cls, n in (("UNTESTED", args.untested), ("EQUIVALENT", args.equivalent), ("DEAD", args.dead)):
        picked = [m for m in ledger["mutants"] if m["classification"] == cls][:n]
        for m in picked:
            entry = {"id": m["id"], "want_classification": cls, "want_bytes": m["bytes"]}
            if m["bytes"] == "changed":
                entry["want_changed"] = sorted(c["module"] for c in m["changed"])
            else:
                entry["want_reach"] = m["reach"]
                # RQ-66-DELETE: a record carrying wide-reach evidence pins its
                # first N witnesses per configuration (sorted, deterministic);
                # `ci` requires every one of them to keep reaching the site.
                if m.get("reach_wide"):
                    entry["want_reach_wide"] = {
                        cfg: mods[: args.reach_witnesses] for cfg, mods in m["reach_wide"].items() if mods
                    }
            subset.append(entry)
    ledger["ci_subset"] = subset
    save_ledger(args.ledger, ledger)
    log(f"ci_subset pinned: {len(subset)} entries: " + ", ".join(e["id"] for e in subset))


def cmd_ci(args):
    """Replay the pinned subset; fail on any disagreement with the ledger."""
    ledger = load_ledger(args.ledger)
    ensure_symlink()
    ok, err, _ = build_synth()
    if not ok:
        sys.exit(f"build failed: {err}")
    # RQ-66-POTENCY (#1189): `ci` uses `preflight_l1` (NOT `preflight_suite`'s
    # cheap commit-match L2 check — that is WRONG here: `ci` inherently
    # replays against a tree EXPECTED to have moved since `baseline`, so "the
    # commit still matches" would refuse every real invocation by design).
    # L1 is probed narrowly (`--full`: the whole derived suite, since UNTESTED
    # replay walks all of it via `run_suite`; otherwise just the steps the
    # subset's KILLED-type entries actually depend on — "a small fixed
    # subset... not a re-run of the survey", per the module doc). L2 is
    # validated by running it ONCE, directly, on the UNMUTATED tree, whenever
    # the subset can reach it — a replayed L2 kill means nothing if L2 was
    # already red before any mutation was applied.
    subset_for_preflight = ledger.get("ci_subset") or []
    l1_override = None
    if args.full:
        l1_override = preflight_l1(ledger["suite"], log_prefix="[ci-preflight] ")
        needs_l2 = True
    else:
        killer_steps = {(kb["job"], kb["step"])
                         for e in subset_for_preflight
                         if (kb := e.get("want_killed_by", {})).get("layer") == "execution"}
        probe_targets = [s for s in ledger.get("suite", {}).get("l1", [])
                         if (s["job"], s["step"]) in killer_steps]
        if probe_targets:
            _green, unrunnable, red = probe_l1(probe_targets, log_prefix="[ci-preflight] ")
            # Both buckets refuse HERE (unlike the full-suite preflight, which
            # only excludes `red`): a KILLED verdict after mutating means
            # nothing if the pinned killer step is already non-green BEFORE
            # the mutation is applied, whether that is because it cannot run
            # or because it is red for a real reason on this tree.
            bad = unrunnable + red
            if bad:
                lines = "\n".join(f"  {e['job']} / {e['step']}: {e['reason']}" for e in bad)
                sys.exit(
                    f"REFUSING TO RUN: {len(bad)} pinned killer step(s) are not green on the "
                    f"UNMUTATED tree — replaying their mutation would be a vacuous KILLED "
                    f"verdict, not evidence the mutation was caught (#1189):\n{lines}")
        needs_l2 = any(
            e.get("want_killed_by", {}).get("layer") not in (None, "execution")
            for e in subset_for_preflight if e.get("want_classification") == "KILLED")
    if needs_l2:
        green, failing, _binaries, _dt = run_l2(ledger["suite"]["l2"])
        if not green:
            sys.exit(
                f"REFUSING TO RUN: L2 (cargo test) is red on the UNMUTATED tree "
                f"({failing[:3]}) — a replayed L2 KILLED verdict would be vacuous, not "
                f"evidence a mutation was caught (#1189).")
    base_corpus, _ = compile_corpus(TARGET_DIR / "base-corpus")
    if base_corpus != ledger["baseline"]["corpus"]:
        drift = [k for k in base_corpus if base_corpus[k] != ledger["baseline"]["corpus"].get(k)]
        print(f"NOTE: unmutated corpus differs from the ledger's baseline on {len(drift)} entries "
              f"(the tree moved since {ledger['baseline']['commit']}); byte-triage is compared against the LIVE baseline")
    live = dict(ledger)
    live["baseline"] = dict(ledger["baseline"], corpus=base_corpus)
    sites = enumerate_sites()
    controls = {c["id"]: c for c in control_sites()}
    subset = ledger.get("ci_subset") or []
    if len(subset) < 4:
        sys.exit(f"VACUOUS: ci_subset has {len(subset)} entries (< 4)")
    failures = []
    n_wide = n_wide_ok = 0
    for entry in subset:
        sid = entry["id"]
        expect = {"classification": entry["want_classification"], "bytes": entry.get("want_bytes"),
                  "killed_by": entry.get("want_killed_by"), "changed": entry.get("want_changed"),
                  "reach": entry.get("want_reach"), "reach_wide": entry.get("want_reach_wide") or {}}
        n_wide += bool(expect["reach_wide"])
        site = controls.get(sid) or sites.get(sid)
        if site is None:
            failures.append(f"{sid}: site no longer exists on this tree (re-anchor the ledger)")
            continue
        t0 = time.time()
        if expect["classification"] == "KILLED":
            with Edit(site, "after"):
                ok, err, _ = build_synth()
                if not ok:
                    failures.append(f"{sid}: expected KILLED but no longer compiles: {err[:120]}")
                    continue
                mut_corpus, _ = compile_corpus(TARGET_DIR / "mutant-corpus")
                changed = diff_corpus(base_corpus, mut_corpus)
                if not changed:
                    failures.append(f"{sid}: expected byte change, corpus identical — triage blind")
                    continue
                killer = expect["killed_by"]
                steps = [s for s in ledger["suite"]["l1"] if s["job"] == killer["job"] and s["step"] == killer["step"]]
                if killer["layer"] == "execution" and not steps:
                    failures.append(f"{sid}: recorded killer step {killer['job']}/{killer['step']} no longer in ci.yml")
                    continue
                if steps:
                    code, out, dt = run_step(steps[0])
                    verdict = "KILLED" if code != 0 else "SURVIVED"
                else:
                    green, failing, _, dt = run_l2(ledger["suite"]["l2"])
                    verdict = "SURVIVED" if green else "KILLED"
            assert git_clean(site["file"])
            print(f"{sid}: expect KILLED by {killer['job']}/{killer['step'][:40]} -> {verdict} ({time.time() - t0:.0f}s)")
            if verdict != "KILLED":
                failures.append(f"{sid}: a mutation the ledger records as KILLED now SURVIVES its killer — the oracle lost its power")
        else:
            rec = evaluate(site, live, run_oracles=(expect["classification"] == "UNTESTED" and args.full),
                           wide=bool(expect["reach_wide"]), l1=l1_override)
            want_bytes = expect["bytes"]
            if rec.get("bytes") != want_bytes:
                failures.append(f"{sid}: bytes {rec.get('bytes')} != ledger {want_bytes}")
            elif want_bytes == "changed":
                got = sorted(c["module"] for c in rec["changed"])
                if got != sorted(expect["changed"]):
                    failures.append(f"{sid}: changed-set moved: {len(got)} vs ledger {len(expect['changed'])}")
                if args.full and rec["classification"] != "UNTESTED":
                    failures.append(f"{sid}: ledger says UNTESTED, suite now says {rec['classification']} "
                                    f"({rec.get('killed_by', {}).get('step')}) — an oracle gained reach: bank it in the ledger")
            else:
                if rec.get("reach") != expect["reach"]:
                    failures.append(f"{sid}: reach {rec.get('reach')} != ledger {expect['reach']}")
                if expect["reach_wide"]:
                    # RQ-66-DELETE: the DEAD verdict is relative to CORPUS_CFGS;
                    # under REACH_CFGS the pinned witnesses must still reach.
                    silent = reach_wide_failures(expect["reach_wide"], rec.get("reach_wide"))
                    if silent:
                        failures.append(
                            f"{sid}: reach-wide witnesses went SILENT {silent[:4]}"
                            f"{' ...' if len(silent) > 4 else ''} — the site became unreachable under "
                            f"REACH_CFGS, was deleted, or the probe went blind; a human decides which")
                    else:
                        n_wide_ok += 1
            wide_tag = ""
            if expect["reach_wide"]:
                wide_tag = " wide=" + ",".join(f"{c}:{len(rec.get('reach_wide', {}).get(c, []))}" for c in expect["reach_wide"])
            print(f"{sid}: expect {expect['classification']} -> {rec['classification']}{wide_tag} ({time.time() - t0:.0f}s)")
    n_killed = sum(1 for e in subset if e["want_classification"] == "KILLED")
    n_other = len(subset) - n_killed
    # RQ-66-DELETE: printed and grepped separately, so a subset with no wide-
    # reach entry at all cannot pass the reach-wide grep (entries >= 1).
    print(f"MUTANTS-REACH-WIDE entries={n_wide} reached={n_wide_ok} unreached={n_wide - n_wide_ok}")
    print(f"MUTANTS-CI subset={len(subset)} controls={n_killed} non-killed={n_other} failures={len(failures)}")
    for f in failures:
        print("FAIL:", f)
    if n_killed < 2 or n_other < 2:
        sys.exit("VACUOUS: need >= 2 known-KILLED and >= 2 known-not-KILLED entries")
    sys.exit(1 if failures else 0)


# ---------------------------------------------------------------------------
# THE SILENT SUBSET (RQ-66-WATCHED, from the v0.65 cold review). "KILLED"
# means CI went red, which counts the compiler REFUSING (#952, a decline
# census tripping), a PANIC, a non-vacuity FLOOR firing and a compiler HANG —
# none of which is an oracle noticing WRONG CODE. The honest denominator for
# "would an oracle catch this being wrong" is the mutants that changed bytes
# and were caught by NOTHING loud, and the honest rate is the survivors over
# that. The rule is MECHANICAL, applied to the recorded killer evidence, so
# the number is re-derived from the ledger rather than hand-tallied (v0.65's
# "4 of 15" was hand-tallied and does not decompose from its own records;
# under this rule the same ledger reads 4 of 16 — see MUTATION_SURVEY.md).
#   loud   := layer `timeout`, or layer `execution` whose recorded tail shows
#             a refusal / panic / floor and NO wrong-value comparison
#   silent := byte-changing and not loud (structure and freeze-only kills are
#             silent: a test or a golden noticed the bytes, the compiler did
#             not refuse them)
# A wrong-value comparison OUTRANKS a floor in the same tail: an execution
# differential that reported 10 wrong vectors and then also tripped its
# population floor did observe wrong code.
# ---------------------------------------------------------------------------
LOUD_RE = re.compile(
    r"#952|no functions compiled|VACUOUS|NEW DECLINE|panicked|index out of bounds|"
    r"RUST_BACKTRACE|FLOOR|floor is|lost its population|declared floor",
)
WRONG_VALUE_RE = re.compile(r"want=|got=|MISMATCH|BUG \[|CHECKS=(\d+)/(\d+)")


def is_loud_kill(m):
    """Was this KILLED mutant caught by something other than an oracle seeing
    wrong code? (See the block comment above.)"""
    kb = m.get("killed_by") or {}
    if kb.get("layer") == "timeout":
        return True
    if kb.get("layer") != "execution":
        return False
    tail = kb.get("tail") or ""
    for wm in WRONG_VALUE_RE.finditer(tail):
        if wm.group(1) is None or int(wm.group(1)) < int(wm.group(2)):
            return False  # a wrong value was observed: silent-caught
    return bool(LOUD_RE.search(tail))


def summarize(ledger):
    ms = [m for m in ledger["mutants"]]
    compiled = [m for m in ms if m["classification"] != "UNCOMPILABLE"]
    changed = [m for m in compiled if m.get("bytes") == "changed"]
    by = lambda cls: [m for m in ms if m["classification"] == cls]
    killed = by("KILLED")
    exec_k = [m for m in killed if m["killed_by"]["layer"] == "execution"]
    struct_k = [m for m in killed if m["killed_by"]["layer"] == "structure"]
    freeze_k = [m for m in killed if m["killed_by"]["layer"] == "freeze-only"]
    timeout_k = [m for m in killed if m["killed_by"]["layer"] == "timeout"]
    loud = [m for m in killed if is_loud_kill(m)]
    silent = [m for m in changed if not (m["classification"] == "KILLED" and is_loud_kill(m))]
    silent_exec = [m for m in exec_k if not is_loud_kill(m)]
    return {
        "sampled": len(ms), "uncompilable": len(by("UNCOMPILABLE")), "compiled": len(compiled),
        "changed": len(changed), "identical": len(compiled) - len(changed),
        "killed": len(killed), "killed_execution": len(exec_k), "killed_structure": len(struct_k),
        "killed_freeze_only": len(freeze_k), "killed_timeout": len(timeout_k),
        "untested": len(by("UNTESTED")), "equivalent": len(by("EQUIVALENT")), "dead": len(by("DEAD")),
        "unresolved": len(by("UNRESOLVED")),
        # the silent subset (RQ-66-WATCHED): loud kills removed from the frame
        "killed_loud": len(loud), "silent_changed": len(silent),
        "silent_killed_execution": len(silent_exec),
        "silent_killed_structure": len(struct_k), "silent_killed_freeze_only": len(freeze_k),
        "silent_untested": len(by("UNTESTED")),
    }


def cmd_report(args):
    ledger = load_ledger(args.ledger)
    s = summarize(ledger)
    rate = (100.0 * s["untested"] / s["changed"]) if s["changed"] else float("nan")
    print(f"survival rate: {s['untested']}/{s['changed']} byte-changing mutants = {rate:.1f}% UNTESTED")
    srate = (100.0 * s["silent_untested"] / s["silent_changed"]) if s["silent_changed"] else float("nan")
    print(f"SILENT-subset rate: {s['silent_untested']}/{s['silent_changed']} silently byte-changing mutants "
          f"= {srate:.1f}% UNTESTED ({s['killed_loud']} loud kills removed: refusal / panic / floor / hang; "
          f"silent kills: execution {s['silent_killed_execution']}, structure {s['silent_killed_structure']}, "
          f"freeze-only {s['silent_killed_freeze_only']})")
    print(json.dumps(s, indent=1))
    print()
    print("| region | sampled | uncompilable | identical (equiv/dead/unres.) | changed | killed (exec/struct/freeze-only/timeout) | UNTESTED | survival |")
    print("|---|---|---|---|---|---|---|---|")
    for region in REGIONS:
        ms = [m for m in ledger["mutants"] if m["region"] == region]
        c = lambda cls: sum(1 for m in ms if m["classification"] == cls)
        changed = sum(1 for m in ms if m.get("bytes") == "changed")
        k = [m for m in ms if m["classification"] == "KILLED"]
        kl = lambda layer: sum(1 for m in k if m["killed_by"]["layer"] == layer)
        ident = sum(1 for m in ms if m.get("bytes") == "identical")
        rate_r = f"{100.0 * c('UNTESTED') / changed:.0f} %" if changed else "n/a"
        print(f"| {region} | {len(ms)} | {c('UNCOMPILABLE')} | {ident} ({c('EQUIVALENT')}/{c('DEAD')}/{c('UNRESOLVED')}) | {changed} | "
              f"{len(k)} ({kl('execution')}/{kl('structure')}/{kl('freeze-only')}/{kl('timeout')}) | {c('UNTESTED')} | {rate_r} |")
    print()
    print("| id | operator | site | diff | classification | detail |")
    print("|---|---|---|---|---|---|")
    for m in ledger["mutants"]:
        if m["classification"] not in ("UNTESTED", "DEAD", "EQUIVALENT", "UNRESOLVED"):
            continue
        b = m["before"].strip().replace("|", "\\|")[:70]
        a = m["after"].strip().replace("|", "\\|")[:70]
        detail = ""
        if m["classification"] == "UNTESTED":
            detail = f"{len(m['changed'])} corpus objects changed"
        elif m.get("reach"):
            detail = f"reach={m['reach']}"
            if m.get("reach_wide") is not None:
                n = sum(len(v) for v in m["reach_wide"].values())
                detail += f"; REACH_CFGS: {n} reaching (module, cfg)" if n else "; REACH_CFGS: unreached"
        print(f"| `{m['id']}` | {m['op']} | `{Path(m['file']).name}:{m['start']}` | `{b}` -> `{a}` | {m['classification']} | {detail} |")
    print()
    print("| id | operator | site | diff | objects changed | killed by |")
    print("|---|---|---|---|---|---|")
    for m in ledger["mutants"]:
        if m["classification"] != "KILLED":
            continue
        kb = m["killed_by"]
        if kb["layer"] in ("execution", "timeout"):
            who = f"{kb['layer']}: {kb['job']} / {kb['step'][:70]}"
        else:
            tests = ", ".join(t.split("::")[-1] for t in kb.get("tests", [])[:3])
            more = f" (+{len(kb.get('tests', [])) - 3} more)" if len(kb.get("tests", [])) > 3 else ""
            who = f"{kb['layer']}: {', '.join(kb.get('binaries', []))} — `{tests}`{more}"
        b = m["before"].strip().replace("|", "\\|")[:60]
        a = m["after"].strip().replace("|", "\\|")[:60]
        print(f"| `{m['id']}` | {m['op']} | `{Path(m['file']).name}:{m['start']}` | `{b}` -> `{a}` | {len(m['changed'])} | {who} |")


def main():
    # A SIGTERM (a harness killed mid-mutant) must still restore the working
    # tree: turn it into SystemExit so every `with Edit(...)` unwinds. Measured
    # once the hard way — a killed run left a mutated selector on disk.
    import signal

    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ledger", type=Path, default=Path(os.environ.get("SYNTH_MUTANTS_LEDGER") or DEFAULT_LEDGER))
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("sites")
    p = sub.add_parser("sample")
    p.add_argument("--seed", type=int, default=1189)
    p.add_argument("--per-region", type=int, default=12)
    p.add_argument("--oversample", type=int, default=4)
    p = sub.add_parser("baseline")
    p.add_argument("--skip-l2", action="store_true")
    p.add_argument("--jobs", help="comma-separated ci.yml job ids: restrict L1 to this NAMED subset (recorded in the ledger)")
    p = sub.add_parser("run")
    p.add_argument("--seed", type=int, default=1189)
    p.add_argument("--per-region", type=int, default=12)
    p.add_argument("--oversample", type=int, default=4)
    p.add_argument("--only", help="comma-separated site ids to run regardless of the sample")
    sub.add_parser("controls")
    sub.add_parser("l2")
    sub.add_parser("attribute")
    sub.add_parser("reanchor")
    p = sub.add_parser("reach", help="RQ-66-DELETE: probe DEAD sites under REACH_CFGS and name the reaching modules")
    p.add_argument("--only", help="comma-separated site ids (default: every DEAD mutant in the ledger)")
    p.add_argument("--write", action="store_true", help="record reach_wide on the ledger records")
    p = sub.add_parser("pin-subset")
    p.add_argument("--untested", type=int, default=2)
    p.add_argument("--equivalent", type=int, default=1)
    p.add_argument("--dead", type=int, default=1)
    p.add_argument("--reach-witnesses", type=int, default=4,
                   help="RQ-66-DELETE: witnesses pinned per REACH_CFGS configuration for records carrying reach_wide")
    p = sub.add_parser("ci")
    p.add_argument("--full", action="store_true", help="also re-run the suite for UNTESTED entries")
    sub.add_parser("report")
    args = ap.parse_args()
    {"sites": cmd_sites, "sample": cmd_sample, "baseline": cmd_baseline, "run": cmd_run,
     "controls": cmd_controls, "l2": cmd_l2, "attribute": cmd_attribute, "reanchor": cmd_reanchor,
     "pin-subset": cmd_pin_subset, "ci": cmd_ci, "report": cmd_report, "reach": cmd_reach}[args.cmd](args)


if __name__ == "__main__":
    main()
