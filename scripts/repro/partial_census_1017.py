#!/usr/bin/env python3
# ci-status: manual (measurement) — RQ-59-PARTIALCENSUS (#1017) is a CENSUS, scoped by the maintainer to MEASURE and STOP: it re-derives the one-function-blocks-module share over a corpus's full decline set so the --allow-partial decision has a number instead of an intuition. It has no expected values and no verdict, so there is nothing for CI to fail on, and its input is a local real-world corpus CI does not carry. The behaviour it measures — that a declined function declines its whole module — is gated by the wired decline-honesty oracles, not by this report.
"""RQ-59-PARTIALCENSUS (#1017): re-derive the one-function-blocks-module share
over the FULL decline set of a corpus, per module — not just the top-12 decline
reasons #1017's lower bound covered.

THE QUESTION (#1017, decision deferred by the maintainer 2026-08-21 pending this
measurement): when one unsupported function blocks a whole module, is that the
DOMINANT decline cause (in which case refusing whole modules discards mostly-
compiled objects at scale and the policy fork is live), or a minority (in which
case the refusal is defensible policy and the honest action is to DOCUMENT it)?

WHAT THIS SCRIPT MEASURES, per module, on one backend (default: arm):
  a. does the module decline SOLELY because of per-function skips?  Operational
     definition: the plain `--all-exports --relocatable` run exits non-zero, AND
     re-running with `--allow-skipped-exports` exits zero (so no module-level
     blocker exists), OR the failure is the "no functions compiled successfully"
     bail (per-function skips took EVERY function — the 0%% end of the same
     class, not a different blocker).
  b. in those modules, what fraction of functions compiled — parsed from
     synth's own "N of M functions were skipped" warning (M = the full
     requested output set: exports + reachability-pulled internals).
  c. the DISTRIBUTION of that fraction (histogram, not a mean — a mean over a
     bimodal distribution would mislead exactly where the policy decision
     lives).
  d. components (binary layer field == 1) reported as a SEPARATE stratum from
     core modules — #1017 showed components are dominated by a different cause
     (import dispatch) and must not be pooled silently.
  e. (RQ-62-REACH increment 1) a four-bucket acceptance summary per stratum
     (accepted / partial / declined / errored) and a RANKED BLOCKER HISTOGRAM:
     one PRIMARY blocker per non-accepted module — the module-level error for a
     module-level decline, the modal per-function skip reason for a skip-only
     decline — so "which blocker accounts for how many modules" has a number.
     Instance-specific payloads (symbol lists, export-name lists, global-
     initializer dumps) are collapsed so one CAUSE is one bucket, and the #952
     export-skip / #1102 dangling-reloc refusals — POLICY errors whose root
     cause is the per-function declines behind them — are attributed to the
     modal per-function skip reason synth's own stderr names, when it names
     one.  Still a measurement: no expected values, no verdict.

This script only ever RUNS synth and READS its stderr; it changes no compile
behaviour.  It is the measurement, not the feature (#1017 / RQ-59-PARTIALCENSUS).

Usage:
  python3 scripts/repro/partial_census_1017.py --synth target/debug/synth \
      [--backend arm] [--json out.json] ROOT [ROOT ...]

ROOTs are directories scanned recursively for *.wasm (dedup by sha256; target/,
.git/, node_modules/, worktrees/ excluded) or individual .wasm files.
Exit code: 0 on a completed census (regardless of verdict mix), 2 on usage /
empty corpus.
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

SKIP_WARN_RE = re.compile(
    r"warning: (\d+) of (\d+) functions were skipped \(not in output\): (.+)"
)
SKIP_REASON_RE = re.compile(r"warning: skipping function '[^']+': (.+)")
# #952 refusal names WHICH exports were skipped and out of how many total
# exports — the numerator/denominator of the prune-then-compile question.
EXPORT_SKIP_RE = re.compile(
    r"(\d+) of (\d+) requested export\(s\) were skipped \(not in the "
    r"output object\): (.+?)\. Exiting non-zero",
    re.S,
)
# Wrapper prefixes stripped iteratively so the ROOT cause aggregates, not the
# layer it was reported through.
REASON_PREFIXES = (
    "backend 'arm' failed: ",
    "backend 'riscv' failed: ",
    "backend 'aarch64' failed: ",
    "compilation failed: ",
    "ARM encoding failed: ",
    "Synthesis failed: ",
    "Compilation failed: ",
)


def normalize_reason(reason):
    changed = True
    while changed:
        changed = False
        for p in REASON_PREFIXES:
            if reason.startswith(p):
                reason = reason[len(p):]
                changed = True
    # Collapse per-instance specifics (indices, offsets) so reasons bucket.
    reason = re.sub(r"\b\d+\b", "N", reason)
    return reason.strip()[:160]
EXCLUDE_PARTS = {"target", ".git", "node_modules", "worktrees", ".claude"}

# Histogram bins for fraction-of-functions-compiled, chosen so the two poles
# the policy question distinguishes ("one bad function in hundreds" vs "half
# the module") land in different bins.  Upper edge inclusive.
BINS = [
    ("0%", 0.0, 0.0),
    ("(0,25%]", 0.0, 0.25),
    ("(25,50%]", 0.25, 0.50),
    ("(50,75%]", 0.50, 0.75),
    ("(75,90%]", 0.75, 0.90),
    ("(90,<100%)", 0.90, 0.9999999),
]


def discover(roots):
    seen = {}
    for root in roots:
        p = Path(root)
        files = [p] if p.is_file() else sorted(p.rglob("*.wasm"))
        for f in files:
            # Exclusions apply to the path BELOW the root, so a corpus root
            # that itself lives under e.g. a worktree still scans.
            rel_parts = f.relative_to(p).parts if p.is_dir() else ()
            if any(part in EXCLUDE_PARTS for part in rel_parts):
                continue
            try:
                data = f.read_bytes()
            except OSError:
                continue
            if len(data) < 8 or data[:4] != b"\0asm":
                continue
            digest = hashlib.sha256(data).hexdigest()
            # keep the first path seen for a given content hash
            seen.setdefault(digest, (f, data))
    return [(f, data, d) for d, (f, data) in sorted(seen.items(), key=lambda kv: str(kv[1][0]))]


def is_component(data):
    # Core module preamble: version 0x01 0x00 0x00 0x00.
    # Component preamble: 2-byte version + 2-byte layer; layer == 1.
    return data[6] == 1


def _uleb(data, i):
    v = s = 0
    while True:
        b = data[i]
        i += 1
        v |= (b & 0x7F) << s
        if not b & 0x80:
            return v, i
        s += 7


def has_active_data(data):
    """Does this CORE module carry an ACTIVE data segment?  Flags #1041
    entanglement: ARM `--relocatable` currently drops active data segments
    silently (exit 0, no bytes, no symbol), so an ACCEPT verdict on such a
    module is an accept of an object whose data is missing — the verdict is
    real, but 'success' must not be read as 'complete image'."""
    if is_component(data):
        return None  # component layout differs; not the #1041 shape
    i = 8
    try:
        while i < len(data):
            sec_id = data[i]
            i += 1
            size, i = _uleb(data, i)
            if sec_id == 11:  # data section
                j = i
                count, j = _uleb(data, j)
                for _ in range(count):
                    flags, j = _uleb(data, j)
                    if flags in (0, 2):  # active (memidx 0 / explicit)
                        return True
                    if flags == 1:  # passive: [len][bytes]
                        n, j = _uleb(data, j)
                        j += n
                    else:
                        return None  # unknown encoding: don't guess
                return False
            i += size
    except IndexError:
        return None
    return False


def run_synth(synth, module, backend, extra, timeout):
    with tempfile.NamedTemporaryFile(suffix=".o") as tmp:
        cmd = [
            synth, "compile", str(module), "-b", backend,
            "--all-exports", "--relocatable", "-o", tmp.name,
        ] + extra
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout
            )
            return proc.returncode, proc.stderr
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT"


def first_error_line(stderr):
    for line in stderr.splitlines():
        if line.startswith("Error:") or line.lower().startswith("error"):
            return line.strip()[:200]
    tail = stderr.strip().splitlines()
    return (tail[-1].strip()[:200]) if tail else "(empty stderr)"


def skip_reasons(stderr):
    return Counter(
        normalize_reason(m.group(1))
        for m in SKIP_REASON_RE.finditer(stderr)
    )


def _names(csv_names):
    return [n.strip() for n in csv_names.strip().split(",") if n.strip()]


def _export_skip(err):
    """Parse the #952 refusal: (exports_skipped, total_exports, names)."""
    m = EXPORT_SKIP_RE.search(err)
    if not m:
        return None
    return int(m.group(1)), int(m.group(2)), _names(m.group(3))


def classify(synth, module, backend, timeout, component=False):
    rc, err = run_synth(synth, module, backend, [], timeout)
    if rc is None:
        return {"verdict": "TIMEOUT", "reason": "timeout"}
    m = SKIP_WARN_RE.search(err)
    skipped, total = (int(m.group(1)), int(m.group(2))) if m else (0, None)
    if rc == 0:
        if skipped:
            # Object shipped; only non-exported reachability helpers skipped.
            return {
                "verdict": "ACCEPT_INTERNAL_SKIPS",
                "skipped": skipped,
                "total": total,
                "fraction_compiled": (total - skipped) / total,
                "skip_reasons": dict(skip_reasons(err)),
            }
        return {"verdict": "ACCEPT_FULL"}
    # Non-zero: is the SOLE blocker per-function skips?
    if "no functions compiled successfully" in err:
        # Per-function skips took every function — same class, fraction 0.
        # Every real export is in that set, so there is nothing to prune
        # down to.
        return {
            "verdict": "DECLINE_SKIP_ONLY",
            "skipped": skipped or None,
            "total": total,
            "fraction_compiled": 0.0,
            "reason": "all functions skipped (nothing to emit)",
            "skip_reasons": dict(skip_reasons(err)),
            "prune_class": "entry-poisoned",
        }
    rc2, err2 = run_synth(
        synth, module, backend, ["--allow-skipped-exports"], timeout
    )
    if rc2 == 0:
        m2 = SKIP_WARN_RE.search(err2)
        if m2:
            s2, t2 = int(m2.group(1)), int(m2.group(2))
            skipped_names = _names(m2.group(3))
            rec = {
                "verdict": "DECLINE_SKIP_ONLY",
                "skipped": s2,
                "total": t2,
                "fraction_compiled": (t2 - s2) / t2,
                "skip_reasons": dict(skip_reasons(err2)),
            }
            # Prune-then-compile (DO-178C dead-code-removal shape): the #952
            # refusal on the PLAIN run names which EXPORTS were skipped.  If
            # every skipped function is itself a skipped export, requesting
            # only the surviving exports is a FULL compile — no partial
            # object, no manifest ambiguity.  If internal reachability
            # helpers were also skipped, attribution needs a call graph and
            # this census reports it unresolved rather than guessing.
            es = _export_skip(err)
            if es:
                e_skipped, e_total, e_names = es
                rec["exports_skipped"] = e_skipped
                rec["exports_total"] = e_total
                rec["prune_converts_to_full"] = set(skipped_names) <= set(
                    e_names
                )
                if not component:
                    rec["prune_class"] = prune_reachability(
                        module, skipped_names, set(e_names), timeout
                    )
            return rec
        # Declined plain but clean with the flag and no skip warning: should
        # not happen; surface it rather than misfile it.
        return {"verdict": "ANOMALY", "reason": first_error_line(err)}
    # Keep the plain run's per-function skip reasons: for the #952/#1102
    # refusal classes they carry the ROOT CAUSE the blocker histogram ranks.
    return {
        "verdict": "DECLINE_MODULE_LEVEL",
        "reason": first_error_line(err),
        "skip_reasons": dict(skip_reasons(err)),
    }


# One wat identifier/index token, shared by every call-graph regex below.
# Identifiers may be plain ($name) or QUOTED with arbitrary content including
# spaces ($"#func31 dummy") — wasm-tools emits the quoted form for names that
# are not valid plain identifiers.
_TOK = r'\$"[^"\\]*(?:\\.[^"\\]*)*"|\$[^\s()]+|\d+'
CALL_RE = re.compile(rf"\b(?:call|return_call)[ \t]+({_TOK})")
# ref.func'd functions can be invoked from ANYWHERE via call_ref / a funcref
# table, so they join the global indirect-target set, not one caller's edges.
REF_FUNC_RE = re.compile(rf"\bref\.func[ \t]+({_TOK})")
FUNC_HDR_RE = re.compile(rf"^\s*\(func (?:({_TOK}) )?(?:\(@name [^)]*\) )?\(;(\d+);\)")
IMPORT_FUNC_RE = re.compile(
    rf"^\s*\(import .*\(func (?:({_TOK}) )?(?:\(@name [^)]*\) )?\(;(\d+);\)"
)
ELEM_FUNC_RE = re.compile(rf"\(elem\b[^)]*?\bfunc((?:[ \t]+(?:{_TOK}))+)\)")
ELEM_TOK_RE = re.compile(_TOK)
EXPORT_FUNC_RE = re.compile(rf'\(export "((?:[^"\\]|\\.)*)" \(func ({_TOK})\)')


def prune_reachability(module, skipped_names, skipped_export_names, timeout):
    """DO-178C prune-then-compile attribution for a CORE module: from the
    surviving real exports, is any skipped function still reachable?  Uses
    `wasm-tools print` text; call_indirect is over-approximated by treating
    EVERY element-segment (and ref.func'd) function as a call target from any
    function that performs an indirect call — so 'unreachable' is sound and
    'reachable' may be pessimistic.  Skipped names arrive in synth's own
    naming: a real export name, or 'func_N' with N the function INDEX.
    Returns one of:
      'prunable'        — no skipped function reachable from any surviving
                          export: requesting only the surviving exports is a
                          FULL compile.
      'poisoned-reachable' — some surviving export (transitively) needs a
                          skipped function; pruning exports cannot help
                          without dropping that export too.
      'entry-poisoned'  — every real export was itself skipped; nothing
                          survives to prune down to.
      None              — analysis unavailable (wasm-tools missing/failed,
                          name mapping incomplete): reported unresolved, not
                          guessed.
    """
    try:
        proc = subprocess.run(
            ["wasm-tools", "print", str(module)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    name_to_idx = {}
    calls = {}  # idx -> set of callee tokens ($name or int)
    elem_targets = set()
    indirect_callers = set()
    exports = {}  # export name -> idx token
    cur = None
    for line in proc.stdout.splitlines():
        im = IMPORT_FUNC_RE.match(line)
        if im:
            if im.group(1):
                name_to_idx[im.group(1)] = int(im.group(2))
            continue  # imports have no body; keep cur on the last defined fn
        h = FUNC_HDR_RE.match(line)
        if h:
            idx = int(h.group(2))
            if h.group(1):
                name_to_idx[h.group(1)] = idx
            cur = idx
            calls.setdefault(cur, set())
        for m in EXPORT_FUNC_RE.finditer(line):
            exports[m.group(1)] = m.group(2)
        for m in ELEM_FUNC_RE.finditer(line):
            for tok in ELEM_TOK_RE.findall(m.group(1)):
                elem_targets.add(tok)
        for m in REF_FUNC_RE.finditer(line):
            elem_targets.add(m.group(1))
        if cur is not None:
            if "call_indirect" in line or "call_ref" in line:
                indirect_callers.add(cur)
            for m in CALL_RE.finditer(line):
                calls[cur].add(m.group(1))
    def resolve(tok):
        if tok.startswith("$"):
            return name_to_idx.get(tok)
        return int(tok)
    # Map synth's skipped names to indices.
    skipped_idx = set()
    for n in skipped_names:
        if n in exports:
            i = resolve(exports[n])
        elif re.fullmatch(r"func_(\d+)", n):
            i = int(n.split("_")[1])
        else:
            i = None
        if i is None:
            return None  # mapping incomplete: refuse to guess
        skipped_idx.add(i)
    surviving = [
        resolve(tok)
        for name, tok in exports.items()
        if name not in skipped_export_names
    ]
    if any(s is None for s in surviving):
        return None
    if not surviving:
        return "entry-poisoned"
    elem_idx = {resolve(t) for t in elem_targets}
    if None in elem_idx:
        return None
    seen = set()
    work = list(surviving)
    while work:
        i = work.pop()
        if i in seen:
            continue
        seen.add(i)
        if i in skipped_idx:
            return "poisoned-reachable"
        nxt = {resolve(t) for t in calls.get(i, ())}
        if None in nxt:
            return None
        if i in indirect_callers:
            nxt |= elem_idx
        work.extend(nxt)
    return "prunable"


def collapse_instance_lists(reason):
    """Collapse instance-specific payloads so one CAUSE buckets as one
    histogram row: the #1102 dangling-reloc symbol list ('func_25' ->
    'func_20', ...), the #952 skipped-export name list, and the global-
    initializer dump all differ per module while naming the same class.
    Applied AFTER normalize_reason (digits already collapsed to N).  The full
    per-module text is preserved in the --json records."""
    reason = re.sub(r"DECLINED: .*$", "DECLINED: <symbol list>", reason)
    reason = re.sub(
        r"skipped \(not in the output object\): .*$",
        "skipped (not in the output object): <export list>",
        reason,
    )
    reason = re.sub(r"\(global N = .*$", "(global <initializer list>)", reason)
    return reason


def _modal(skip_reasons):
    """The MODAL skip reason (most functions skipped for it; ties broken
    lexicographically so the ranking is deterministic)."""
    return max(skip_reasons.items(), key=lambda kv: (kv[1], kv[0]))[0]


def primary_blocker(rec):
    """One PRIMARY blocker per non-accepted module (RQ-62-REACH increment 1).

    DECLINE_MODULE_LEVEL -> the normalized, list-collapsed module-level error
    (the thing that refused the whole module) — EXCEPT the #952 export-skip
    and #1102 dangling-reloc refusals, which are POLICY errors whose root
    cause is the per-function declines behind them: those are attributed to
    the modal per-function skip reason synth's own stderr names, when it
    names one.  DECLINE_SKIP_ONLY -> the modal per-function skip reason.
    TIMEOUT/ANOMALY -> their own buckets.  Attribution, not verdict: the
    histogram ranks causes, it asserts nothing.
    """
    v = rec["verdict"]
    if v == "DECLINE_MODULE_LEVEL":
        reason = rec.get("reason", "?")
        if reason.startswith("Error: "):
            reason = reason[len("Error: "):]
        reason = collapse_instance_lists(normalize_reason(reason))
        sr = rec.get("skip_reasons") or {}
        if sr and (
            "requested export(s) were skipped" in reason
            or "retained function(s) relocate against" in reason
        ):
            return _modal(sr)
        return reason
    if v == "DECLINE_SKIP_ONLY":
        sr = rec.get("skip_reasons") or {}
        if not sr:
            return "(per-function skips, reasons unparsed)"
        return _modal(sr)
    if v == "TIMEOUT":
        return "timeout"
    return rec.get("reason", "?")


def bin_label(frac):
    if frac >= 1.0:
        return "100%"
    for label, lo, hi in BINS:
        if (frac == 0.0 and hi == 0.0) or (lo < frac <= hi):
            return label
    return "(90,<100%)"


def histogram(fractions):
    counts = Counter(bin_label(f) for f in fractions)
    labels = [b[0] for b in BINS] + ["100%"]
    return [(lbl, counts.get(lbl, 0)) for lbl in labels]


def report_stratum(name, rows):
    print(f"\n== stratum: {name} ({len(rows)} modules) ==")
    verdicts = Counter(r["verdict"] for r in rows)
    for v, n in verdicts.most_common():
        print(f"  {v:24s} {n}")
    # RQ-62-REACH increment 1: four-bucket acceptance summary.  "partial" =
    # object shipped but internal reachability helpers were skipped — callers
    # deciding off this number must know it is NOT a full accept.
    accepted = verdicts.get("ACCEPT_FULL", 0)
    partial_n = verdicts.get("ACCEPT_INTERNAL_SKIPS", 0)
    declined_n = sum(n for v, n in verdicts.items() if v.startswith("DECLINE"))
    errored = len(rows) - accepted - partial_n - declined_n
    if rows:
        print(
            f"  -> accepted {accepted} / partial {partial_n} / declined "
            f"{declined_n} / errored {errored}   (denominator: {len(rows)})"
        )
    # RQ-62-REACH increment 1: ranked blocker histogram — one PRIMARY blocker
    # per non-accepted module, ranked by modules blocked.
    blockers = Counter(
        primary_blocker(r)
        for r in rows
        if not r["verdict"].startswith("ACCEPT")
    )
    if blockers:
        print(
            "  ranked blocker histogram (one PRIMARY blocker per "
            "non-accepted module):"
        )
        for reason, n in blockers.most_common():
            print(f"    {n:4d}  {reason}")
    declines = [r for r in rows if r["verdict"].startswith("DECLINE")]
    skip_only = [r for r in rows if r["verdict"] == "DECLINE_SKIP_ONLY"]
    if declines:
        print(
            f"  -> declines: {len(declines)}; skip-only (one-function-blocks-"
            f"module, no other blocker): {len(skip_only)} "
            f"({100.0 * len(skip_only) / len(declines):.0f}% of declines)"
        )
    fracs = [
        r["fraction_compiled"]
        for r in skip_only
        if r.get("fraction_compiled") is not None
    ]
    if fracs:
        print("  distribution of fraction-compiled in skip-only declines:")
        for lbl, n in histogram(fracs):
            bar = "#" * n
            print(f"    {lbl:12s} {n:4d} {bar}")
        fracs_sorted = sorted(fracs)
        median = fracs_sorted[len(fracs_sorted) // 2]
        print(
            f"  median fraction compiled: {median:.2f}  "
            f"(mean {sum(fracs) / len(fracs):.2f} — reported for completeness; "
            f"the histogram is the number that decides)"
        )
    # Prune-then-compile (DO-178C dead-code-removal shape): per skip-only
    # decline, is every skipped function UNREACHABLE from the surviving real
    # exports (conservative call graph; call_indirect over-approximated by
    # the full indirect-target set)?  'prunable' means requesting only the
    # surviving exports is a FULL compile — no partial object at all.
    if skip_only:
        pc = Counter(str(r.get("prune_class")) for r in skip_only)
        print(
            "  prune-then-compile attribution (conservative call graph):"
        )
        legend = {
            "prunable": "no skipped fn reachable from surviving exports "
            "-> prune = FULL compile",
            "poisoned-reachable": "a surviving export needs a skipped fn "
            "-> prune alone cannot help",
            "entry-poisoned": "every real export itself skipped -> nothing "
            "to prune down to",
            "None": "unresolved (component / wasm-tools unavailable / "
            "name mapping incomplete)",
        }
        for k, n in pc.most_common():
            print(f"    {k:20s} {n:4d}  {legend.get(k, '')}")
    # #1041: an ARM --relocatable ACCEPT of a module with ACTIVE data
    # segments ships an object whose data bytes were silently dropped.
    accepts_with_data = [
        r
        for r in rows
        if r["verdict"].startswith("ACCEPT") and r.get("active_data") is True
    ]
    if accepts_with_data:
        print(
            f"  #1041 entanglement: {len(accepts_with_data)} ACCEPT(s) carry "
            f"ACTIVE data segments — on ARM --relocatable those bytes are "
            f"currently DROPPED silently; 'accept' here means the functions "
            f"compiled, NOT that the image is complete"
        )
    mod_reasons = Counter(
        r.get("reason", "?") for r in rows if r["verdict"] == "DECLINE_MODULE_LEVEL"
    )
    if mod_reasons:
        print("  module-level decline reasons (top 10):")
        for reason, n in mod_reasons.most_common(10):
            print(f"    {n:4d}  {reason}")
    # Aggregate per-FUNCTION skip reasons over the skip-only declines — the
    # "full decline set" #1017's top-12 lower bound could not see.  Counted in
    # (modules affected, functions skipped) pairs so one huge module cannot
    # masquerade as a corpus-wide cause.
    fn_reasons = Counter()
    fn_mods = Counter()
    for r in skip_only:
        for reason, n in r.get("skip_reasons", {}).items():
            fn_reasons[reason] += n
            fn_mods[reason] += 1
    if fn_reasons:
        print("  per-function skip reasons in skip-only declines")
        print("  (modules affected / functions skipped):")
        for reason, n in fn_reasons.most_common(15):
            print(f"    {fn_mods[reason]:4d} mod / {n:5d} fn  {reason}")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("roots", nargs="+", help=".wasm files or directories")
    ap.add_argument("--synth", default="target/debug/synth")
    ap.add_argument("--backend", default="arm")
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--json", help="write per-module records to this file")
    args = ap.parse_args()

    modules = discover(args.roots)
    if not modules:
        print("no .wasm modules found under the given roots", file=sys.stderr)
        return 2

    rows = []
    for path, data, digest in modules:
        rec = classify(
            args.synth,
            path,
            args.backend,
            args.timeout,
            component=is_component(data),
        )
        rec.update(
            path=str(path),
            sha256=digest[:16],
            size=len(data),
            component=is_component(data),
            active_data=has_active_data(data),
        )
        if not rec["verdict"].startswith("ACCEPT"):
            rec["primary_blocker"] = primary_blocker(rec)
        rows.append(rec)
        frac = rec.get("fraction_compiled")
        frac_s = f" frac={frac:.2f}" if frac is not None else ""
        print(
            f"[{rec['verdict']:22s}]{frac_s} "
            f"{'C' if rec['component'] else 'M'} {path}"
        )

    core = [r for r in rows if not r["component"]]
    comp = [r for r in rows if r["component"]]
    try:
        ver = subprocess.run(
            [args.synth, "--version"], capture_output=True, text=True
        ).stdout.strip()
    except OSError:
        ver = "?"
    print(
        f"\n=== census: {len(rows)} unique modules "
        f"({len(core)} core, {len(comp)} components), backend={args.backend}, "
        f"synth={ver} ==="
    )
    report_stratum("core modules", core)
    if comp:
        report_stratum("components", comp)

    if args.json:
        Path(args.json).write_text(json.dumps(rows, indent=1))
        print(f"\nper-module records written to {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
