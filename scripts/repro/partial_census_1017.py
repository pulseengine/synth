#!/usr/bin/env python3
# ci-status: wired — `--self-test` (RQ-64-HISTOGRAM, #1159) runs in the required `claim-check` job: a hermetic check of the INSTRUMENT (the numeric-payload mask on the two fragmenting shapes observed in the wild, the printed-rows sum invariant and its negative control) that needs no corpus and asserts nothing about synth. The census modes themselves are still a local MEASUREMENT (RQ-59-PARTIALCENSUS #1017: no expected value, no verdict about the compiler, over a real-world corpus CI does not carry; the behaviour they measure is gated by the wired decline-honesty oracles). This file was `manual (measurement)` until the self-test gave it a verdict CI can fail on — the note beside the manual ceiling in claims.yaml named that as exactly the moment it must be wired.
# ci-checks: stdout /^self-test OK: (\d+) assertions/ >= 14
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
  f. (RQ-64-HISTOGRAM, #1159) NUMERIC payloads — hex AND decimal immediates,
     offsets, sizes — are masked by the one normalization every reason passes
     through, so `immediate 0x624` and `immediate 0x5dc` are ONE row (before
     this, the decimal collapsed and the hex did not, and a cause with a
     varying payload was systematically UNDER-RANKED against one without —
     in the histogram v0.63 was scoped from).  And every ranked view now
     ASSERTS on each run that its printed rows sum to the modules they rank
     (a collapse that loses rows is worse than one that fragments them);
     `--self-test` exercises the mask on the two shapes observed in the wild
     and proves the sum check can fail (negative control) — and it is WIRED
     (claim-check job), because a self-test that never runs guards nothing.
     The assertion is about the REPORT's integrity, never about synth: the
     census modes still carry no expected value and no verdict on the
     compiler.

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
    # Collapse per-instance NUMERIC payloads (indices, offsets, sizes,
    # immediates) so reasons bucket by CAUSE, not by the value that happened
    # to trigger it.  This is THE numeric mask — it runs on every reason
    # (per-function skip reasons AND module-level errors) before any other
    # collapse, so a payload class added here is masked on every path.
    #
    # Hex FIRST (#1159 / RQ-64-HISTOGRAM): `\b\d+\b` alone leaves `0x5dc`
    # intact because the `x` glues the digits into one word, which is exactly
    # how `immediate 0x5dc (1500)` printed as `immediate 0x5dc (N)` — the
    # decimal collapsed, the hex not — and one cause fragmented into one row
    # per distinct immediate, under-ranking it against every cause with no
    # varying payload.  Hex and decimal collapse to DIFFERENT tokens
    # (`0xN` / `N`) so the message shape stays readable; a bare `0x` prefix
    # with no digits is not a number and is left alone.  Identifiers that
    # merely CONTAIN digits (`i32`, `R11`, `func_25`, `RV32`, `imm12`) are
    # not word-bounded numbers and survive, so op/register/function identity
    # — which IS cause identity — is never masked.  The same line is drawn
    # for REFERENCE identifiers a message carries as literal text — an issue
    # (`#1102`), a spec section (`§4.5.5`), a roadmap id (`VCR-MEM-002`):
    # they are format-string constants, so they cannot vary per instance and
    # masking them can only lose identity, never merge a fragment.  One
    # tokenizing pass: a reference (`#`/`§` followed by a dotted number, or
    # `<letter>-<digits>`) is kept whole; a hex literal becomes `0xN`; a bare
    # decimal becomes `N`.  A NEGATIVE payload like ` -4` still masks because
    # the hyphen there follows whitespace, not a letter.  The mask is
    # idempotent (`0xN` and `N` match nothing), so re-normalizing an already-
    # normalized reason is the identity — which is what lets a --json
    # record's `skip_reasons` (normalized at capture) be re-ranked offline by
    # the same function without re-fragmenting.
    reason = NUMERIC_PAYLOAD_RE.sub(_mask_numeric, reason)
    return reason.strip()[:160]


NUMERIC_PAYLOAD_RE = re.compile(
    r"(?P<ref>[#§]\d[\d.]*|[A-Za-z]-\d+)"
    r"|(?P<hex>\b0[xX][0-9A-Fa-f]+\b)"
    r"|(?P<dec>\b\d+\b)"
)


def _mask_numeric(m):
    if m.group("ref") is not None:
        return m.group("ref")
    return "0xN" if m.group("hex") is not None else "N"
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


def classify(synth, module, backend, timeout, component=False, extra=None):
    rc, err = run_synth(synth, module, backend, list(extra or []), timeout)
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
    Applied AFTER normalize_reason, which is THE numeric mask (decimal AND
    hex payloads already collapsed to `N` / `0xN`, #1159) — this function
    collapses only the LIST-shaped payloads the numeric mask cannot, and is
    reached only by module-level reasons, so a new payload CLASS belongs in
    normalize_reason unless it is list-shaped.  The full per-module text is
    preserved in the --json records."""
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


def module_reason(rec):
    """The normalized, list-collapsed MODULE-LEVEL error of a record: ONE
    pipeline (strip the CLI's `Error: ` wrapper, mask numeric payloads,
    collapse instance lists) so every ranked view of module-level reasons —
    the primary-blocker histogram and the module-level top-10 — buckets
    identically.  Two copies of this chain would be the second-source-of-
    truth shape #1159 was filed against."""
    reason = rec.get("reason", "?")
    if reason.startswith("Error: "):
        reason = reason[len("Error: "):]
    return collapse_instance_lists(normalize_reason(reason))


def print_ranked(blockers, expected, what, top=None, width=None):
    """Print a ranked histogram AND assert the SUM INVARIANT on what was
    PRINTED (#1159 / RQ-64-HISTOGRAM): the rows a reader sees must sum to
    the number of modules they rank.  A collapse that LOSES rows is worse
    than one that fragments them — fragmentation under-ranks a cause, loss
    hides it — so this is checked on every run, not observed once.

    The invariant is stated over the PRINTED rows, not the Counter (a Counter
    over one key per module sums by construction, so asserting that would be
    a check that cannot fail): a `top` cut prints its remainder as an
    explicit row so the visible sum still closes, and a `width` cut under
    which two DISTINCT causes would print identically is refused by printing
    those rows in full (the reader would otherwise see what looks like one
    fragmented cause, or one cause where there are two).  Exit 3 on
    violation: a histogram whose rows do not sum is not a measurement, it is
    a defect in the instrument.  This asserts nothing about synth and pins
    no expected value, so the script stays a MEASUREMENT (ci-status:
    manual) — the check is on the report, not on the compiler."""
    total = sum(blockers.values())
    bad = [k for k in blockers if not isinstance(k, str) or not k.strip()]
    ranked = blockers.most_common()
    shown = ranked if top is None else ranked[:top]
    rest = [] if top is None else ranked[top:]
    labels = [k if width is None else k[:width] for k, _ in shown]
    if len(set(labels)) != len(labels):
        labels = [k for k, _ in shown]  # the width cut collided: print in full
    printed = 0
    for (_, n), label in zip(shown, labels):
        print(f"    {n:4d}  {label}")
        printed += n
    if rest:
        rest_n = sum(n for _, n in rest)
        print(
            f"    {rest_n:4d}  (+{len(rest)} more rows below the top-{top} "
            f"cut — counted so the rows still sum)"
        )
        printed += rest_n
    if bad or printed != total or total != expected:
        print(
            f"HISTOGRAM SUM INVARIANT VIOLATED ({what}): printed rows sum to "
            f"{printed}, counter to {total}, modules ranked {expected}"
            + (f"; empty bucket keys: {bad!r}" if bad else ""),
            file=sys.stderr,
        )
        sys.exit(3)
    print(
        f"    ---- {len(shown) + (1 if rest else 0)} rows sum to {printed} "
        f"= {expected} modules ranked (sum invariant OK)"
    )


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
        reason = module_reason(rec)
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
    non_accepted = [r for r in rows if not r["verdict"].startswith("ACCEPT")]
    blockers = Counter(primary_blocker(r) for r in non_accepted)
    if blockers:
        print(
            "  ranked blocker histogram (one PRIMARY blocker per "
            "non-accepted module):"
        )
        print_ranked(blockers, len(non_accepted), f"{name}: blocker histogram")
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
    # Same pipeline as the histogram (module_reason): this list is ALSO a
    # ranking, and it printed RAW reasons until #1159 — so it fragmented on
    # every payload the histogram had already learned to collapse.
    mod_level = [r for r in rows if r["verdict"] == "DECLINE_MODULE_LEVEL"]
    mod_reasons = Counter(module_reason(r) for r in mod_level)
    if mod_reasons:
        print("  module-level decline reasons (top 10):")
        print_ranked(mod_reasons, len(mod_level),
                     f"{name}: module-level reasons", top=10)
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



# ---------------------------------------------------------------------------
# RQ-63-LADDER (v0.63): acceptance is a function of INVOCATION, not one number.
#
# v0.62's census reported a single figure per backend measured with ONE fixed
# invocation. That under-reports: `--embedder-data-init` / `--embedder-global-init`
# are an ACKNOWLEDGEMENT of an embedder obligation (the #952/#1041/#1052
# honest-refusal pattern), not a feature switch, and modules behind them compile
# TODAY. So the honest report is a LADDER whose rungs are named and reported
# SEPARATELY — never summed into one rate.
#
# The rungs are deliberately NOT all "accepts":
#   default        no flags — what a consumer gets with no knowledge
#   embedder-ack   the consumer acknowledges an embedder obligation
#   allow-skipped  CATEGORICALLY DIFFERENT: a PARTIAL object is a third state,
#                  not a pass. Counted, reported, and never folded into accepts.
#   no-optimize    selector-path difference only
#   NEVER          declines at every rung; attributed by primary_blocker()
# ---------------------------------------------------------------------------
LADDER_RUNGS = [
    ("default", []),
    ("embedder-ack", ["--embedder-data-init", "--embedder-global-init"]),
    ("allow-skipped", ["--embedder-data-init", "--embedder-global-init",
                       "--allow-skipped-exports"]),
    # STRUCTURALLY INERT UNDER THIS BASE INVOCATION, and labelled as such
    # rather than deleted, because a rung that cannot move is exactly the
    # "checker that cannot fail" class this release spent its scope finding —
    # here in a MEASUREMENT harness rather than a CI gate.
    # Every rung runs `--relocatable` (see run_synth), and
    # arm_backend.rs:990 selects the direct path on
    # `no_optimize || relocatable || ...` — so `--no-optimize` changes nothing
    # on ARM under this base. synth-backend-riscv and synth-backend-aarch64
    # never read `no_optimize` at all (one selector each). The optimized ARM
    # selector is therefore NEVER REACHED by this ladder, and "+0" is the only
    # value this rung can ever report.
    # Consequence, stated so it is not inferred away: NOTHING about the two
    # #197 selector paths follows from this rung. Measuring that needs a run
    # WITHOUT `--relocatable`, which is a different ABI and a different
    # measurement.
    ("no-optimize (INERT)", ["--embedder-data-init", "--embedder-global-init",
                             "--allow-skipped-exports", "--no-optimize"]),
]
# Rungs whose flags cannot change the outcome under the base invocation. The
# report marks them so a reader never reads "+0" as a measured negative.
INERT_RUNGS = {"no-optimize (INERT)"}
ACCEPT_VERDICTS = {"ACCEPT_FULL", "ACCEPT_INTERNAL_SKIPS"}


def ladder_classify(synth, module, backend, timeout, component=False):
    """First rung at which the module is accepted, or NEVER.

    Returns (rung_name, record). The record is the classify() result at the
    rung that accepted, or at the LAST rung when none did — so the NEVER
    bucket's primary_blocker() reflects the most permissive invocation, which
    is the honest attribution: a blocker that survives every flag is a real
    capability gap, not a missing acknowledgement."""
    last = None
    for name, extra in LADDER_RUNGS:
        rec = classify(synth, module, backend, timeout,
                       component=component, extra=extra)
        last = rec
        if rec.get("verdict") in ACCEPT_VERDICTS:
            return name, rec
        if rec.get("verdict") == "TIMEOUT":
            return "TIMEOUT", rec
    return "NEVER", last


def report_ladder(backend, rows):
    """Rungs printed SEPARATELY with the denominator beside them (#1095 rule),
    and the NEVER bucket broken down by root cause."""
    total = len(rows)
    order = [n for n, _ in LADDER_RUNGS] + ["NEVER", "TIMEOUT"]
    counts = Counter(r["rung"] for r in rows)
    print(f"\n=== {backend}: acceptance LADDER over {total} modules ===")
    print("    (rungs are SEPARATE, never summed — `allow-skipped` yields a")
    print("     PARTIAL object, which is a third state and not an accept)")
    cumulative = 0
    for name in order:
        n = counts.get(name, 0)
        if name in ("NEVER", "TIMEOUT"):
            print(f"  {name:<14} {n:>4}          of {total}")
            continue
        # Cumulative is ACCEPTS ONLY. `allow-skipped` yields PARTIAL objects
        # and the inert rung cannot move, so folding either into a running
        # percentage would contradict the banner two lines above — which the
        # v0.63 cold review caught this harness doing.
        counts_as_accept = name not in ("allow-skipped",) and name not in INERT_RUNGS
        if counts_as_accept:
            cumulative += n
        pct = 100.0 * cumulative / total if total else 0.0
        note = ("  <- partial objects, NOT accepts; excluded from cum"
                if name == "allow-skipped" else "")
        if name in INERT_RUNGS:
            note = ("  <- INERT: cannot move under --relocatable; +0 is the "
                    "only possible value, NOT a measured negative")
        print(f"  {name:<14} {n:>4}  (cum {cumulative:>4} = {pct:4.1f}%) of {total}{note}")
    never = [r for r in rows if r["rung"] == "NEVER"]
    if never:
        print(f"\n  NEVER bucket ({len(never)}) by primary blocker — the real capability gaps:")
        blockers = Counter(primary_blocker(r["record"]) or "(unattributed)"
                           for r in never)
        # The top-12 cut and the 88-column width are DISPLAY choices; the
        # sum invariant (#1159) is asserted over what is printed, so the cut
        # carries an explicit remainder row and a width collision prints in
        # full rather than showing two causes as one.
        print_ranked(blockers, len(never), f"{backend}: NEVER bucket",
                     top=12, width=88)


def self_test():
    """`--self-test`: the instrument's own checks (#1159 / RQ-64-HISTOGRAM),
    WIRED in the required `claim-check` job (see the ci-status / ci-checks
    header).  (1) the two fragmenting shapes observed in the wild collapse to
    ONE key — and, RED-FIRST kept permanently, are DISTINCT under the
    pre-#1159 rule, so the merge check is known to discriminate; (2) the mask
    is idempotent; (3) digit-bearing IDENTIFIERS survive, so op/register/
    function identity is never masked; (4) list collapse still composes after
    the numeric mask; (5) a NEGATIVE control — the sum invariant must be able
    to fail, or it is not a check — and a top-cut positive control whose
    remainder row closes the sum.  Runs no synth, needs no corpus.  Prints the
    COUNT of assertions executed; the `ci-checks: stdout` floor binds that
    count, so a self-test whose body stopped running cannot pass green."""
    import contextlib
    import io

    n = [0]

    def check(cond, what):
        n[0] += 1
        if not cond:
            raise AssertionError(f"self-test assertion {n[0]} FAILED: {what}")

    rot = ("encode_operand2: immediate {} ({}) is not an ARM32 rotated "
           "immediate — the selector must materialize large constants via "
           "MOVW/MOVT")
    raw_a, raw_b = rot.format("0x624", 1572), rot.format("0x5dc", 1500)
    # (1) RED-FIRST, permanent: the PRE-#1159 rule (bare decimals only) keeps
    # these two shapes APART.  If a future edit removes the hex payload from
    # the shapes, this fails and the merge check below is known to have gone
    # vacuous — a self-test that passes on both the broken and the fixed mask
    # would be the same defect one level down.
    def old_rule(s):
        return re.sub(r"\b\d+\b", "N", s)
    check(old_rule(raw_a) != old_rule(raw_b),
          "pre-#1159 rule no longer fragments the two wild shapes")
    a, b = normalize_reason(raw_a), normalize_reason(raw_b)
    check(a == b == rot.format("0xN", "N"), f"hex shapes did not merge: {a!r} vs {b!r}")
    check(normalize_reason(a) == a, "numeric mask is not idempotent")
    check(normalize_reason("0xDEADbeef at 0X10 vs 0x") == "0xN at 0xN vs 0x",
          "hex case / bare-prefix handling")
    ident = "i32.add: R11 clobbered in func_25 on RV32 (imm12) via 0x"
    check(normalize_reason(ident) == ident,
          f"identifier masked: {normalize_reason(ident)!r}")
    check(normalize_reason("offset 4096 (0x1000) exceeds imm12 at #952")
          == "offset N (0xN) exceeds imm12 at #952",
          "decimal + hex payload beside an issue reference")
    refs = "multi-memory (#406) per WASM Core §4.5.5 (VCR-MEM-002 phase 1)"
    check(normalize_reason(refs)
          == "multi-memory (#406) per WASM Core §4.5.5 (VCR-MEM-002 phase N)",
          f"reference identifiers: {normalize_reason(refs)!r}")
    check(normalize_reason("offset -4 and 7-3") == "offset -N and N-N",
          "negative / arithmetic payloads")
    lst = normalize_reason(
        "Error: 3 retained function(s) relocate against DECLINED: 'func_25' "
        "-> 'func_20' (0x10)")
    check(collapse_instance_lists(lst)
          == "Error: N retained function(s) relocate against DECLINED: "
             "<symbol list>",
          f"list collapse after numeric mask: {collapse_instance_lists(lst)!r}")

    # (5) negative controls: the sum invariant must EXIT 3 on a violation.
    def expect_exit3(counter, expected, what):
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                print_ranked(counter, expected, what)
        except SystemExit as e:
            check(e.code == 3, f"{what}: exit {e.code}, not 3")
        else:
            check(False, f"{what}: sum invariant did not fire")

    expect_exit3(Counter({"a": 1, "b": 1}), 3,
                 "self-test negative (2 rows for 3 modules)")
    expect_exit3(Counter({"": 2}), 2, "self-test negative (empty bucket key)")
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        print_ranked(Counter({"a": 3, "b": 2, "c": 1}), 6, "self-test cut",
                     top=1, width=1)
    out = buf.getvalue()
    check("(+2 more rows below the top-1 cut" in out,
          f"remainder row missing under a top cut: {out!r}")
    check("2 rows sum to 6 = 6 modules ranked" in out,
          f"printed sum did not close under a top cut: {out!r}")
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        print_ranked(Counter({"same-prefix-A": 1, "same-prefix-B": 1}), 2,
                     "self-test width collision", width=8)
    check("same-prefix-A" in buf.getvalue(),
          f"width collision not printed in full: {buf.getvalue()!r}")
    print(f"self-test OK: {n[0]} assertions — numeric mask (hex+decimal), "
          "red-first discriminator, idempotence, identifier survival, list "
          "collapse, sum-invariant negative + cut controls")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("roots", nargs="*", help=".wasm files or directories")
    ap.add_argument("--self-test", action="store_true",
                    help="RQ-64-HISTOGRAM: run the instrument's own checks "
                         "(numeric mask, sum-invariant negative control); "
                         "runs no synth, needs no corpus")
    ap.add_argument("--synth", default="target/debug/synth")
    ap.add_argument("--backend", default="arm")
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--json", help="write per-module records to this file")
    ap.add_argument("--ladder", action="store_true",
                    help="RQ-63-LADDER: report the flag-aware acceptance "
                         "ladder (rungs reported separately, NEVER bucket "
                         "attributed by root cause) instead of the #1017 "
                         "single-invocation census")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not args.roots:
        ap.error("at least one ROOT is required (or --self-test)")
    modules = discover(args.roots)
    if not modules:
        print("no .wasm modules found under the given roots", file=sys.stderr)
        return 2

    if args.ladder:
        # RQ-63-LADDER. Deliberately a SEPARATE path: the #1017 census below is
        # exact about ONE invocation and is cited as such, so the ladder must
        # not silently change what that census reports.
        lrows = []
        for path, data, digest in modules:
            rung, rec = ladder_classify(
                args.synth, path, args.backend, args.timeout,
                component=is_component(data),
            )
            rec.update(path=str(path), sha256=digest[:16],
                       component=is_component(data))
            lrows.append({"path": str(path), "rung": rung,
                          "component": is_component(data), "record": rec})
        core = [r for r in lrows if not r["component"]]
        comp = [r for r in lrows if r["component"]]
        report_ladder(f"{args.backend} / core", core)
        if comp:
            report_ladder(f"{args.backend} / components", comp)
        report_ladder(f"{args.backend} / ALL", lrows)
        if args.json:
            with open(args.json, "w") as fh:
                json.dump([{k: v for k, v in r.items() if k != "record"}
                           | {"verdict": r["record"].get("verdict"),
                              "primary_blocker": primary_blocker(r["record"])
                              if r["rung"] == "NEVER" else None}
                           for r in lrows], fh, indent=1)
            print(f"\nper-module ladder records written to {args.json}")
        return 0

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
