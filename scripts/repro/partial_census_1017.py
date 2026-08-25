#!/usr/bin/env python3
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

SKIP_WARN_RE = re.compile(r"warning: (\d+) of (\d+) functions were skipped")
SKIP_REASON_RE = re.compile(r"warning: skipping function '[^']+': (.+)")
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


def classify(synth, module, backend, timeout):
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
        return {
            "verdict": "DECLINE_SKIP_ONLY",
            "skipped": skipped or None,
            "total": total,
            "fraction_compiled": 0.0,
            "reason": "all functions skipped (nothing to emit)",
            "skip_reasons": dict(skip_reasons(err)),
        }
    rc2, err2 = run_synth(
        synth, module, backend, ["--allow-skipped-exports"], timeout
    )
    if rc2 == 0:
        m2 = SKIP_WARN_RE.search(err2)
        if m2:
            s2, t2 = int(m2.group(1)), int(m2.group(2))
            return {
                "verdict": "DECLINE_SKIP_ONLY",
                "skipped": s2,
                "total": t2,
                "fraction_compiled": (t2 - s2) / t2,
                "skip_reasons": dict(skip_reasons(err2)),
            }
        # Declined plain but clean with the flag and no skip warning: should
        # not happen; surface it rather than misfile it.
        return {"verdict": "ANOMALY", "reason": first_error_line(err)}
    return {"verdict": "DECLINE_MODULE_LEVEL", "reason": first_error_line(err)}


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
        rec = classify(args.synth, path, args.backend, args.timeout)
        rec.update(
            path=str(path),
            sha256=digest[:16],
            size=len(data),
            component=is_component(data),
        )
        rows.append(rec)
        frac = rec.get("fraction_compiled")
        frac_s = f" frac={frac:.2f}" if frac is not None else ""
        print(
            f"[{rec['verdict']:22s}]{frac_s} "
            f"{'C' if rec['component'] else 'M'} {path}"
        )

    core = [r for r in rows if not r["component"]]
    comp = [r for r in rows if r["component"]]
    print(
        f"\n=== census: {len(rows)} unique modules "
        f"({len(core)} core, {len(comp)} components), backend={args.backend} ==="
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
