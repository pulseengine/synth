#!/usr/bin/env python3
"""RQ-57-MCDC (#912) — score witness MC/DC over synth's OWN decision logic.

Why this script exists rather than reading a percentage off `witness report`
-----------------------------------------------------------------------------
Three separate things make the raw module-level number unusable as a gate, and
each of them is the "instrument measuring the wrong surface" class this repo
keeps finding:

1.  A `wasm32-wasip1` link drags in wasi-libc (`malloc.c`, `stpcpy.c`, …) and
    Rust `std` (`panicking.rs`, `core::fmt`, …). Those contribute THOUSANDS of
    never-evaluated conditions. `3/770 full MC/DC` says almost nothing about
    synth. Scoring must be restricted to synth's own functions.

2.  witness's `source_file` / `source_line` are NOT reliable for scoping. They
    are DWARF line attributions of INLINED code, so `resolve_owner`'s decision
    reports as `static_data_addr.rs:355` (the decision is at :274) and
    `validate_reloc_resolutions`' decisions report as `backend.rs:480` and
    `num.rs:85` — files in other crates entirely. That is upstream
    pulseengine/witness#179. `source_file` is also only a BASENAME, so six
    crates' `backend.rs` collide.

    The manifest's per-branch `function_name` IS reliable: it is the Rust
    symbol of the function the branch physically lives in. This script scopes
    and reports by DEMANGLED FUNCTION, never by file, and prints the reported
    line only as an advisory.

3.  A ratio cannot notice a DELETED condition — removing `|| rs2 == Reg::RA`
    from a predicate removes a gap row and the percentage IMPROVES. So the
    floors below are COUNTS (conditions present, conditions proved) as well as
    a gap ceiling.

Usage:
    scripts/mcdc_gate.py <mcdc-run-dir>      # dir written by scripts/mcdc_run.sh
    scripts/mcdc_gate.py <dir> --report-only # print, never fail
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# ───────────────────────────────────────────────────────────────────────────
# THE SCORED SURFACE — "the right parts" (#912)
#
# Not every decision in synth is worth an MC/DC obligation. These three module
# prefixes are the predicate classes where a MISSED CONDITION HAS ALREADY
# SHIPPED A SOUNDNESS BUG IN THIS REPO:
#
#   * static_data_addr  — validator accept/reject. VCR-VER-003 (#777). Its
#                         whole job is to hard-error the #757 wrong-segment
#                         miscompile; a missed condition green-washes it.
#                         Also carries the #798 served-image gate.
#   * alloc_validator   — validator accept/reject. VCR-RA-003 (#815). #871
#                         shipped an unsaved-`ra` miscompile: a non-leaf
#                         function returning into its own call site. The fix
#                         WAS a condition added to the save-set predicate.
#   * riscv backend     — guard emission. The #953/#959 sentinel-vs-value
#                         class, three consecutive releases: `mem_size == 0`
#                         was EXEMPT from the power-of-two mask gate, so
#                         `(memory 0)` emitted an identity mask (0-1 =
#                         0xFFFF_FFFF) and every access ran unmasked.
#
# EXPLICITLY OUT OF SCOPE (named, not hidden — see #912 for the argument):
#   * synth_synthesis::instruction_selector — 225 boolean-operator lines; a
#     lane-sized surface of its own, and its decisions are already gated by
#     ~30 execution differentials.
#   * the aarch64 `bounds_check` / `form_ea` closures — reachable only by
#     driving a whole function body through the selector; named residual.
#   * synth_backend::wcet* — the decline predicates are match-dispatch
#     (`scan_for_decline`: 1 boolean-operator line in 1061), so most of that
#     surface has no compound decision to measure.
SCORED_PREFIXES = (
    "synth_core::static_data_addr::",
    "synth_backend_riscv::alloc_validator::",
    "synth_backend_riscv::backend::",
)

# ───────────────────────────────────────────────────────────────────────────
# DECLARED FLOORS — measured, not guessed (see #912 / the PR body for the run
# these came from). Raise them when a lane adds rows; never lower them to make
# a red gate green.
#
# MEASURED BASELINE (witness 0.28.0, wasm32-wasip1, 56 rows):
#   20 scored decisions / 144 conditions / 63 proved / 31 gap / 50 dead
#   3 decisions at FULL MC/DC (is_ret, sp_slot_load, build_options)
# The floors ARE those numbers. A floor set below what was measured is the
# half-value-floor defect this hub already found elsewhere; a floor set above
# is a red gate nobody can fix.
#
# ci-checks: mcdc scored decisions >= 20
# ci-checks: mcdc scored conditions >= 144
# ci-checks: mcdc scored conditions proved >= 63
# ci-checks: mcdc fully-proved decisions >= 3
# ci-checks: mcdc dead conditions <= 50
FLOOR_DECISIONS = 20
FLOOR_CONDITIONS = 144
FLOOR_PROVED = 63
FLOOR_FULL_MCDC_DECISIONS = 3
# DEAD is CEILINGED, not ignored. 50 of the 144 scored conditions are never
# evaluated — 40 of them in `is_straight_line`, whose match arms cover RV32
# opcodes the row set does not construct. That is an honest residual, but an
# UNFLOORED residual is how a number rots: a change that stopped reaching the
# segment barriers would raise `dead`, lower nothing else, and pass. It is also
# a third potency surface — mutation (a) moved dead 50 -> 52.
CEILING_DEAD = 50


def demangle(sym: str) -> str:
    """Rust legacy (`_ZN…E`) symbol -> `crate::module::fn`.

    Only the path components are needed; the trailing `17h<hash>` disambiguator
    and any generic arguments are dropped. Falls back to the raw symbol so an
    unrecognised mangling is visible rather than silently dropped.
    """
    m = re.match(r"^_ZN(.*)E$", sym)
    if not m:
        return sym
    body, parts, i = m.group(1), [], 0
    while i < len(body):
        j = i
        while j < len(body) and body[j].isdigit():
            j += 1
        if j == i:
            break
        n = int(body[i:j])
        seg = body[j : j + n]
        i = j + n
        if re.fullmatch(r"h[0-9a-f]{16}", seg):
            continue
        parts.append(seg)
    return "::".join(parts) if parts else sym


def load(run_dir: Path):
    manifest = json.loads((run_dir / "instrumented.wasm.witness.json").read_text())
    report = json.loads((run_dir / "report.json").read_text())
    return manifest, report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_dir", type=Path)
    ap.add_argument("--report-only", action="store_true")
    args = ap.parse_args()

    manifest, report = load(args.run_dir)
    if report.get("schema") != "https://pulseengine.eu/witness-mcdc/v3":
        print(f"note: unexpected report schema {report.get('schema')!r}", file=sys.stderr)

    branch_fn = {b["id"]: demangle(b.get("function_name", "")) for b in manifest["branches"]}

    # A decision belongs to a function when its conditions' branches do. A
    # decision straddling two functions (inlining) is attributed to the one
    # owning the most conditions, and flagged.
    per_fn: dict[str, dict] = {}
    scored_decisions = []
    for dec in report["decisions"]:
        owners: dict[str, int] = {}
        for c in dec["conditions"]:
            owners[branch_fn.get(c["branch_id"], "?")] = (
                owners.get(branch_fn.get(c["branch_id"], "?"), 0) + 1
            )
        owner = max(owners, key=lambda k: owners[k])
        if not owner.startswith(SCORED_PREFIXES):
            continue
        scored_decisions.append((owner, dec, len(owners) > 1))
        st = per_fn.setdefault(
            owner, {"decisions": 0, "full": 0, "proved": 0, "gap": 0, "dead": 0}
        )
        st["decisions"] += 1
        statuses = [c["status"] for c in dec["conditions"]]
        for s in statuses:
            st[s if s in ("proved", "gap", "dead") else "gap"] += 1
        if statuses and all(s == "proved" for s in statuses):
            st["full"] += 1

    tot = {k: sum(v[k] for v in per_fn.values()) for k in ("decisions", "full", "proved", "gap", "dead")}
    conditions = tot["proved"] + tot["gap"] + tot["dead"]

    print("MC/DC over synth's own decision logic (RQ-57-MCDC, #912)")
    print(f"  witness {report.get('witness_version')}  schema {report.get('schema')}")
    print(f"  attribution_source: {manifest.get('attribution_source')} "
          f"(function names; file:line is unreliable — witness#179)")
    print()
    print(f"{'function':<62}{'dec':>5}{'full':>6}{'cond':>6}{'prov':>6}{'gap':>5}{'dead':>6}")
    print("-" * 96)
    for fn in sorted(per_fn):
        v = per_fn[fn]
        c = v["proved"] + v["gap"] + v["dead"]
        short = fn if len(fn) <= 60 else "…" + fn[-59:]
        print(f"{short:<62}{v['decisions']:>5}{v['full']:>6}{c:>6}{v['proved']:>6}{v['gap']:>5}{v['dead']:>6}")
    print("-" * 96)
    print(f"{'TOTAL':<62}{tot['decisions']:>5}{tot['full']:>6}{conditions:>6}"
          f"{tot['proved']:>6}{tot['gap']:>5}{tot['dead']:>6}")
    print()

    # The gap rows themselves — the point of the exercise. A percentage without
    # these is the thing #912 spent six releases mistaking for a result.
    print("GAP ROWS (condition proved by no unique-cause / masking pair):")
    n_gap = 0
    for owner, dec, straddles in scored_decisions:
        gaps = [c for c in dec["conditions"] if c["status"] == "gap"]
        if not gaps:
            continue
        n_gap += len(gaps)
        flag = "  [inlined across functions]" if straddles else ""
        print(f"  {owner}  (decision #{dec['id']}, reported at "
              f"{dec['source_file']}:{dec['source_line']}){flag}")
        for c in gaps:
            gc = c.get("gap_closure") or {}
            print(f"      c{c['index']}: need a row {gc.get('evaluated')} "
                  f"with outcome != {gc.get('outcome_must_differ_from')} "
                  f"(pair with row {gc.get('paired_with_row')})")
    if n_gap == 0:
        print("  (none)")
    print()

    fails = []
    if tot["decisions"] < FLOOR_DECISIONS:
        fails.append(f"scored decisions {tot['decisions']} < floor {FLOOR_DECISIONS}")
    if conditions < FLOOR_CONDITIONS:
        fails.append(f"scored conditions {conditions} < floor {FLOOR_CONDITIONS}")
    if tot["proved"] < FLOOR_PROVED:
        fails.append(f"proved conditions {tot['proved']} < floor {FLOOR_PROVED}")
    if tot["full"] < FLOOR_FULL_MCDC_DECISIONS:
        fails.append(
            f"fully-proved decisions {tot['full']} < floor {FLOOR_FULL_MCDC_DECISIONS}"
        )
    if tot["dead"] > CEILING_DEAD:
        fails.append(f"dead conditions {tot['dead']} > ceiling {CEILING_DEAD}")

    if fails and not args.report_only:
        for f in fails:
            print(f"FAIL: {f}")
        print()
        print("A DROP in `scored conditions` means a condition was deleted from a")
        print("gated predicate — that is the case a ratio-only floor cannot see, and")
        print("it is why this gate counts. Do not lower a floor to go green.")
        return 1
    for f in fails:
        print(f"(report-only) would FAIL: {f}")
    print("PASS: all MC/DC floors met")
    return 0


if __name__ == "__main__":
    sys.exit(main())
