#!/usr/bin/env python3
# ci-status: manual (measurement) — RQ-69-PROSEGATE's REFUTATION evidence, and the one script in this tree whose own conclusion is that it must not be wired: measured at 0 live true positives against 1 false positive on a correct record, so running it in CI would red honest artifacts and catch nothing. It prints counts and has no verdict. What DOES gate this class: R11 in scripts/status_evidence_check.py (wired) over the STRUCTURED status, plus the pre-tag clean-room review, which is what actually found the one historical instance.
"""RQ-69-PROSEGATE (#1319) — measure the rule R11 cannot have.

R11 (#1250) checks an artifact's STRUCTURED `status:`. It cannot see the
artifact's PROSE claiming a different one. This script measures every rule I
could construct for that class, so the refutation in RQ-69-PROSEGATE.yaml is a
number a reader can re-derive rather than a claim they must take on trust.

  python3 scripts/repro/prose_status_claim_1319.py            # measure this tree
  python3 scripts/repro/prose_status_claim_1319.py --show     # + every hit's context

It is deliberately NOT wired into CI: its conclusion is that it should not be.
"""
import argparse, glob, re, sys, yaml

# The lifecycle words a status claim can name. A claim naming anything else is
# a grammatical accident ("the status is WHAT was wrong"), not a status claim.
STATUSES = {"draft", "proposed", "approved", "implemented", "verified", "accepted"}

# STAGE 1, the naive rule: the word `status` (or `it`), a copula, a word.
# This is what you write first, before measuring anything.
NAIVE = re.compile(
    r'\bstatus\s+(?:is|was|stays|stayed|remains|remained)\s+`?([A-Za-z-]+)`?', re.I)


def artifacts():
    for f in sorted(glob.glob('artifacts/**/*.yaml', recursive=True)):
        try:
            d = yaml.safe_load(open(f))
        except Exception:
            continue
        if isinstance(d, dict):
            for a in (d.get('artifacts') or []):
                if isinstance(a, dict) and 'id' in a:
                    yield f, a


def prose_of(a):
    fields = a.get('fields') or {}
    parts = [v for k, v in a.items() if isinstance(v, str) and k != 'status']
    parts += [v for k, v in fields.items() if isinstance(v, str) and k != 'status']
    return "\n".join(parts)


# This record quotes the false positives in order to explain them, so the naive
# stage flags it too — and every edit to its prose moves the number it publishes.
# It is reported SEPARATELY rather than folded in, so the measurement is stable
# under rewording. The self-hit count is a finding, not noise to suppress.
SELF = "RQ-69-PROSEGATE"


def measure(show=False):
    blocks = 0
    stages = {"naive": [], "real-status": [], "not-quoted": []}
    for _f, a in artifacts():
        blocks += 1
        structured = str(a.get('status', '')).strip().lower()
        prose = prose_of(a)
        for m in NAIVE.finditer(prose):
            claimed = m.group(1).lower()
            if claimed == structured:
                continue                      # prose agrees; nothing to report
            ctx = prose[max(0, m.start() - 120):m.end() + 60].replace("\n", " ")
            hit = (a['id'], structured, claimed, ctx)
            stages["naive"].append(hit)

            # STAGE 2: the claim must name a REAL status. Kills the grammatical
            # accidents, and is principled — not tuned to any record.
            if claimed not in STATUSES:
                continue
            stages["real-status"].append(hit)

            # STAGE 3: ignore reported speech. A record quoting its own earlier
            # sentence in order to CORRECT it is not claiming that status now.
            before = prose[max(0, m.start() - 60):m.start()]
            if "'" in before or '"' in before or '“' in before:
                continue
            stages["not-quoted"].append(hit)
    return blocks, stages


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--show', action='store_true')
    args = ap.parse_args()
    blocks, stages = measure()
    print(f"artifact blocks scanned: {blocks}")
    for name in ("naive", "real-status", "not-quoted"):
        hits = [h for h in stages[name] if h[0] != SELF]
        selfhits = [h for h in stages[name] if h[0] == SELF]
        ids = sorted({h[0] for h in hits})
        print(f"{name:14s} hits={len(hits):3d}  artifacts={len(ids)}  "
              f"(+{len(selfhits)} self)  {ids}")
        if args.show:
            for h in hits + selfhits:
                tag = "  [SELF]" if h[0] == SELF else ""
                print(f"    {h[0]}{tag}: structured={h[1]} claimed={h[2]}")
                print(f"      …{h[3]}…")
    return 0


if __name__ == '__main__':
    sys.exit(main())
