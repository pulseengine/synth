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


# RQ-77-PROSEBLIND (v0.77): THE POSITIVE CONTROL, which this census lacked.
#
# Every stage above measures FALSE positives on the live tree. None of them could
# show that any stage catches the defect it exists for — because the one real
# instance was corrected in v0.68.0 and is no longer in the working tree. A
# separation experiment with no positive control cannot distinguish "no rule
# separates the classes" from "no rule fires at all", and those have opposite
# consequences.
#
# So the control comes from git history: at 3e6a520b, RQ-68-CLAIMSDRIFT read
# "Status stays `proposed`" while structurally `implemented`; the v0.68.0 release
# commit bd81bc8c corrected it to "Status is `implemented`". A stage is only
# INFORMATIVE if it reds there and stays green on the live narratives.
CONTROL = ("3e6a520b", "artifacts/release-v0.68/RQ-68-CLAIMSDRIFT.yaml")


def control_text():
    """The historical false claim. REFUSES rather than returning nothing."""
    import subprocess
    r = subprocess.run(["git", "show", f"{CONTROL[0]}:{CONTROL[1]}"],
                       capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.strip():
        sys.exit(f"REFUSE: cannot read the positive control {CONTROL[0]}:{CONTROL[1]}. "
                 f"Without it every 'green' below is indistinguishable from a rule "
                 f"that never fires ({r.stderr.strip()[:100]})")
    return r.stdout


def stage_verdicts(raw_or_parsed_text, structured):
    """Which stages fire on ONE artifact's text? Returns a dict of stage -> bool."""
    out = {"naive": False, "real-status": False, "not-quoted": False}
    for m in NAIVE.finditer(raw_or_parsed_text):
        claimed = m.group(1).lower()
        if claimed == structured:
            continue
        out["naive"] = True
        if claimed not in STATUSES:
            continue
        out["real-status"] = True
        before = raw_or_parsed_text[max(0, m.start() - 60):m.start()]
        if "'" in before or '"' in before or '\u201c' in before:
            continue
        out["not-quoted"] = True
    return out


def verify():
    """Does any stage SEPARATE the historical defect from the live narratives?

    RQ-77-PROSEBLIND. Note the population: this reads the RAW file text, not
    `prose_of()`. The parsed object cannot see YAML COMMENTS, and an artifact's
    comments are part of its prose — a false claim in one is still a false claim.
    Measured: the raw scan and the parsed scan do not agree on the hit count.
    """
    ctl = control_text()
    ctl_status = str(yaml.safe_load(ctl)['artifacts'][0].get('status', '')).lower()
    rows = [("POSITIVE " + CONTROL[0], stage_verdicts(ctl, ctl_status), True)]
    for f, a in artifacts():
        raw = open(f).read()
        if raw.count("\n  - id:") > 0 and len(yaml.safe_load(raw).get('artifacts') or []) != 1:
            continue          # raw text cannot be attributed in a multi-artifact file
        aid = a['id']
        if aid in (SELF, "RQ-77-PROSEBLIND"):
            continue          # records that QUOTE the patterns to explain them
        v = stage_verdicts(raw, str(a.get('status', '')).strip().lower())
        if any(v.values()):
            rows.append((f"negative {aid}", v, False))
    print("\nseparation experiment (RAW text, incl. YAML comments) — the control "
          "must RED, negatives must stay green")
    separating = []
    for stage in ("naive", "real-status", "not-quoted"):
        ok = all(v[stage] == must for _l, v, must in rows)
        if ok:
            separating.append(stage)
        detail = " ".join(f"{l.split()[-1]}={'RED' if v[stage] else 'green'}"
                          for l, v, _m in rows)
        print(f"  {stage:14s} {'SEPARATES' if ok else 'fails    '}  {detail}")

    # THE VERDICT IS DERIVED, NOT PRINTED. v0.77's round-1 gate review found this
    # sentence hardcoded: repointing CONTROL at bd81bc8c — the commit where v0.68
    # CORRECTED the false claim, so the control is green under every stage and
    # demonstrates nothing — still printed "The control reds under all three".
    # A conclusion that cannot be wrong about its own experiment is the defect
    # RQ-77-PROSEBLIND exists to record, one level up.
    # NOTE round 2: `rows` is SEEDED with the control unconditionally at the top of
    # this function, so a "no positive control" branch here would be DEAD CODE. It
    # was written and removed rather than left in as a refusal that cannot fire —
    # which is the same defect class as a marker in a comment. The reachable guard
    # is the green-control one below, and it is red-first proven.
    ctrl = next(v for _l, v, must in rows if must)
    ctrl_red = [s for s in ("naive", "real-status", "not-quoted") if ctrl[s]]
    if not ctrl_red:
        sys.exit(f"REFUSE: the positive control is GREEN under all three stages, so "
                 f"this experiment is UNINFORMATIVE — it cannot distinguish 'no "
                 f"rule separates' from 'no rule fires at all'. Check that CONTROL "
                 f"still names a commit whose artifact carries the false claim; "
                 f"{CONTROL[0]} was chosen because the claim is live there.")
    if separating:
        print(f"  VERDICT: {len(separating)} stage(s) SEPARATE — "
              f"{', '.join(separating)}. That CONTRADICTS RQ-69-PROSEGATE's and "
              f"RQ-77-PROSEBLIND's recorded refutation, which say none does. "
              f"Re-measure before believing either: a rule that separates is a "
              f"gate this repo could wire, and #1319 would be wrong to hold as "
              f"refuted.")
    else:
        # THE CAUSAL CLAUSE IS DERIVED TOO. Round 2 constructed the 2-of-3 case and
        # found the count derived while the *reason* stayed a literal — and at a
        # stage where the control goes GREEN, non-separation is caused by the
        # control, not by the negatives. Say which.
        green_at = [s for s in ("naive", "real-status", "not-quoted")
                    if s not in ctrl_red]
        if green_at:
            cause = (f"at {', '.join(green_at)} the CONTROL itself stays green, so "
                     f"non-separation there is the control failing to fire, not a "
                     f"negative firing")
        else:
            cause = ("so do records that correctly narrate their own history, "
                     "which is what makes every stage fire on a true statement")
        print(f"  VERDICT: no stage separates. The control reds under "
              f"{len(ctrl_red)} of 3 ({', '.join(ctrl_red) or 'none'}); {cause} — "
              f"which is why this script must not be wired, and why "
              f"RQ-77-PROSEBLIND records a refutation rather than a gate.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--show', action='store_true')
    ap.add_argument('--verify', action='store_true',
                    help="RQ-77-PROSEBLIND: run the separation experiment against "
                         "the historical positive control")
    args = ap.parse_args()
    blocks, stages = measure()
    if blocks == 0:
        sys.exit("REFUSE: zero artifact blocks parsed — every count below would be "
                 "about the empty set")
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
    if args.verify:
        verify()
    return 0


if __name__ == '__main__':
    sys.exit(main())
