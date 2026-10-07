#!/usr/bin/env python3
# NOTE on home: this lives in scripts/ (with claim_check.py — tooling over
# shipped artifacts), not scripts/repro/ (defect oracles). It has a VERDICT and
# is WIRED, which is the whole difference between it and
# scripts/repro/prose_status_claim_1319.py — see "WHY THIS IS NOT #1319" below.
"""RQ-80-SENTENCE (#1461) — the leading VERDICT of `verified-by:` must agree
with the artifact's own structured `status:`/`disposition:`.

THE CLASS, and the instance that motivates it. v0.79 shipped with every
structured gate green while its cold-review record enumerated twenty defect
items, and the citable one reached `main`: at commit 28196ec7,
artifacts/release-v0.79/RQ-79-ORDEAL.yaml carried `status: proposed` and
`disposition: partial` while its own `verified-by:` prose opened with the word
`LANDED.` R11 was not blind to it -- R11 was SATISFIED BY IT, because R11's
obligation is only that a disposition be PRESENT beside a `landed:` on a
non-claiming status. So the field that exists to flag an under-claim is the same
field whose presence let the prose over-claim.

THE RULE. Many `verified-by:` blocks open with an ALL-CAPS verdict word. When
that word asserts COMPLETION, the structured fields must agree (claiming status,
no non-delivery disposition); when it asserts NON-COMPLETION, they must agree the
other way. The vocabulary is DERIVED from the tree, not invented -- see
`--census`, which prints the leading-token distribution the sets below come from.

  python3 scripts/verdict_prose_check.py           # verdict: rc=1 on disagreement
  python3 scripts/verdict_prose_check.py --census   # the derivation, no verdict
  python3 scripts/verdict_prose_check.py --self-test # potency, three controls

WHY THIS IS NOT #1319, measured rather than asserted.
`scripts/repro/prose_status_claim_1319.py` (RQ-69-PROSEGATE) refuted a DIFFERENT
rule: prose that NAMES a lifecycle status ("the status is implemented"). Run both
on the same tree -- that rule's final stage hits RQ-62-EMBEDDER and RQ-75-REPLAY;
this one hits RQ-66-PINDEBT and RQ-66-UNWATCHED. The populations are disjoint, so
the refutation of that rule says nothing about this one, and this one catches two
live instances that one cannot see. Its header's "0 live true positives" is also
no longer the live figure; re-run it rather than quoting it.

POTENCY TAKES THREE CONTROLS, and the obvious one is the weakest. `--self-test`
holds the FIELDS constant and swaps only the leading verdict (A: prose-sensitivity),
holds the PROSE constant and swaps the status (B: field-sensitivity), and replays
RQ-79-ORDEAL at 28196ec7/f8809521 (C: a combination R11 ACCEPTS, so this is added
coverage over R11). C alone proves nothing about prose -- the prose reads `LANDED.`
at both of those shas -- which is why A exists.

THE CARVE-OUT, and it is a named gate conflict rather than a fudge. A leading
`REFUTED` beside a CLAIMING status is LEGAL. Delivering a refutation IS delivery,
so `implemented` is correct -- and R11 FORBIDS `disposition: refuted` beside a
claiming status, so no legal field can express it. That is #1430's shape: for one
real combination neither remedy exists. Without this carve-out the gate reds
RQ-77-PROSEBLIND, whose prose is right and whose fields cannot be.
"""
import argparse, glob, re, sys, yaml
from collections import Counter

CLAIMING = {"implemented", "verified", "accepted"}
NON_DELIVERY_DISPOSITION = {"partial", "deferred", "refuted", "blocked", "superseded"}

# Leading verdicts asserting the work IS delivered.
COMPLETE = {"DELIVERED", "IMPLEMENTED", "VERIFIED", "LANDED", "SHIPPED",
            "COMPLETE"}
# Leading verdicts asserting it is NOT (or not fully) delivered. `NOT DELIVERED`
# is a PHRASE, not the bare word: `NOT` alone could lead "NOT a regression --
# delivered in full", which is the opposite verdict.
INCOMPLETE = {"PARTIAL", "PENDING", "NOT DELIVERED", "DEFERRED", "BLOCKED",
              "WITHDRAWN", "REFUTED"}
# MEASURED EXCLUSIONS, not oversights. These lead a `verified-by:` in this tree
# and are NOT verdicts about the work -- the #1319 script's stage-2 lesson, which
# is that the first all-caps run is often a grammatical accident:
#   FULL      -- "FULL 243-MODULE CORPUS measured on ..." (describes the corpus)
#   DONE-WHEN -- "DONE-WHEN BRANCH B, taken deliberately ..." (names a field)
# Both sit on claiming artifacts today, so including them would cost nothing
# now and produce a false positive the first time such prose led a non-claiming
# artifact. Re-run --census before adding to either set.
NOT_A_VERDICT = {"FULL", "DONE-WHEN", "RED-FIRST", "THE", "BOTH", "MEASURED",
                 "ORACLE", "CHARACTERIZATION", "DECIDED", "ENUMERATION",
                 # RQ-81-SILENT (#1476). Added as MEASURED EXCLUSIONS when
                 # `unclassified_lead` made this set load-bearing: these are the
                 # SIX openings that the LEAD regex catches on the live tree and
                 # that are not verdicts about the work. Derived, not guessed —
                 # over 175 artifacts carrying `verified-by`, these are exactly
                 # the unclassified leads, one occurrence each, all in v0.65..v0.77.
                 # Without them a red-on-unclassified gate would red six innocent
                 # artifacts on day one, which is the RQ-74-STALEMSG trap: a gate
                 # nobody can move honestly is a gate they route around.
                 # The DANGEROUS escapes are deliberately NOT here, so they red:
                 # NOT LANDED, DONE, NOT-DELIVERED, CLOSED.
                 "CLASSIFICATION", "TRIAGE", "EVERY", "ADDED", "BYTE", "RULE"}
# See THE CARVE-OUT above (#1430).
LEGAL_BESIDE_CLAIMING = {"REFUTED"}

LEAD = re.compile(r"^([A-Z][A-Z0-9-]{2,}(?:\s+[A-Z][A-Z0-9-]{2,})?)\b")


def leading_verdict(vb):
    """The leading verdict token, preferring the two-word phrase. None when the
    opening run is not a verdict about the work."""
    m = LEAD.match(vb.strip())
    if not m:
        return None
    phrase = " ".join(m.group(1).split())
    if phrase in COMPLETE or phrase in INCOMPLETE:
        return phrase
    first = phrase.split()[0]
    if first in NOT_A_VERDICT:
        return None
    if first in COMPLETE or first in INCOMPLETE:
        return first
    return None


def unclassified_lead(vb):
    """The leading ALL-CAPS run when it LOOKS LIKE A VERDICT but no set
    classifies it — the #1476 hole, made nameable.

    `leading_verdict` returns None for TWO different situations and that
    conflation IS the defect: "this opening is not a verdict about the work"
    (correct, nothing to check) and "this verdict word is not in any set"
    (an ESCAPE — out of population, and out of population is
    indistinguishable from compliant). Measured escapes on the live sets:
    `NOT LANDED`, `DONE`, `NOT-DELIVERED`, `CLOSED`. `NOT LANDED` is the
    sharpest, because excluding a bare leading `NOT` means `NOT` + any
    COMPLETE word is unclassified, and that consequence was written down
    nowhere.

    NOTE WHAT THIS DOES TO `NOT_A_VERDICT`. Before this function the set was
    INERT: every member was already outside COMPLETE u INCOMPLETE, so its
    branch was always followed by a path returning None anyway, and deleting
    it changed no verdict and passed every unit test. Here it becomes
    LOAD-BEARING — it is the list that separates a deliberate non-verdict
    opening from an escape. The documented intent and the behaviour now agree.
    """
    m = LEAD.match(vb.strip())
    if not m:
        return None
    phrase = " ".join(m.group(1).split())
    if phrase in COMPLETE or phrase in INCOMPLETE:
        return None
    first = phrase.split()[0]
    if first in COMPLETE or first in INCOMPLETE:
        return None
    if first in NOT_A_VERDICT:
        return None
    return phrase


def artifacts(root="."):
    for f in sorted(glob.glob(f"{root}/artifacts/**/*.yaml", recursive=True)):
        try:
            d = yaml.safe_load(open(f))
        except Exception:
            continue
        if isinstance(d, dict):
            for a in (d.get("artifacts") or []):
                if isinstance(a, dict) and "id" in a:
                    yield f, a


def classify(a):
    """None when the artifact is outside the population; else (tok, bad, why)."""
    fl = a.get("fields") or {}
    vb = fl.get("verified-by")
    if not isinstance(vb, str) or not vb.strip():
        return None
    tok = leading_verdict(vb)
    if tok is None:
        return None                      # not a verdict word; out of population
    kind = "complete" if tok in COMPLETE else "incomplete"
    status = str(a.get("status", "")).strip().lower()
    disp = str(fl.get("disposition", "")).strip().lower()
    claiming, non_delivery = status in CLAIMING, disp in NON_DELIVERY_DISPOSITION
    if kind == "complete":
        if not claiming:
            return tok, True, f"prose claims {tok} but status is '{status}'"
        if non_delivery:
            return tok, True, f"prose claims {tok} beside disposition '{disp}'"
        return tok, False, ""
    if claiming and not non_delivery:
        if tok in LEGAL_BESIDE_CLAIMING:
            return tok, False, ""        # the #1430 carve-out
        return tok, True, (f"prose says {tok} but status is '{status}' with no "
                           f"disposition to say why")
    return tok, False, ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--census", action="store_true",
                    help="print the leading-token derivation; no verdict")
    ap.add_argument("--self-test", action="store_true",
                    help="prove potency against real git history")
    args = ap.parse_args()

    if args.self_test:
        return self_test(args.root)

    pop, bad = 0, []
    lead_all = Counter()
    for f, a in artifacts(args.root):
        fl = a.get("fields") or {}
        vb = fl.get("verified-by")
        if isinstance(vb, str) and vb.strip():
            m = LEAD.match(vb.strip())
            raw = " ".join(m.group(1).split()) if m else "<no all-caps lead>"
            lead_all[raw] += 1
        r = classify(a)
        if r is None:
            continue
        pop += 1
        tok, is_bad, why = r
        if is_bad:
            bad.append((a["id"], f, tok, why, " ".join(str(vb).split())[:110]))

    if args.census:
        print(f"verdict-prose census: {pop} artifacts in the population")
        for k, v in lead_all.most_common():
            mark = ("COMPLETE" if k in COMPLETE else
                    "INCOMPLETE" if k in INCOMPLETE else "-")
            print(f"  {v:4d}  {k:28s} {mark}")
        return 0

    # A DERIVED POPULATION OF ZERO IS A REFUSAL, NOT A PASS.
    if pop == 0:
        print("REFUSE verdict-prose: population is ZERO -- no artifact's "
              "`verified-by:` opens with a verdict word. Either the field moved "
              "or the vocabulary is wrong; this is not a pass.")
        return 2

    for i, f, tok, why, snip in bad:
        print(f"FAIL verdict-prose {i} ({f}): {why}")
        print(f"     verified-by opens: {snip}...")
    print(f"verdict-prose: {pop} artifacts in the population, {len(bad)} "
          f"disagree with their own structured fields")
    return 1 if bad else 0


def self_test(root):
    """POTENCY, as three separate controls. The rule must respond to the PROSE
    and to the FIELDS, and neither alone may determine the verdict.

    An earlier version of this self-test used only RQ-79-ORDEAL at two commits
    (28196ec7 -> f8809521) and claimed that proved prose-sensitivity. It did not:
    the prose reads `LANDED.` at BOTH shas, and what changed between them was the
    status and the disposition. That test could have passed for a rule that never
    read prose at all. It is kept below as control C, relabelled for what it
    actually shows, and the two controls that matter are A and B.
    """
    import copy, subprocess

    def verdict_of(art):
        r = classify(art)
        return None if r is None else ("RED" if r[1] else "pass")

    def load(rel, aid=None):
        for f, a in artifacts(root):
            if f.endswith(rel) and (aid is None or a.get("id") == aid):
                return a
        return None

    ok = True

    # --- CONTROL A: FIELDS HELD CONSTANT, prose swapped. --------------------
    # If the verdict does not flip here, the rule is not reading prose.
    base = load("RQ-66-PINDEBT.yaml", "RQ-66-PINDEBT")
    if base is None:
        print("REFUSE self-test: RQ-66-PINDEBT not found; control A cannot run")
        return 2
    for lead, want in (("PENDING", "RED"), ("DELIVERED", "pass")):
        a = copy.deepcopy(base)
        vb = a["fields"]["verified-by"]
        a["fields"]["verified-by"] = re.sub(r"^[A-Z][A-Z0-9-]*", lead, vb.strip())
        got = verdict_of(a)
        mark = "ok" if got == want else "FAIL"
        if got != want:
            ok = False
        print(f"  {mark:4s} A  fields=(implemented, no disposition) prose={lead:10s}"
              f" -> {got} (want {want})")

    # --- CONTROL B: PROSE HELD CONSTANT, fields swapped. -------------------
    # If the verdict does not flip here, the rule is not reading the fields.
    for st, want in (("implemented", "pass"), ("proposed", "RED")):
        a = copy.deepcopy(load("RQ-76-CAPTURE.yaml", "RQ-76-CAPTURE"))
        a["status"] = st
        got = verdict_of(a)
        mark = "ok" if got == want else "FAIL"
        if got != want:
            ok = False
        print(f"  {mark:4s} B  prose=DELIVERED           status={st:11s}"
              f"    -> {got} (want {want})")

    # --- CONTROL C: coverage OVER R11, from real history. ------------------
    # At 28196ec7 the fields were proposed + partial + landed, which R11 accepts
    # as self-consistent -- so R11 passed that commit. This rule reds it, because
    # the prose says LANDED. That is added coverage, NOT prose-sensitivity (the
    # prose is identical at both shas); control A is the prose-sensitivity proof.
    path = "artifacts/release-v0.79/RQ-79-ORDEAL.yaml"
    import yaml as _y
    for sha, want in (("28196ec7", "RED"), ("f8809521", "pass")):
        out = subprocess.run(["git", "-C", root, "show", f"{sha}:{path}"],
                             capture_output=True, text=True)
        if out.returncode != 0:
            print(f"REFUSE self-test: {path} unreadable at {sha} -- the history "
                  f"control C rests on is not reachable")
            return 2
        got = verdict_of(_y.safe_load(out.stdout)["artifacts"][0])
        mark = "ok" if got == want else "FAIL"
        if got != want:
            ok = False
        print(f"  {mark:4s} C  real history {sha}          -> {got} (want {want})")

    print("self-test: the rule reads BOTH the prose (A) and the fields (B), and "
          "reds a combination R11 accepts (C)" if ok else
          "self-test: FAILED -- see the controls above")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
