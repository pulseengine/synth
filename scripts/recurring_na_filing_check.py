#!/usr/bin/env python3
"""RQ-87-ARCHMODEL6 (#1136) — is the recurring steps-1-2 N/A filing VISIBLE to
the matcher that counts it, for the release being cut?

THE REFUTING COMMAND: "Derive the ordinal by artifact identity AND run the step
matcher — a filing that is not SEEN has not been filed."

RUN, AND THE PREMISE IS CONFIRMED. The ordinal derived by ARTIFACT IDENTITY (not
by counting releases) is TWENTY-FIVE, v0.63 through v0.87. Of those twenty-five,
exactly ONE was invisible to the matcher: v0.87's own, carrying `feature-loop`
and `process` but NEITHER `aadl` NOR `spar`, which the matcher requires. The
matcher asked for v0.87 returned `RQ-63-ARCHMODEL` — a filing from
TWENTY-FOUR RELEASES EARLIER — marked `stale`, and the conformance slot then
reported DERIVED-FAIL naming the remedy. So the filing had lapsed while every
previous one was fine: a tagging regression, since v0.85 and v0.86 both carry
`aadl`.

WHY THIS CHECK EXISTS SEPARATELY FROM THAT SLOT, which is the placement half.
The slot is only ever asked by `tag_release.sh`. It DOES block — PRETAG
conformance gates the tag push, so this is not a toothless gate — but it blocks
at the LAST possible moment, after every lane has merged. Fixing a one-word
tagging slip there costs a further merge-and-revalidate cycle, which this
repository measures in hours. Asked on the PR instead, the same defect costs one
push. Same gate, same potency, earlier window.

IT IMPORTS THE SHIPPED MATCHER rather than re-implementing it
(`find_filed_steps12_decision`), so there is no second definition of "visible"
to drift. And it derives the release under cut TWO INDEPENDENT WAYS — from
`ANCHOR_TAG + 1` and from `max()` over the artifact tree's own `release:`
fields — and REFUSES when they disagree, because a check that picks the wrong
release would pass over someone else's filing.
"""
import argparse
import glob
import importlib.util
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent


def _load(name: str, rel: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def artifact_docs() -> list[tuple[str, dict]]:
    out = []
    for f in sorted(glob.glob(str(ROOT / "artifacts/**/*.yaml"), recursive=True)):
        try:
            out.append((str(Path(f).relative_to(ROOT)), yaml.safe_load(Path(f).read_text())))
        except Exception:
            continue
    return out


def releases_in(docs) -> set[tuple[int, int]]:
    rel = set()
    for _f, d in docs:
        for a in (d or {}).get("artifacts", []) or []:
            if not isinstance(a, dict):
                continue
            r = str(a.get("release") or "").strip().lstrip("v")
            parts = r.split(".")
            if len(parts) >= 2 and all(p.isdigit() for p in parts[:2]):
                rel.add((int(parts[0]), int(parts[1])))
    return rel


def release_under_cut(docs) -> tuple[str, list[str]]:
    """The release being cut, derived TWICE and cross-checked.

    `ANCHOR_TAG` is the LAST SHIPPED release, so the cut is its successor. The
    artifact tree's own max `release:` must agree. Disagreement is refused
    rather than resolved: picking the wrong release here would let a previous
    release's filing discharge this one's, which is the whole defect #1136 names.
    """
    sec = _load("sec_anchor", "scripts/status_evidence_check.py")
    a_major, a_minor = (int(x) for x in sec.ANCHOR_TAG.lstrip("v").split(".")[:2])
    from_anchor = (a_major, a_minor + 1)
    rels = releases_in(docs)
    if not rels:
        return "", ["no artifact carries a `release:` — a derived population of "
                    "zero is a refusal, not a pass"]
    from_tree = max(rels)
    if from_anchor != from_tree:
        return "", [f"the release under cut is ambiguous: anchor+1 says "
                    f"v{from_anchor[0]}.{from_anchor[1]} while the artifact tree's max "
                    f"says v{from_tree[0]}.{from_tree[1]} — refusing rather than guessing"]
    return f"v{from_anchor[0]}.{from_anchor[1]}", []


def check(docs) -> list[str]:
    rel, fails = release_under_cut(docs)
    if fails:
        return fails
    lcc = _load("lcc_match", "scripts/loop_conformance_check.py")
    hit = lcc.find_filed_steps12_decision(docs, release=rel)
    if hit is None:
        return [f"{rel}: NO steps-1-2 filing is visible to the matcher at all — it "
                f"needs an artifact tagged `feature-loop` plus `aadl` or `spar`, "
                f"carrying a non-empty `fields.issue`"]
    if hit.get("stale"):
        return [f"{rel}: the only visible steps-1-2 filing is {hit['id']}, scoped to "
                f"release {hit['release']} — NOT {rel}. A previous release's filing "
                f"does not discharge this one's (#1136 is a RECURRING N/A). The "
                f"{rel} artifact is most likely MISSING the `aadl`/`spar` tag."]
    return []


def report() -> int:
    docs = artifact_docs()
    rel, _ = release_under_cut(docs)
    fails = check(docs)
    print(f"artifact docs loaded: {len(docs)}   release under cut: {rel or '<refused>'}")
    for m in fails:
        print(f"  FAIL {m}")
    if not fails:
        lcc = _load("lcc_r", "scripts/loop_conformance_check.py")
        hit = lcc.find_filed_steps12_decision(docs, release=rel)
        print(f"  steps-1-2 filing VISIBLE: {hit['id']} ({hit['issue']}, "
              f"status {hit['status']}) scoped to {hit['release']}")
        print("\nNOTE ON PLACEMENT: the conformance slot asks this only in "
              "tag_release.sh —\nit blocks, but after every lane has merged. Asked "
              "here it costs one push.")
    print(f"failures: {len(fails)}")
    return 1 if fails else 0


def self_test() -> int:
    fails = 0

    def ok(cond, what):
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    docs = artifact_docs()
    # POSITIVE CONTROL: the live tree must pass, or the check is just noisy.
    ok(check(docs) == [], f"the live tree passes ({len(check(docs))} failure(s))")
    rel, errs = release_under_cut(docs)
    ok(not errs and rel.startswith("v"), f"the release under cut derives to {rel!r} "
                                         f"from two agreeing sources")

    # NEGATIVE CONTROL 1 — the EXACT defect: the cut release's filing loses its
    # `aadl`/`spar` tag, so only a previous release's filing is visible.
    stripped = []
    for f, d in docs:
        import copy
        d2 = copy.deepcopy(d) if isinstance(d, dict) else d
        for a in (d2 or {}).get("artifacts", []) or []:
            if isinstance(a, dict) and str(a.get("release") or "").strip() == rel:
                a["tags"] = [t for t in (a.get("tags") or []) if t not in ("aadl", "spar")]
        stripped.append((f, d2))
    msgs = check(stripped)
    ok(any("does not discharge" in m or "NO steps-1-2 filing" in m for m in msgs),
       "NEGATIVE CONTROL: stripping the cut release's aadl/spar tag REDS, naming "
       "the stale filing — the defect this lane measured")

    # NEGATIVE CONTROL 2 — an empty population is REFUSED, not passed.
    ok(check([]) != [], "an empty artifact population is REFUSED rather than clean")
    ok(any("zero is a refusal" in m for m in check([])),
       "and it says so in those words")

    # NEGATIVE CONTROL 3 — the two release derivations must be able to DISAGREE,
    # or the cross-check is decoration.
    import copy
    future = copy.deepcopy(docs[0][1]) if isinstance(docs[0][1], dict) else {}
    for a in (future or {}).get("artifacts", []) or []:
        if isinstance(a, dict):
            a["release"] = "v9.99"
    msgs3 = check(docs + [("probe.yaml", future)])
    ok(any("ambiguous" in m for m in msgs3),
       "NEGATIVE CONTROL: a stray newer release makes the cut AMBIGUOUS and is "
       "refused, not resolved by picking one")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else report()


if __name__ == "__main__":
    sys.exit(main())
