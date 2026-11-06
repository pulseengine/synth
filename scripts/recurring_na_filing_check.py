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


def releases_in(docs) -> set[tuple]:
    """Release KEYS, via status_evidence_check's canonical key (v0.89.1 PATCHVER,
    #1622): `v0.89` and `v0.89.0` key as (0, 89), a patch `v0.89.1` as
    (0, 89, 1). The old (major, minor) truncation folded a patch into its minor,
    so the cut could never be a patch and a patch's filing could never count."""
    sec = _load("sec_keys", "scripts/status_evidence_check.py")
    rel = set()
    for _f, d in docs:
        for a in (d or {}).get("artifacts", []) or []:
            if not isinstance(a, dict):
                continue
            key = sec.parse_release(str(a.get("release") or "").strip())
            if key is not None:
                rel.add(key)
    return rel


def release_under_cut(docs, anchor=None) -> tuple[str, list[str]]:
    """The release being cut, derived TWICE and cross-checked.

    `ANCHOR_TAG` is the LAST SHIPPED release, so the cut is its successor. The
    artifact tree's own max `release:` must agree. Disagreement is refused
    rather than resolved: picking the wrong release here would let a previous
    release's filing discharge this one's, which is the whole defect #1136 names.

    `anchor` defaults to the shipped `ANCHOR_TAG`. It is a parameter only so the
    self-test can pin a PATCH-release fixture whose verdict does not depend on
    where the live tree's anchor happens to stand (RQ-90-NASELFTEST, #1653).
    """
    sec = _load("sec_anchor", "scripts/status_evidence_check.py")
    rels = releases_in(docs)
    if not rels:
        return "", ["no artifact carries a `release:` — a derived population of "
                    "zero is a refusal, not a pass"]
    # anchor+1 is the successor MINOR, or the successor PATCH when that patch's
    # own records are present — the same single answer the CENSUS uses.
    from_anchor = sec.expected_cut(sec.ANCHOR_TAG if anchor is None else anchor, rels)
    from_tree = max(rels)
    if from_anchor != from_tree:
        return "", [f"the release under cut is ambiguous: anchor+1 says "
                    f"{sec.fmt_release(from_anchor)} while the artifact tree's max "
                    f"says {sec.fmt_release(from_tree)} — refusing rather than guessing"]
    return sec.fmt_release(from_anchor), []


def check(docs, anchor=None) -> list[str]:
    rel, fails = release_under_cut(docs, anchor)
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

    # PATCH FIXTURE (RQ-90-NASELFTEST, #1653). Every case above is either the
    # live tree or a MINOR-release shape, so the patch key was untested: the
    # v0.89.1 cold review (G10) found this self-test stayed rc 0 under BOTH key
    # mutants — `release_key` folding every patch to (major, minor), and
    # `releases_in` truncating its keys with `[:2]` — and the v0.90 planning
    # measurement found the fold redded it only through the live-tree case,
    # i.e. only while the live anchor happened to be a patch.
    #
    # So this fixture is OFFLINE: a synthetic tree and a PINNED anchor, v0.89.0
    # -> cut v0.89.1, independent of the live ANCHOR_TAG. Measured against the
    # two mutants at authoring:
    #   * the fold keys the anchor and the filing as (0, 89): both sources say
    #     v0.89 and agree, the derived release is v0.89, and the v0.89.1 filing
    #     is reported stale;
    #   * the truncation keys the tree as {(0, 89)}: the patch is absent, so
    #     anchor+1 says v0.90 while the tree's max says v0.89 -> ambiguous.
    # The derived RELEASE STRING is asserted, not only `check() == []`, so the
    # fold cannot pass by some other filing matching the folded release.
    patch_fixture = [("fixture/release-v0.89.1/RQ-89-1-ARCHMODEL.yaml", {
        "artifacts": [{"id": "RQ-89-1-ARCHMODEL", "release": "v0.89.1",
                       "status": "proposed",
                       "tags": ["feature-loop", "aadl"],
                       "fields": {"issue": "#1136"}}]})]
    prel, perrs = release_under_cut(patch_fixture, anchor="v0.89.0")
    ok(prel == "v0.89.1" and not perrs,
       f"PATCH FIXTURE: anchor v0.89.0 + a v0.89.1 filing derives the cut as "
       f"v0.89.1, a PATCH key (got {prel!r}, {perrs})")
    pmsgs = check(patch_fixture, anchor="v0.89.0")
    ok(pmsgs == [], f"PATCH FIXTURE: the patch release's own filing is VISIBLE "
                    f"and discharges it ({pmsgs})")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else report()


if __name__ == "__main__":
    sys.exit(main())
