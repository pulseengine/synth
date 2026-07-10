#!/usr/bin/env python3
"""claim_check — gate synth's documentation claims against live evidence.

Adapted from the pulseengine-claude `claim-verification` skill's reference
implementation. The repo's load-bearing doc claims (proof counts, "verified"
wording, DSL rule coverage, trusted-base sizes) live in `claims.yaml`; CI runs
this script; drift between a claim, its recorded ledger, and the *actual
source* fails the build. Truth-over-time becomes a property of the gate, not
the author.

Usage:  scripts/claim_check.py [claims.yaml]     (default: ./claims.yaml)
Exit:   0 = all claims hold · 1 = one or more drifted

Evidence predicates re-derive from source — never a number typed only in prose:

  verbatim     the honest wording appears VERBATIM in the doc
  file-exists  the proof/harness the claim rests on is present
  count-eq     re-count a pattern from source; fail unless it EQUALS the doc's
               stated number (for headline counts: a new proof landing must
               update the doc + ledger together)
  count-max    re-count from source; fail if it exceeds the recorded trusted-
               base size (for things that must not grow)
  no-new       no new sorry/admit/Admitted since the ledger's recorded count
  yaml-field   a field of a list item in a YAML artifact file (e.g. the rivet
               roadmap's `status:`) equals the recorded value — "verified"
               wording in prose is bound to the roadmap's status field
"""

import glob
import pathlib
import re
import sys

try:
    import yaml
except ImportError:
    sys.exit("claim_check: needs PyYAML  (pip install pyyaml)")


def _count(pattern, globs, root):
    rx = re.compile(pattern, re.MULTILINE)
    globs = [globs] if isinstance(globs, str) else globs
    total = 0
    matched_any = False
    for g in globs:
        # Resolve globs relative to the claims file's directory, NOT the CWD —
        # otherwise the predicate silently matches nothing and greens a claim
        # it never checked (the "oracle that measures nothing" failure).
        for f in glob.glob(str(root / g), recursive=True):
            p = pathlib.Path(f)
            if p.is_file():
                matched_any = True
                total += len(rx.findall(p.read_text(errors="ignore")))
    return total, matched_any


def _yaml_field(ev, root):
    """Look up `field` of the list item whose `id` matches, in `path`."""
    path = root / ev["path"]
    if not path.exists():
        return None, f'yaml file missing: {ev["path"]}'
    data = yaml.safe_load(path.read_text(errors="ignore")) or {}
    items = data.get(ev.get("list", "artifacts"), [])
    for item in items:
        if isinstance(item, dict) and item.get("id") == ev["id"]:
            return item.get(ev["field"]), None
    return None, f'id {ev["id"]!r} not found in {ev["path"]}'


def check_claim(c, root):
    fails = []
    doc_path = root / c["doc"]
    if not doc_path.exists():
        return [f'doc not found: {c["doc"]}']
    doc = doc_path.read_text(errors="ignore")

    text = c.get("text")
    if text and text not in doc:
        fails.append(f'claim text not found verbatim in {c["doc"]}: "{text}"')

    for ev in c.get("evidence", []):
        kind = ev.get("kind")
        if kind == "verbatim":
            s = ev.get("text", text)
            if s and s not in doc:
                fails.append(f'verbatim string absent from {c["doc"]}: "{s}"')
        elif kind == "file-exists":
            if not (root / ev["path"]).exists():
                fails.append(f'evidence file missing: {ev["path"]}')
        elif kind == "count-eq":
            n, matched = _count(ev["pattern"], ev["glob"], root)
            if not matched:
                fails.append(
                    f'predicate matched NO files (measures nothing): glob {ev["glob"]}'
                )
            elif n != ev["expect"]:
                fails.append(
                    f'count drifted: derived {n} != documented {ev["expect"]}  '
                    f'[/{ev["pattern"]}/ over {ev["glob"]}]  '
                    f'— update the doc AND claims.yaml together'
                )
        elif kind == "count-max":
            n, matched = _count(ev["pattern"], ev["glob"], root)
            if not matched:
                fails.append(
                    f'predicate matched NO files (measures nothing): glob {ev["glob"]}'
                )
            elif n > ev["max"]:
                fails.append(
                    f'trusted base grew: {n} > recorded max {ev["max"]}  '
                    f'[/{ev["pattern"]}/]  — update the claim, not just the number'
                )
        elif kind == "no-new":
            n, matched = _count(ev["pattern"], ev["glob"], root)
            if not matched:
                fails.append(
                    f'predicate matched NO files (measures nothing): glob {ev["glob"]}'
                )
            elif n > ev.get("recorded", 0):
                fails.append(
                    f'new unproven obligations: {n} > recorded {ev.get("recorded", 0)}  '
                    f'[/{ev["pattern"]}/]'
                )
        elif kind == "yaml-field":
            val, err = _yaml_field(ev, root)
            if err:
                fails.append(err)
            elif val != ev["equals"]:
                fails.append(
                    f'{ev["path"]}: {ev["id"]}.{ev["field"]} is {val!r}, '
                    f'claim requires {ev["equals"]!r} — fix the PROSE to match '
                    f'the roadmap, or land the status change first'
                )
        else:
            fails.append(f"unknown evidence kind: {kind!r}")
    return fails


def main():
    path = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "claims.yaml")
    if not path.exists():
        sys.exit(f"claim_check: {path} not found")
    root = path.parent
    data = yaml.safe_load(path.read_text()) or {}
    claims = data.get("claims", [])
    if not claims:
        print("claim_check: no claims declared — nothing to gate.")
        return

    bad = 0
    for c in claims:
        fails = check_claim(c, root)
        if fails:
            bad += 1
            print(f"FAIL {c['id']}")
            for f in fails:
                print(f"    {f}")
        else:
            print(f"ok   {c['id']}")

    print(f"\n{len(claims) - bad}/{len(claims)} claims hold.")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
