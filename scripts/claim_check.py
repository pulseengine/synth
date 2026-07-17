#!/usr/bin/env python3
"""claim_check — gate synth's documentation claims against live evidence.

Adapted from the pulseengine-claude `claim-verification` skill's reference
implementation. The repo's load-bearing doc claims (proof counts, "verified"
wording, DSL rule coverage, trusted-base sizes) live in `claims.yaml`; CI runs
this script; drift between a claim, its recorded ledger, and the *actual
source* fails the build. Truth-over-time becomes a property of the gate, not
the author.

Usage:
  scripts/claim_check.py [claims.yaml]                verify everything (CI mode)
  scripts/claim_check.py [claims.yaml] --emit-status  regenerate the derived
                                                      artifacts (status.json +
                                                      the generated feature
                                                      matrix), then verify

Exit:   0 = all claims hold · 1 = one or more drifted

Four gates run in CI mode:

  1. Claims        — every entry in `claims:` (evidence predicates below).
  2. Status         — `artifacts/status.json` and the generated
     staleness       `docs/status/FEATURE_MATRIX.md` must EQUAL what
                     re-derivation produces right now. Numbers live in that
                     one machine-derived artifact (README badges point at it);
                     prose stays number-free. Hand-editing either file, or
                     landing a proof without regenerating, is a red build.
  3. README link    — every relative `.md` link in README.md must resolve AND
     coverage        be claim-covered (some claim's `doc:`), generated, or
                     explicitly allowlisted in `readme_link_coverage.
                     unpinned_ok` with a rationale. A new linked doc cannot
                     silently join the unverified surface.
  4. (CI job)      — `scripts/repo_metadata_check.py` pins the GitHub repo
                     description/topics; wired as a separate step.

Evidence predicates re-derive from source — never a number typed only in prose:

  verbatim     the honest wording appears VERBATIM in the doc
  file-exists  the proof/harness the claim rests on is present
  count-eq     re-count a pattern from source; fail unless it EQUALS the doc's
               stated number (for headline counts: a new proof landing must
               update the doc + ledger together)
  count-max    re-count from source; fail if it exceeds the recorded trusted-
               base size (for things that must not grow)
  count-min    re-count from source; fail if it falls below the recorded floor
               (for tracks that must not silently empty out)
  count-same   two or more independent derivations must agree with EACH OTHER
               (1:1 invariants — e.g. DSL manifest rules == Qed rule theorems)
               without pinning the value itself; the value flows to
               status.json instead
  no-new       no new sorry/admit/Admitted since the ledger's recorded count
  yaml-field   a field of a list item in a YAML artifact file (e.g. the rivet
               roadmap's `status:`) equals the recorded value — "verified"
               wording in prose is bound to the roadmap's status field
  status-field the named field is declared in `status_fields:` (used to bind a
               README badge's JSONPath query to a real derived field)

Derived-status field kinds (under `status_fields:`):

  count           len(regex findall) over globs (same engine as count-eq)
  capture         first regex capture group in one file (e.g. the version)
  distinct-tokens number of DISTINCT capture-group values in one file,
                  optionally truncated at a `before:` marker (e.g. the ops an
                  instruction selector handles, stopping before `mod tests`)
  const           a hand-written value (names, not numbers) whose supporting
                  paths under `require:` must all exist
"""

import glob
import json
import pathlib
import re
import sys

try:
    import yaml
except ImportError:
    sys.exit("claim_check: needs PyYAML  (pip install pyyaml)")

STATUS_JSON = "artifacts/status.json"
FEATURE_MATRIX = "docs/status/FEATURE_MATRIX.md"
FEATURE_MATRIX_TMPL = "scripts/templates/feature_matrix.md.tmpl"


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


# ---------------------------------------------------------------------------
# Derived status — the ONE machine-derived numbers artifact (status.json).
# README badges and the generated feature matrix surface these; prose does not
# repeat them.
# ---------------------------------------------------------------------------


def derive_status(spec, root):
    """Compute every field declared under `status_fields:`. Raises on a
    predicate that measures nothing — a derivation that silently matches no
    files must never green."""
    out = {}
    for name, f in sorted(spec.items()):
        kind = f.get("kind")
        if kind == "count":
            n, matched = _count(f["pattern"], f["glob"], root)
            if not matched:
                raise RuntimeError(
                    f"status field {name!r}: glob matched NO files: {f['glob']}"
                )
            out[name] = n
        elif kind == "capture":
            text = (root / f["file"]).read_text(errors="ignore")
            m = re.search(f["pattern"], text, re.MULTILINE)
            if not m:
                raise RuntimeError(
                    f"status field {name!r}: pattern matched nothing in {f['file']}"
                )
            out[name] = m.group(1)
        elif kind == "distinct-tokens":
            text = (root / f["file"]).read_text(errors="ignore")
            marker = f.get("before")
            if marker:
                if marker not in text:
                    raise RuntimeError(
                        f"status field {name!r}: 'before' marker {marker!r} "
                        f"absent from {f['file']} — derivation region undefined"
                    )
                text = text.split(marker, 1)[0]
            toks = set(re.findall(f["pattern"], text))
            if not toks:
                raise RuntimeError(
                    f"status field {name!r}: no tokens matched in {f['file']}"
                )
            out[name] = len(toks)
        elif kind == "const":
            for p in f.get("require", []):
                if not (root / p).exists():
                    raise RuntimeError(
                        f"status field {name!r}: required path missing: {p}"
                    )
            out[name] = f["value"]
        else:
            raise RuntimeError(f"status field {name!r}: unknown kind {kind!r}")
    return out


def render_status_json(status):
    return json.dumps(status, indent=2, sort_keys=True) + "\n"


def render_feature_matrix(status, root):
    tmpl = (root / FEATURE_MATRIX_TMPL).read_text()
    unknown = []

    def sub(m):
        key = m.group(1)
        if key not in status:
            unknown.append(key)
            return m.group(0)
        return str(status[key])

    rendered = re.sub(r"\{\{(\w+)\}\}", sub, tmpl)
    if unknown:
        raise RuntimeError(
            f"feature-matrix template references undeclared status fields: {unknown}"
        )
    return rendered


def check_generated_fresh(status, root):
    """The committed status.json + generated feature matrix must equal what
    re-derivation produces NOW (hand edits and stale commits both fail)."""
    fails = []
    want = {
        STATUS_JSON: render_status_json(status),
        FEATURE_MATRIX: render_feature_matrix(status, root),
    }
    for rel, expected in want.items():
        p = root / rel
        if not p.exists():
            fails.append(f"generated file missing: {rel} — run --emit-status")
        elif p.read_text() != expected:
            fails.append(
                f"generated file STALE or hand-edited: {rel} — regenerate with "
                f"`python3 scripts/claim_check.py claims.yaml --emit-status` "
                f"and commit the result"
            )
    return fails


# ---------------------------------------------------------------------------
# README link coverage — the linked-doc surface cannot grow unverified.
# ---------------------------------------------------------------------------

_MD_LINK = re.compile(r"\]\(([^)\s#]+\.md)(?:#[^)]*)?\)")


def check_readme_links(data, claims, root):
    fails = []
    cfg = data.get("readme_link_coverage") or {}
    generated = set(cfg.get("generated", []))
    allow = {}
    for e in cfg.get("unpinned_ok", []):
        if not e.get("rationale", "").strip():
            fails.append(
                f'readme_link_coverage.unpinned_ok entry {e.get("path")!r} '
                f"has no rationale — an allowlist entry must say WHY it is "
                f"safe to leave unpinned"
            )
        allow[e.get("path")] = e.get("rationale", "")
    claim_docs = {c.get("doc") for c in claims}

    readme = root / "README.md"
    links = sorted(
        {
            link.lstrip("/")
            for link in _MD_LINK.findall(readme.read_text(errors="ignore"))
            if not link.startswith(("http://", "https://"))
        }
    )
    for link in links:
        if not (root / link).exists():
            fails.append(f"README links a MISSING file (dangling link): {link}")
            continue
        if link in claim_docs or link in generated or link in allow:
            continue
        fails.append(
            f"README-linked doc not in the claim surface: {link} — either add "
            f"a claims.yaml entry with doc: {link}, mark it generated, or "
            f"allowlist it under readme_link_coverage.unpinned_ok with a "
            f"rationale"
        )
    # The allowlist must not accumulate dead entries pointing at nothing.
    for p in allow:
        if p and not (root / p).exists():
            fails.append(f"readme_link_coverage.unpinned_ok entry missing on disk: {p}")
    return fails


# ---------------------------------------------------------------------------
# Claim evidence predicates
# ---------------------------------------------------------------------------


def check_claim(c, root, status_spec):
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
        elif kind == "count-min":
            n, matched = _count(ev["pattern"], ev["glob"], root)
            if not matched:
                fails.append(
                    f'predicate matched NO files (measures nothing): glob {ev["glob"]}'
                )
            elif n < ev["min"]:
                fails.append(
                    f'track shrank below floor: {n} < recorded min {ev["min"]}  '
                    f'[/{ev["pattern"]}/]  — update the claim, not just the number'
                )
        elif kind == "count-same":
            derived = []
            for leg in ev["legs"]:
                n, matched = _count(leg["pattern"], leg["glob"], root)
                if not matched:
                    fails.append(
                        f'count-same leg matched NO files: glob {leg["glob"]}'
                    )
                    break
                derived.append((leg.get("name", leg["glob"]), n))
            else:
                vals = {n for _, n in derived}
                if len(vals) > 1:
                    fails.append(
                        f"1:1 invariant broken — legs disagree: "
                        + ", ".join(f"{name}={n}" for name, n in derived)
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
        elif kind == "status-field":
            if ev["name"] not in status_spec:
                fails.append(
                    f'status field {ev["name"]!r} not declared in status_fields '
                    f'— a badge/query is pointing at a field status.json will '
                    f'never carry'
                )
        else:
            fails.append(f"unknown evidence kind: {kind!r}")
    return fails


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    emit = "--emit-status" in sys.argv[1:]
    path = pathlib.Path(args[0] if args else "claims.yaml")
    if not path.exists():
        sys.exit(f"claim_check: {path} not found")
    root = path.parent
    data = yaml.safe_load(path.read_text()) or {}
    claims = data.get("claims", [])
    status_spec = data.get("status_fields", {}) or {}
    if not claims:
        print("claim_check: no claims declared — nothing to gate.")
        return

    status = derive_status(status_spec, root) if status_spec else {}

    if emit and status_spec:
        (root / STATUS_JSON).parent.mkdir(parents=True, exist_ok=True)
        (root / STATUS_JSON).write_text(render_status_json(status))
        (root / FEATURE_MATRIX).write_text(render_feature_matrix(status, root))
        print(f"emitted {STATUS_JSON} + {FEATURE_MATRIX}")

    bad = 0
    for c in claims:
        fails = check_claim(c, root, status_spec)
        if fails:
            bad += 1
            print(f"FAIL {c['id']}")
            for f in fails:
                print(f"    {f}")
        else:
            print(f"ok   {c['id']}")

    extra = []
    if status_spec:
        extra += check_generated_fresh(status, root)
    extra += check_readme_links(data, claims, root)
    for f in extra:
        bad += 1
        print(f"FAIL {f}")

    print(f"\n{len(claims) - bad}/{len(claims)} claims hold." if not extra else "")
    if extra:
        print(f"{len(claims)} claims checked; {bad} failure(s) incl. surface gates.")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
