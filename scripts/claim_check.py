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
  ratchet      a DIRECTED, slack-free pin on a `status_fields:` derivation —
               see the RQ-58-METRIC block below
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

  count           len(regex findall) over globs (same engine as count-eq),
                  optionally truncated at a `before:` marker and optionally
                  counting FILES-with-a-match instead of matches (`unit: files`)
  capture         first regex capture group in one file (e.g. the version)
  distinct-tokens number of DISTINCT capture-group values in one file,
                  optionally truncated at a `before:` marker (e.g. the ops an
                  instruction selector handles, stopping before `mod tests`)
  const           a hand-written value (names, not numbers) whose supporting
                  paths under `require:` must all exist

===============================================================================
RQ-58-METRIC — the `ratchet` evidence kind (epic #242)
===============================================================================

Epic #242 says "replace the patch-accreting code generator". Measured v0.42.0 ->
v0.57.0 it went the OTHER way and nothing noticed, because nothing measured it:
the instruction selector's non-test code grew 14,694 -> 18,480 lines while the
verified-rule count that is supposed to be replacing it went 40 -> 50 and then
sat flat for twelve releases. A North Star with no number that can go the wrong
way is not falsifiable in practice.

`ratchet` is that number, and it is deliberately UNLIKE count-max/count-min:

  * SLACK-FREE. `value:` must EQUAL the live derivation, always, in both
    directions. A ceiling recorded at "current + slack" is the vacuous version
    of this gate; here there is no room to record one. Every movement of the
    number is therefore a visible claims.yaml diff in the PR that caused it.

  * DIRECTED. `direction: down` = a ceiling that must fall (selector size,
    wildcard arms, mirror markers). `direction: up` = a floor that must rise
    (verified DSL rules).

  * SELF-BANKING. `baseline:` is the best value ever recorded. Move the number
    the GOOD way and the gate fails until `baseline:` is updated too — so an
    improvement cannot be silently given back later.

  * WAIVED, NOT ROUTED AROUND. Moving the number the BAD way is allowed, and
    that is the point: this is not a code-golf gate, it measures hand-maintained
    decisions, and a lane that legitimately needs to grow the file must be able
    to. It costs a `waivers:` entry whose `to:` equals the new value plus a
    written `reason:` — the #911 rule (say why, in the same PR) applied to size.
    Because the waiver is bound to a specific value, a SECOND regression needs a
    SECOND waiver; a waiver is not a standing licence.

  * SINGLE-DERIVATION. A ratchet names a `status_fields:` entry rather than
    carrying its own regex. The number is derived exactly once, flows to
    status.json, and is staleness-gated there. Re-deriving it here would make
    this gate a hand-maintained mirror of the thing it exists to count.

HONEST RESIDUAL, stated so nobody has to rediscover it: the checker is stateless
(no git history), so it enforces "worse than the best ever recorded needs a
waiver bound to this exact value", not "worse than last week". A regression past
an ALREADY-waived value still needs its own new waiver; a return to a previously
waived value does not. Every movement remains a ledger diff either way.

The ratchet predicate itself is unit-tested — `scripts/test_claim_check.py`,
wired in the claim-check CI job. v0.57's lesson was that the checkers are where
the defects are; a 60-line gate whose only validation is that it fired once is
the next one.
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


class MeasureError(Exception):
    """A derivation could not be performed as specified — never a silent 0."""


def _region(text, marker, where):
    """Truncate `text` at `marker`, which must occur EXACTLY ONCE.

    Absent marker => the derivation would silently widen to the whole file.
    Repeated marker => it would silently truncate at the wrong one, which is the
    FEATURE_MATRIX staleness failure (compare the render to the template, never
    the template to the code) wearing a different hat. Both are hard errors.
    """
    n = text.count(marker)
    if n != 1:
        raise MeasureError(
            f"{where}: region marker {marker!r} occurs {n} times, expected "
            f"exactly 1 — the measured region is undefined"
        )
    return text.split(marker, 1)[0]


def _count(pattern, globs, root, before=None, unit="matches"):
    """Count regex matches (or files-with-a-match) over globs.

    `before` restricts each file to the text preceding a unique marker — used to
    measure a source region (e.g. an instruction selector's non-test code)
    without the file's test module, so that adding tests never moves a size
    ceiling and a ledger bump therefore always MEANS something.
    """
    rx = re.compile(pattern, re.MULTILINE)
    globs = [globs] if isinstance(globs, str) else globs
    if unit not in ("matches", "files"):
        raise MeasureError(f"unknown count unit {unit!r} (matches|files)")
    total = 0
    matched_any = False
    for g in globs:
        # Resolve globs relative to the claims file's directory, NOT the CWD —
        # otherwise the predicate silently matches nothing and greens a claim
        # it never checked (the "oracle that measures nothing" failure).
        for f in sorted(glob.glob(str(root / g), recursive=True)):
            p = pathlib.Path(f)
            if p.is_file():
                matched_any = True
                text = p.read_text(errors="ignore")
                if before is not None:
                    text = _region(text, before, p.name)
                hits = len(rx.findall(text))
                total += min(hits, 1) if unit == "files" else hits
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
            try:
                n, matched = _count(
                    f["pattern"],
                    f["glob"],
                    root,
                    before=f.get("before"),
                    unit=f.get("unit", "matches"),
                )
            except MeasureError as e:
                raise RuntimeError(f"status field {name!r}: {e}") from e
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
                # ONE implementation of the region rule, shared with `count` —
                # a second copy here would be exactly the hand-maintained
                # mirror this file's RQ-58-METRIC block exists to count.
                try:
                    text = _region(text, marker, f["file"])
                except MeasureError as e:
                    raise RuntimeError(f"status field {name!r}: {e}") from e
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
# RQ-58-METRIC — the directed, slack-free ratchet (see the module docstring).
#
# A PURE function of (derived, spec) so it is unit-testable without touching the
# filesystem: `scripts/test_claim_check.py` drives every branch below. The gate
# whose thesis is "checkers are where the defects are" does not get to be the
# unvalidated one.
# ---------------------------------------------------------------------------

_RATCHET_HELP = (
    "the subtraction metric (epic #242) — see the RQ-58-METRIC block in "
    "scripts/claim_check.py"
)


def check_ratchet(derived, ev):
    """Return a list of failure strings for one `kind: ratchet` evidence item.

    `derived` is the live value of the `status_fields:` entry named by the pin;
    the pin itself carries NO regex, so the number is derived exactly once.
    """
    fails = []
    name = ev.get("name")
    direction = ev.get("direction")
    if direction not in ("up", "down"):
        return [f"ratchet {name!r}: direction must be 'up' or 'down', got {direction!r}"]
    for key in ("value", "baseline"):
        if not isinstance(ev.get(key), int) or isinstance(ev.get(key), bool):
            return [f"ratchet {name!r}: {key!r} must be an integer, got {ev.get(key)!r}"]
    value, baseline = ev["value"], ev["baseline"]
    goal = "ceiling that must FALL" if direction == "down" else "floor that must RISE"

    def worse_than_baseline(v):
        return v > baseline if direction == "down" else v < baseline

    def better_than_baseline(v):
        return v < baseline if direction == "down" else v > baseline

    # 1. SLACK-FREE. No "current + slack" ceiling is expressible: the ledger
    #    must carry the live number exactly, so every movement is a PR diff.
    if derived != value:
        moved = "the WRONG way" if worse_than_baseline(derived) else "the right way"
        fails.append(
            f"ratchet {name!r} MOVED {moved}: derived {derived} != ledger value "
            f"{value} (baseline {baseline}, {goal}) — update claims.yaml in the "
            f"SAME PR; if it moved the wrong way add a waivers: entry saying why "
            f"[{_RATCHET_HELP}]"
        )
        return fails  # everything below reasons about `value`; don't pile on.

    # 2. SELF-BANKING. An improvement must be recorded, or it can be silently
    #    given back later — which is how a ceiling rots into decoration.
    if better_than_baseline(value):
        fails.append(
            f"ratchet {name!r}: {value} beats baseline {baseline} but the win is "
            f"NOT BANKED — set `baseline: {value}` so it cannot be given back "
            f"without a waiver [{_RATCHET_HELP}]"
        )

    # 3. WAIVED, NOT ROUTED AROUND. Growth is allowed — it costs a written
    #    reason bound to this exact value (#911's rule applied to size).
    waivers = ev.get("waivers") or []
    if worse_than_baseline(value):
        matching = [w for w in waivers if w.get("to") == value]
        if not matching:
            fails.append(
                f"ratchet {name!r}: {value} is worse than baseline {baseline} "
                f"({goal}) with NO waiver — either delete a hand-written arm "
                f"instead, or add `waivers: [{{to: {value}, reason: ...}}]` in "
                f"THIS PR stating why the growth is justified [{_RATCHET_HELP}]"
            )
        for w in matching:
            if not str(w.get("reason", "")).strip():
                fails.append(
                    f"ratchet {name!r}: waiver to {value} has an EMPTY reason — a "
                    f"waiver is a stated justification, not a checkbox"
                )

    # 4. No dead waivers. A waiver whose value is already met is a standing
    #    licence nobody reviewed; same dead-entry rule as unpinned_ok.
    for w in waivers:
        to = w.get("to")
        if not isinstance(to, int) or isinstance(to, bool):
            fails.append(f"ratchet {name!r}: waiver `to` must be an integer, got {to!r}")
        elif not worse_than_baseline(to):
            fails.append(
                f"ratchet {name!r}: DEAD waiver to {to} — baseline is {baseline} "
                f"({goal}), so this waiver authorises nothing; delete it"
            )
    return fails


# ---------------------------------------------------------------------------
# Claim evidence predicates
# ---------------------------------------------------------------------------


def check_claim(c, root, status_spec, status=None):
    fails = []
    doc_path = root / c["doc"]
    if not doc_path.exists():
        return [f'doc not found: {c["doc"]}']
    doc = doc_path.read_text(errors="ignore")

    text = c.get("text")
    if text and text not in doc:
        fails.append(f'claim text not found verbatim in {c["doc"]}: "{text}"')

    status = status if status is not None else {}
    for ev in c.get("evidence", []):
        kind = ev.get("kind")
        try:
            fails += _check_evidence(ev, kind, c, doc, text, root, status_spec, status)
        except MeasureError as e:
            fails.append(f"derivation failed: {e}")
    return fails


def _check_evidence(ev, kind, c, doc, text, root, status_spec, status):
    fails = []
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
    elif kind == "ratchet":
        # SINGLE-DERIVATION: the pin names a status_fields entry; it does not
        # carry its own regex, so this gate cannot mirror-drift from the number
        # it publishes.
        name = ev.get("name")
        if name not in status_spec:
            fails.append(
                f"ratchet {name!r} names no status_fields derivation — a "
                f"directed pin MUST bind to the single derivation of its "
                f"number, never re-derive it here"
            )
        elif name not in status:
            fails.append(f"ratchet {name!r}: status derivation produced no value")
        elif not isinstance(status[name], int) or isinstance(status[name], bool):
            fails.append(
                f"ratchet {name!r}: derivation yields {status[name]!r}, not a "
                f"number — only counting derivations can be ratcheted"
            )
        else:
            fails += check_ratchet(status[name], ev)
    else:
        fails.append(f"unknown evidence kind: {kind!r}")
    return fails


def report_metric(claims, status):
    """Print the subtraction metric (RQ-58-METRIC) with its delta from baseline.

    A gate nobody can read is a gate nobody defends: CI prints this table on
    every run, so "the patch pile grew again" is visible in the job log rather
    than only in a red assertion.
    """
    rows = []
    for c in claims:
        for ev in c.get("evidence", []):
            if ev.get("kind") != "ratchet":
                continue
            name = ev.get("name")
            live = status.get(name)
            base = ev.get("baseline")
            arrow = "must FALL" if ev.get("direction") == "down" else "must RISE"
            delta = (live - base) if isinstance(live, int) and isinstance(base, int) else "?"
            if isinstance(delta, int):
                delta = f"{delta:+d}"
            rows.append((name, str(live), str(base), delta, arrow, len(ev.get("waivers") or [])))
    if not rows:
        # ANTI-VACUITY. Deleting the pins does not make a claim fail — an
        # evidence-less claim passes trivially — so the ABSENCE of the metric
        # has to be its own failure, or the easiest way to green this gate is
        # to remove it. (The exact POPULATION is pinned separately, by
        # SYNTH-SUBTRACTION-PINS-DECLARED, so removing just one is red too.)
        print(
            "subtraction metric: NO ratchet pins declared — the North Star is "
            "unmeasured. Restore them or this gate measures nothing."
        )
        return False
    w = max(len(r[0]) for r in rows)
    print(f"\n=== subtraction metric (epic #242) — {len(rows)} directed pins ===")
    print(f"{'metric'.ljust(w)}  {'now':>7}  {'baseline':>8}  {'delta':>6}  direction   waivers")
    for name, live, base, delta, arrow, nw in rows:
        print(f"{name.ljust(w)}  {live:>7}  {base:>8}  {delta:>6}  {arrow:<10}  {nw}")
    print()
    return True


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    emit = "--emit-status" in sys.argv[1:]
    metric = "--metric" in sys.argv[1:]
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
    if metric and not report_metric(claims, status):
        bad += 1

    for c in claims:
        fails = check_claim(c, root, status_spec, status)
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
