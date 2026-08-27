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
  fields-equal two or more DERIVED status fields must carry the same VALUE —
               pins hand-maintained copies of one constant against each other
               (count-same at the value level, so editing BOTH copies to the
               same wrong number cannot green it)

Derived-status field kinds (under `status_fields:`):

  count           len(regex findall) over globs (same engine as count-eq),
                  optionally truncated at a `before:` marker and optionally
                  counting FILES-with-a-match instead of matches (`unit: files`).
                  `before_missing: whole-file` makes the marker per-file-optional
                  (a file without it counts whole) so one field can measure a
                  FILE FAMILY — see the RQ-58-SPLIT note at `_region` for why
                  that opt-in does not reopen the silently-widen hole.
  capture         first regex capture group in one file (e.g. the version)
  distinct-tokens number of DISTINCT capture-group values in one file,
                  optionally truncated at a `before:` marker (e.g. the ops an
                  instruction selector handles, stopping before `mod tests`)
  json-list       a LIST of names selected out of a derived, freshness-gated
                  JSON artifact and rendered as prose (RQ-58-MIRRORS: a decline
                  list stops being hand-typed template prose and becomes a
                  substitution, so code drift moves the render). Fails loudly
                  when the selection matches nothing.
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

  * DIRECTED. `direction: down` = a ceiling that must fall (selector lowering
    code, its wildcard arms, mirror markers). `direction: up` = a floor that
    must rise (verified DSL rules). `direction: track` = slack-free but NOT
    directional — for a number quoted elsewhere that must not drift silently,
    but whose population is mixed enough that asserting a direction would file
    honest work (adding tests) in the waiver channel next to the growth the
    gate exists to catch.

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

class DuplicateKeyError(Exception):
    """A mapping declared the same key twice (#1087)."""


class StrictLoader(yaml.SafeLoader):
    """`yaml.safe_load` keeps the LAST value on a duplicate key, silently.

    That is not a hypothetical here. On main, `claims.yaml`'s
    `selector_lines_code` ratchet carried TWO `reason:` keys inside one
    waiver mapping: RQ-60-VFPPRESSURE increment 1 wrote an honest
    justification for a **+622 line** growth of the instruction selector,
    and last-wins silently replaced it with RQ-59-I64SHIFT's reason for a
    **+10 line** growth. The ledger then recorded — and this gate passed —
    a 622-line growth of the North Star's headline metric as permitted
    because ten lines were added to `select_default`. The waiver mechanism
    exists so every movement of a pinned number carries a written reason
    bound to that value; a duplicate key removes exactly that, and nothing
    downstream can tell, because what survives is a perfectly valid
    non-empty string.

    So this file is parsed duplicate-key-strict. This is the same loader
    discipline `scripts/status_evidence_check.py` applies to the release
    artifacts (#1059) — it was simply never pointed at the ledger, which is
    the one file every other claim in the repo is checked against.
    """


def _strict_mapping(loader: StrictLoader, node, deep: bool = False):
    seen: dict = {}
    for key_node, _ in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in seen:
            raise DuplicateKeyError(
                f"duplicate key {key!r}: declared at line {seen[key]} and "
                f"AGAIN at line {key_node.start_mark.line + 1} — YAML keeps "
                f"the LAST one silently, so the first value is discarded "
                f"with no diagnostic. Split the mapping (#1087)."
            )
        seen[key] = key_node.start_mark.line + 1
    return yaml.SafeLoader.construct_mapping(loader, node, deep)


StrictLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _strict_mapping
)


def strict_load(text: str, where: str):
    """Parse YAML, refusing the silent last-wins duplicate-key merge."""
    try:
        return yaml.load(text, Loader=StrictLoader)
    except DuplicateKeyError as exc:
        sys.exit(f"claim_check: {where}: {exc}")


STATUS_JSON = "artifacts/status.json"
FEATURE_MATRIX = "docs/status/FEATURE_MATRIX.md"
FEATURE_MATRIX_TMPL = "scripts/templates/feature_matrix.md.tmpl"


class MeasureError(Exception):
    """A derivation could not be performed as specified — never a silent 0."""


def _region(text, marker, where, missing="error"):
    """Truncate `text` at `marker`, which must occur EXACTLY ONCE.

    Absent marker => the derivation would silently widen to the whole file.
    Repeated marker => it would silently truncate at the wrong one, which is the
    FEATURE_MATRIX staleness failure (compare the render to the template, never
    the template to the code) wearing a different hat. Both are hard errors —
    unless the field OPTS IN with `before_missing: whole-file`, which makes an
    ABSENT marker mean "this whole file is the region". A repeated marker stays
    a hard error in both modes.

    WHY THE OPT-IN IS SAFE (RQ-58-SPLIT, #242): it exists so one `count` field
    can measure a FILE FAMILY — the selector's root file (whose test module the
    marker excludes) PLUS the split-out sibling files (all code, no marker).
    Without it, a split would either leave the ratchet measuring ONE file (a
    relocation then reads as a huge fake win — the vacuous-checker class this
    repo keeps finding) or hard-error on every marker-less sibling. The hole
    the hard error guards — a mangled marker silently widening the count by the
    whole test module — is still caught downstream: every consumer of these
    fields is a slack-free `ratchet` pin whose `value:` must EQUAL the live
    derivation, so a widening jump of thousands of lines is a loud red, not a
    silent green.
    """
    n = text.count(marker)
    if n == 0 and missing == "whole-file":
        return text
    if n != 1:
        raise MeasureError(
            f"{where}: region marker {marker!r} occurs {n} times, expected "
            f"exactly 1 — the measured region is undefined"
        )
    return text.split(marker, 1)[0]


def _count(pattern, globs, root, before=None, unit="matches", before_missing="error"):
    """Count regex matches (or files-with-a-match) over globs.

    `before` restricts each file to the text preceding a unique marker — used to
    measure a source region (e.g. an instruction selector's non-test code)
    without the file's test module, so that adding tests never moves a size
    ceiling and a ledger bump therefore always MEANS something.
    `before_missing="whole-file"` makes that marker per-file-optional (see
    `_region` for the safety argument); the default keeps an absent marker a
    hard error.
    """
    rx = re.compile(pattern, re.MULTILINE)
    globs = [globs] if isinstance(globs, str) else globs
    if unit not in ("matches", "files"):
        raise MeasureError(f"unknown count unit {unit!r} (matches|files)")
    if before_missing not in ("error", "whole-file"):
        raise MeasureError(
            f"unknown before_missing {before_missing!r} (error|whole-file)"
        )
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
                    text = _region(text, before, p.name, missing=before_missing)
                hits = len(rx.findall(text))
                total += min(hits, 1) if unit == "files" else hits
    return total, matched_any


def _yaml_field(ev, root):
    """Look up `field` of the list item whose `id` matches, in `path`."""
    path = root / ev["path"]
    if not path.exists():
        return None, f'yaml file missing: {ev["path"]}'
    data = strict_load(path.read_text(errors="ignore"), ev["path"]) or {}
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
                    before_missing=f.get("before_missing", "error"),
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
        elif kind == "json-list":
            # A LIST of names pulled out of a DERIVED, freshness-gated JSON
            # artifact and rendered into the template as prose. This is the
            # RQ-58-MIRRORS seam: a decline list, an op list or a capability
            # list stops being hand-typed template prose and becomes a
            # substitution, so code drift moves the render and
            # check_generated_fresh goes red.
            path = root / f["file"]
            if not path.exists():
                raise RuntimeError(
                    f"status field {name!r}: derived artifact missing: {f['file']}"
                )
            data = json.loads(path.read_text(errors="ignore"))
            items = data.get(f["list"])
            if not isinstance(items, list):
                raise RuntimeError(
                    f"status field {name!r}: {f['file']} has no list at "
                    f"key {f['list']!r}"
                )
            where = f.get("where") or {}
            vals = sorted(
                {
                    it[f["field"]]
                    for it in items
                    if isinstance(it, dict)
                    and f["field"] in it
                    and all(it.get(k) == v for k, v in where.items())
                }
            )
            if not vals:
                # An empty selection would render an empty phrase and green a
                # claim it never measured — the vacuous-derivation failure.
                raise RuntimeError(
                    f"status field {name!r}: selection {where!r} over "
                    f"{f['file']}:{f['list']} matched NOTHING"
                )
            w = f.get("wrap", "")
            out[name] = f.get("join", ", ").join(f"{w}{v}{w}" for v in vals)
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
# RQ-58-MIRRORS — TEMPLATE-vs-CODE coverage.
#
# `check_generated_fresh` above byte-compares the RENDERED feature matrix
# against the TEMPLATE. That proves the render is faithful to the template and
# says NOTHING about whether the template is faithful to the code — which is
# why v0.57 shipped three stale numbers behind a green 43/43, one of them a
# capability that release had shipped, listed as a loud decline.
#
# The repo already had the right MECHANISM (a claim whose `doc:` is the
# template, pinning prose to a re-derivation — #880). What it lacked was
# EXHAUSTIVENESS: nothing said which of the template's assertions were covered
# by it, so an unpinned number was indistinguishable from a pinned one.
#
# This gate supplies the missing half. Every NUMBER in the template must be
# accounted for as exactly one of:
#
#   DERIVED    inside a `{{field}}` substitution — status.json re-derives it
#              from source every run, and a drift fails check_generated_fresh
#   PINNED     inside the `text:`/`verbatim:` span of a claim whose `doc:` is
#              the template — some evidence predicate re-derives it
#   UNCHECKED  declared in `feature_matrix_facts.unchecked` WITH a rationale —
#              narrative prose that no derivation covers, named as such
#   MASKED     an identifier-shaped token that is not a measurement at all
#              (issue refs, type widths, target names, spec sections), each
#              mask declared with a `why:` in claims.yaml
#
# Anything left over is a number nobody classified: RED. The gate cannot prove
# a pinned or unchecked claim TRUE — it proves that every assertion has been
# put in one of those buckets on purpose, and it fails closed on new ones.
# The mask list is the residual trust; it is declared in claims.yaml so it is
# reviewable rather than buried here.
# ---------------------------------------------------------------------------

_NUM_RE = re.compile(r"(?<![\w.])\d[\d,]*(?:\.\d+)?(?![\w])")


def _blank(text, needle):
    """Replace every occurrence of `needle` with same-length NULs, so offsets
    (and therefore the surrounding context reported on failure) survive."""
    if not needle:
        return text, 0
    n = text.count(needle)
    return text.replace(needle, "\x00" * len(needle)), n


def check_template_facts(data, claims, root):
    fails = []
    cfg = data.get("feature_matrix_facts")
    if cfg is None:
        return ["claims.yaml has no `feature_matrix_facts:` section — the "
                "template-vs-code coverage gate is not configured"]

    tmpl = (root / FEATURE_MATRIX_TMPL).read_text()
    census = {"derived": 0, "pinned": 0, "unchecked": 0, "masked": 0}

    # 1. DERIVED — {{field}} substitutions.
    def _sub_blank(m):
        census["derived"] += 1
        return "\x00" * len(m.group(0))

    text = re.sub(r"\{\{(\w+)\}\}", _sub_blank, tmpl)

    # 2. PINNED — claim spans whose `doc:` is the template itself.
    for c in claims:
        if c.get("doc") != FEATURE_MATRIX_TMPL:
            continue
        spans = [c.get("text")]
        spans += [
            e.get("text")
            for e in c.get("evidence", [])
            if e.get("kind") == "verbatim"
        ]
        for s in spans:
            if not s:
                continue
            if s not in text and s not in tmpl:
                fails.append(
                    f"claim {c['id']} pins template text that is ABSENT: {s!r}"
                )
                continue
            text, n = _blank(text, s)
            census["pinned"] += n

    # 3. UNCHECKED — declared narrative prose, each with a rationale.
    for e in cfg.get("unchecked", []) or []:
        s = e.get("text", "")
        why = (e.get("rationale") or "").strip()
        if len(why) < 20:
            fails.append(
                f"feature_matrix_facts.unchecked entry {s[:40]!r} needs a "
                f">=20-char rationale saying WHY no derivation covers it"
            )
        if not any(ch.isdigit() for ch in s):
            fails.append(
                f"feature_matrix_facts.unchecked entry {s[:40]!r} contains no "
                f"number — the hatch exists for unpinnable ASSERTIONS, not for "
                f"blanking prose wholesale"
            )
        if len(s) > 240:
            fails.append(
                f"feature_matrix_facts.unchecked entry is {len(s)} chars — keep "
                f"an entry to the assertion (<=240), not a paragraph"
            )
        if s and s not in text:
            fails.append(
                f"feature_matrix_facts.unchecked entry no longer present in the "
                f"template (dead entry — delete it): {s[:60]!r}"
            )
            continue
        text, n = _blank(text, s)
        census["unchecked"] += n

    # 4. MASKED — identifier-shaped tokens that are not measurements.
    for m in cfg.get("masks", []) or []:
        why = (m.get("why") or "").strip()
        if len(why) < 20:
            fails.append(
                f"feature_matrix_facts.masks entry {m.get('pattern')!r} needs a "
                f">=20-char `why:` — the mask list is the residual trust in this "
                f"gate and must be reviewable"
            )
        try:
            rx = re.compile(m["pattern"])
        except re.error as exc:
            fails.append(f"feature_matrix_facts.masks pattern does not compile: {exc}")
            continue
        hits = 0

        def _mask_blank(mm):
            nonlocal hits
            hits += 1
            return "\x00" * len(mm.group(0))

        text = rx.sub(_mask_blank, text)
        if hits == 0:
            fails.append(
                f"feature_matrix_facts.masks pattern matches NOTHING (dead "
                f"mask — delete it): {m['pattern']!r}"
            )
        census["masked"] += hits

    # 5. Whatever is left is an unclassified assertion.
    for mm in _NUM_RE.finditer(text):
        s, e = mm.start(), mm.end()
        ctx = tmpl[max(0, s - 60) : min(len(tmpl), e + 60)].replace("\n", " ")
        fails.append(
            f"UNCLASSIFIED number {mm.group(0)!r} in the feature-matrix "
            f"template — make it a {{{{field}}}} substitution, pin it with a "
            f"claim whose doc: is the template, or declare it under "
            f"feature_matrix_facts.unchecked with a rationale.\n"
            f"        context: ...{ctx}..."
        )

    print(
        f"template-fact census: {census['derived']} derived · "
        f"{census['pinned']} pinned · {census['unchecked']} unchecked · "
        f"{census['masked']} masked identifier tokens"
    )

    # NON-VACUITY. Without this, the cheapest way to green the gate is to
    # DELETE the assertions — an empty template classifies perfectly. Floors
    # (>=, so adding coverage never reddens) on the two buckets that represent
    # real verification; the ratchet direction is up. Lower one only when
    # evidence genuinely weakened.
    floors = cfg.get("floors") or {}
    for bucket in ("derived", "pinned"):
        want = floors.get(bucket)
        if want is None:
            fails.append(
                f"feature_matrix_facts.floors has no {bucket!r} floor — the "
                f"exhaustiveness gate would pass over an emptied template"
            )
        elif census[bucket] < want:
            fails.append(
                f"feature-matrix {bucket} coverage FELL: {census[bucket]} < "
                f"recorded floor {want}. Verified assertions were removed from "
                f"the template — restore them, or lower the floor in the same "
                f"PR that says why the evidence weakened"
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
    if direction not in ("up", "down", "track"):
        return [
            f"ratchet {name!r}: direction must be 'up', 'down' or 'track', "
            f"got {direction!r}"
        ]
    if not isinstance(ev.get("value"), int) or isinstance(ev.get("value"), bool):
        return [f"ratchet {name!r}: 'value' must be an integer, got {ev.get('value')!r}"]

    # `track` — SLACK-FREE but NOT directional. For a number that is quoted
    # elsewhere and must not drift silently, yet whose direction we decline to
    # assert because the population is mixed. Concretely: the selector's
    # whole-file counts include its test module, so a PR that only adds test
    # coverage moves them. Demanding a WAIVER for that would file "added 40
    # lines of tests" alongside "grew the patch pile" in the same list, and a
    # waiver channel full of noise is a waiver channel nobody reads — which is
    # how a gate gets routed around. The directed pin is the region-scoped one.
    if direction == "track":
        if "baseline" in ev:
            fails.append(
                f"ratchet {name!r}: 'track' has no baseline to measure against "
                f"— remove the field rather than leaving one nothing reads"
            )
        if ev.get("waivers"):
            fails.append(
                f"ratchet {name!r}: 'track' cannot carry waivers — there is no "
                f"direction to waive, and an inert waiver reads as permission"
            )
        if derived != ev["value"]:
            fails.append(
                f"tracked number {name!r} MOVED: derived {derived} != ledger "
                f"value {ev['value']} — update claims.yaml in the SAME PR. NO "
                f"waiver needed: this pin asserts no direction (the directed "
                f"one is the region-scoped pin) [{_RATCHET_HELP}]"
            )
        return fails

    if not isinstance(ev.get("baseline"), int) or isinstance(ev.get("baseline"), bool):
        return [
            f"ratchet {name!r}: 'baseline' must be an integer, got {ev.get('baseline')!r}"
        ]
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
    elif kind == "fields-equal":
        # Two or more DERIVED fields must carry the same VALUE. This is
        # `count-same` at the value level: it pins two hand-maintained
        # copies of one constant against each other, and unlike a
        # count-same over a literal pattern it cannot go vacuously green
        # when BOTH copies are edited to the same wrong number.
        names = ev["names"]
        missing = [n for n in names if n not in status]
        if missing:
            fails.append(
                f"fields-equal names undeclared status field(s): {missing}"
            )
        else:
            seen = {n: status[n] for n in names}
            if len({str(v) for v in seen.values()}) > 1:
                fails.append(
                    "hand-maintained copies of one constant DISAGREE: "
                    + ", ".join(f"{n}={v}" for n, v in seen.items())
                    + " — update every copy together"
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
            arrow = {"down": "must FALL", "up": "must RISE"}.get(
                ev.get("direction"), "tracked"
            )
            if isinstance(live, int) and isinstance(base, int):
                delta, base_s = f"{live - base:+d}", str(base)
            else:
                # `track` pins have no baseline; print "—", never a bare None
                # next to a direction they do not have.
                delta, base_s = "—", "—"
            rows.append((name, str(live), base_s, delta, arrow, len(ev.get("waivers") or [])))
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
    data = strict_load(path.read_text(), str(path)) or {}
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
    extra += check_template_facts(data, claims, root)
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
