#!/usr/bin/env python3
"""RQ-72-VEX (#1359): emit a CycloneDX VEX beside the release SBOM.

WHY A VEX AND NOT JUST THE SBOM
-------------------------------
An SBOM says what is IN the product. It cannot say what an advisory MEANS for
it. A consumer pinned to a varve layer asks one question that nothing in the
ecosystem answers for a pinned toolchain: "is RUSTSEC-XXXX-YYYY present in what
I am actually running?"

The asymmetry is the whole argument for this living HERE rather than in varve:
varve can match components against an advisory DB from the outside, but it can
NEVER assert `not_affected because the vulnerable path is unreachable`. That is
a fact about THIS source tree, and only this repository can state it.

THE TRAP, AND THE RULE THAT AVOIDS IT
-------------------------------------
An auto-generated `not_affected` is a machine guess wearing a human assertion's
clothes, and `analysis.detail` is exactly where a plausible false claim would
sit and propagate — the defect class v0.62 measured, where one such claim
reached three files before anyone checked it.

So this emitter CANNOT invent a `not_affected`. It has exactly one source for
them: entries a human wrote in `deny.toml`'s `[advisories].ignore` as
`{ id = "...", reason = "..." }`. The reason is copied VERBATIM; the emitter
never composes one. An advisory with no such entry is `affected` with NO
justification, which is an honest answer and a better one than a fabricated
`vulnerable_code_not_in_execute_path`.

An ignore entry WITHOUT a reason is REFUSED outright: that is a `not_affected`
with no stated basis, which is the failure this rule exists to prevent.

POINT-IN-TIME, AND SAID SO
--------------------------
#1359 also asks for re-issue when a new advisory matches an already-shipped
release. That half is NOT built here. A document generated once and never
revisited carries a date that implies a currency it does not have — so the
emitted VEX says in its own metadata that it is a point-in-time statement and
names what would make it stale. Implying freshness we do not maintain would be
worse than the gap.
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def human_exemptions(deny_path: Path):
    """The ONLY source of `not_affected`. Returns {id: reason} and refuses any
    ignore entry that states no reason."""
    text = deny_path.read_text()
    m = re.search(r"^ignore\s*=\s*\[(.*?)^\]", text, re.S | re.M)
    if not m:
        return {}, []
    body = m.group(1)
    exemptions, unreasoned = {}, []
    for entry in re.finditer(r"\{\s*id\s*=\s*\"([^\"]+)\"\s*,\s*reason\s*=\s*\"((?:[^\"\\]|\\.)*)\"\s*\}", body):
        exemptions[entry.group(1)] = entry.group(2).encode().decode("unicode_escape")
    for bare in re.finditer(r'^\s*"([A-Z]+-\d{4}-\d{4})"\s*,', body, re.M):
        unreasoned.append(bare.group(1))
    return exemptions, unreasoned


def all_advisories(deny_path: Path):
    """Every advisory the DB reports for this workspace, ignore list DISABLED.

    Run against a temporary config whose `ignore` is empty, so an exempted
    advisory still APPEARS — a VEX that omitted the very advisories it exempts
    would answer the consumer's question with silence."""
    cfg = deny_path.read_text()
    cfg = re.sub(r"^ignore\s*=\s*\[.*?^\]", "ignore = []", cfg, flags=re.S | re.M)
    with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False) as fh:
        fh.write(cfg)
        tmp = fh.name
    out = subprocess.run(
        ["cargo", "deny", "--config", tmp, "--format", "json", "check", "advisories"],
        capture_output=True, text=True, cwd=ROOT)
    found = {}
    parsed = 0
    for line in (out.stdout + out.stderr).splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        parsed += 1
        f = d.get("fields", {})
        code = f.get("code") or ""
        blob = json.dumps(d)
        for aid in re.findall(r"(RUSTSEC-\d{4}-\d{4})", blob):
            found.setdefault(aid, {
                "id": aid,
                "message": f.get("message", ""),
                "severity": f.get("severity", "unknown"),
                "code": code,
            })
    # THE RETURN CODE IS READ. It was not, and the v0.72 round-2 gate-potency
    # cold review showed what that costs: with the advisory DB unreachable,
    # cargo-deny exits non-zero, `found` stays EMPTY, and this emitter happily
    # printed "0 advisory/ies" at rc=0. `ci.yml` happens to run a separate
    # `cargo deny check advisories` step first, so it is caught there —
    # `release.yml` does NOT (`grep -n 'cargo deny' release.yml` matches only
    # `cargo install`), and its only post-check is `test -s`, which passes on
    # `"vulnerabilities": []`. A transient fetch failure at release time would
    # have PUBLISHED AND COSIGNED a VEX asserting this release has no
    # advisories at all. Silence presented as an answer is exactly the failure
    # #1359 was filed to prevent.
    #
    # `parsed` is the floor: cargo-deny emits at least one JSON diagnostic on a
    # successful run (the summary), so zero parseable lines means the tool did
    # not run rather than that the workspace is clean.
    if out.returncode != 0 and not parsed:
        raise SystemExit(
            f"emit_vex: cargo-deny exited {out.returncode} and produced no "
            f"parseable diagnostics — REFUSING to emit a VEX that would assert "
            f"no advisories when the check did not run.\n"
            + (out.stderr or out.stdout)[-1200:])
    if not parsed:
        raise SystemExit(
            "emit_vex: cargo-deny produced NO parseable JSON diagnostics. "
            "An empty advisory set and a check that never ran are "
            "indistinguishable in the output, so this refuses rather than "
            "emit a document that cannot be told apart from silence.")
    return found


def advisory_db_commit():
    """#1359 ask 3: WHICH advisory database produced these answers.

    cargo-deny clones RustSec's advisory-db under
    `$CARGO_HOME/advisory-dbs/<host>-<hash>`. The commit of that checkout is
    what makes a `not_affected` checkable six months later: without it the
    document records an opinion with no stated basis.

    Returns a string that is ALWAYS usable as a property value. When the
    checkout cannot be located the value says so IN THE DOCUMENT — an omitted
    property is indistinguishable from one nobody checked, and a VEX is
    precisely a document where that distinction is the whole point.
    """
    cargo_home = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))
    dbs = cargo_home / "advisory-dbs"
    if not dbs.is_dir():
        return f"unavailable: no advisory-db checkout under {dbs}"
    checkouts = sorted(d for d in dbs.iterdir() if (d / ".git").exists())
    if not checkouts:
        return f"unavailable: {dbs} holds no git checkout"
    if len(checkouts) > 1:
        # Ambiguity is reported, never silently resolved by picking one.
        return ("unavailable: " + str(len(checkouts)) + " advisory-db checkouts "
                "under " + str(dbs) + " — cannot say which one produced this")
    r = subprocess.run(["git", "-C", str(checkouts[0]), "rev-parse", "HEAD"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return f"unavailable: git rev-parse failed in {checkouts[0]}"
    return r.stdout.strip()


def build_vex(version: str, exemptions, advisories):
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    vulns = []
    for aid in sorted(advisories):
        adv = advisories[aid]
        entry = {
            "id": aid,
            "source": {"name": "RUSTSEC",
                       "url": f"https://rustsec.org/advisories/{aid}"},
            "description": adv.get("message", ""),
        }
        if aid in exemptions:
            # NO `justification` KEY. The v0.72 round-2 cold review found this
            # emitting a hardcoded `"justification": "code_not_reachable"` for
            # EVERY exemption, whatever the human's reason actually said —
            # while this file, the artifact and `release.yml` all claimed "the
            # emitter composes no justification", and that claim was itself
            # written INTO the signed document.
            #
            # #1359 ask 5, verbatim: "`not_affected` **must not** be
            # auto-asserted — a justification like
            # `vulnerable_code_not_in_execute_path` is a human judgement, and a
            # generated one is a false statement signed into a release."
            # `code_not_reachable` is the CycloneDX spelling of exactly that
            # claim, so emitting it from a template was the precise failure the
            # ask names.
            #
            # `justification` is OPTIONAL in CycloneDX 1.5. The human's reason
            # is carried VERBATIM in `detail`, which is what a consumer reads;
            # an enum nobody chose adds no information and asserts a specific
            # mechanism. If a justification enum is wanted later it must come
            # from the human, in deny.toml, beside the reason.
            entry["analysis"] = {
                "state": "not_affected",
                # VERBATIM from the human. The emitter composes nothing here.
                "detail": exemptions[aid],
            }
        else:
            # No fabricated justification. `affected` with nothing further is
            # the honest answer when nobody has asserted otherwise.
            entry["analysis"] = {"state": "affected"}
        vulns.append(entry)
    return {
        "bomFormat": "CycloneDX",
        "specVersion": "1.5",
        "version": 1,
        "metadata": {
            "timestamp": now,
            "component": {"type": "application", "name": "synth",
                          "version": version},
            "properties": [
                # #1359 ask 3, "Name what made it true": the database commit and
                # the assertion time. Emitted with the issue's OWN property
                # names so a consumer's parser needs no synth-specific mapping.
                {"name": "advisory-db.commit", "value": advisory_db_commit()},
                {"name": "asserted-at", "value": now},
                {"name": "synth:vex:point-in-time",
                 "value": (f"Generated {now} against the advisory database as of that "
                           "moment. This document is NOT re-issued when a new advisory "
                           "later matches this release; a consumer must re-check "
                           "against a current database. Stated because a document that "
                           "is never revisited carries a date implying a currency it "
                           "does not have.")},
                {"name": "synth:vex:not-affected-source",
                 "value": ("Every `not_affected` comes from a human-written "
                           "`{ id, reason }` entry in deny.toml; the reason is copied "
                           "verbatim into `analysis.detail`. NO `justification` "
                           "enum is emitted: CycloneDX makes it optional, and a "
                           "generated one would assert a mechanism no human "
                           "chose. The emitter composes nothing, and "
                           "refuses an ignore entry that states no reason.")},
            ],
        },
        "vulnerabilities": vulns,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--version", required=True)
    ap.add_argument("--deny", default=str(ROOT / "deny.toml"), type=Path)
    ap.add_argument("-o", "--out")
    args = ap.parse_args()

    exemptions, unreasoned = human_exemptions(Path(args.deny))
    if unreasoned:
        print(f"REFUSE: {len(unreasoned)} ignore entr(ies) state no reason: "
              f"{unreasoned}. An exemption with no stated basis becomes a "
              f"`not_affected` nobody can check — write "
              f"`{{ id = \"...\", reason = \"...\" }}` or remove it.")
        return 1

    advisories = all_advisories(Path(args.deny))
    doc = build_vex(args.version, exemptions, advisories)
    text = json.dumps(doc, indent=2) + "\n"
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)

    n_na = sum(1 for v in doc["vulnerabilities"] if v["analysis"]["state"] == "not_affected")
    n_af = len(doc["vulnerabilities"]) - n_na
    print(f"vex: {len(doc['vulnerabilities'])} advisory/ies — "
          f"{n_na} not_affected (human-asserted), {n_af} affected",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
