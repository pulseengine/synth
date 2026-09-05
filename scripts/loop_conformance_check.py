#!/usr/bin/env python3
"""RQ-62-LOOPCONFORM (#1136) — derive a release's feature-loop conformance.

Why this exists
-----------------------------------------------------------------------------
The maintainer's standing release authorization (2026-09-02) is CONDITIONAL:
"yes it stands for all releases IF they run through the feature loop." Until
this script, the only evidence a release ran the loop was that whoever cut it
said so — a self-assessment gating a standing authorization, the exact shape
this project removed five times (#1085 evidence that could not fail, #1091 a
gate that printed instead of asserting, #1113 a floor blind to half its
oracle, #1119 a rule blind to a delivery-commit shape, #1133 a gate whose
scope excluded the file recording programme status).

This gate JOINS traces that already exist — it invents no new attestation
surface. Every DERIVED line below names the artifact it read: a file in the
release ref's tree, a CI check-run conclusion on the release commit, a
workflow run on the tag, a crates.io index entry. Nothing here is a statement
by the person cutting the release.

The one question, at the one moment
-----------------------------------------------------------------------------
"Did THIS release run the feature loop?" — asked BEFORE a tag (mode=pretag,
ref=HEAD, gating the tag about to be cut) or retroactively about a cut
release (mode=retro, ref=the tag, auditing what the tag actually carried).
This is NOT a merge gate and does not re-litigate what the loop contains.

    usage: python3 scripts/loop_conformance_check.py vX.Y.Z [--json OUT]

Exit 0 = conforms; exit 1 = at least one step's trace is missing or red.

Step derivations (loop step numbers from [pulseengine-feature-loop])
-----------------------------------------------------------------------------
steps 1-2  spar AADL -> WIT. NOT a blank and NOT a permanent exemption.
           PASS only if (a) a synth-owned .aadl architecture model is tracked
           in-repo (the real trace, once RQ-62-ARCHMODEL builds it), or (b)
           the recurring N/A cites a FILED, referenced decision — a release
           artifact tagged {feature-loop + aadl|spar} carrying a fields.issue
           (today: RQ-62-ARCHMODEL, the #1136 maintainer decision "not
           permanently N/A; timing first"). An unfiled N/A is RED — that IS
           the #1136 class. Evaluated at the CHECKOUT, not the release ref,
           because a filed decision is programme-scoped: #1136 covers every
           release's historical N/A the moment it is decided, and un-files
           none of them if reverted.
step 3     rivet. The release's artifact set is VISIBLE (>=1 artifact; the
           #1064 zero-artifact shape is red), every artifact declares
           fields.done-when (the RQ-60-FLIPCOUPLE evidenced-status regime),
           and scripts/status_evidence_check.py exists AND is wired in ci.yml
           at the release ref. Run evidence: the required "Claim Check"
           check-run concluded success on the release commit (retro) / the
           gate exits 0 right now (pretag).
step 4     oracle-gated. scripts/oracle_wiring_check.py exists at the ref and
           ci.yml invokes it WITH a nonzero --min-emulation-floor (the #910/
           #1113 ratchet — wiring without a floor is presence, not potency).
           Run evidence: same "Claim Check" run (the wiring gate executes
           inside it) / a live exit-0 run against the ci-pinned floor.
step 5     witness MC/DC. scripts/mcdc_gate.py exists at the ref, carries the
           BRANCH_POPULATION pin (#1100 — the gate without the pin cannot see
           a deleted branch), ci.yml wires it, AND the "MC/DC structural
           coverage" check-run concluded success on the release commit.
step 6     sigil. signing-e2e.yml exists at the ref with a v* tag trigger,
           and a completed "Signing E2E" workflow run on the release commit
           concluded success (retro: the tag's own run; pretag: the latest
           completed main run of the same workflow, since the tag run is
           created by the tag push this gate precedes).
step 7     clean-room review. DERIVED only if docs/reviews/ at the ref holds
           a record for this release naming a reviewed commit that is an
           ancestor of (or equal to) the release commit. Required from v0.62
           (the release that introduces this gate); earlier releases report
           ATTESTED-NOT-DERIVED — their reviews happened (v0.61: 2
           SHOULD-FIXes, both fixed pre-tag) but left no machine-readable
           record, and a regime cannot demand records from before it existed
           (#1091 decided the same boundary for done-when backfill). The
           record's PRESENCE, its reviewed-sha, and its committed-before-tag
           ordering are mechanical; the reviewer's INDEPENDENCE remains
           attested inside the record — stated here so nobody mistakes the
           derived part for more than it is.
step 8     release-exec. Pin sweep: scripts/check_version_pins.py exists and
           the "Version Pin Sweep" check-run concluded success on the release
           commit (retro) / exits 0 now (pretag). Crates live: every crate in
           the ref's own scripts/publish.rs CRATES_TO_PUBLISH list resolves
           on crates.io at this version (retro; pretag reports NA-BY-MOMENT —
           publish happens after the tag, so demanding it pre-tag would be
           inventing evidence). PR-head-vs-merge diff = 0 is ATTESTED, not
           derived: squash-merge head refs are not durably fetchable at audit
           time; record the result in the step-7 review record. A negative
           result is a real result — these two are labeled, not proxied.

Non-vacuity of the verdict itself
-----------------------------------------------------------------------------
CONFORMS requires zero failures AND >= 4 step-slots DERIVED — a run that
derived nothing (offline, gh missing, API dead) must not pass on attestations
alone. Red-first evidence: scripts/repro/loop_conformance_1136_gate.md holds
transcripts — GREEN on v0.61.0, RED on v0.57.0 (evidenced-status regime and
BRANCH_POPULATION pin postdate it) and on v0.56.2 (predates the witness gate
entirely). scripts/test_loop_conformance_check.py unit-tests every
derivation branch on fixtures, no network.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    print("loop-conformance: FATAL — PyYAML required", file=sys.stderr)
    sys.exit(1)

REPO_DEFAULT = "pulseengine/synth"
# The release that introduces this gate; the step-7 review record and this
# check itself are required from here on (regime boundary, see docstring).
REVIEW_REGIME_START = (0, 62)
# Verdict non-vacuity: a CONFORMS with fewer derived step-slots than this is
# refused — it would mean the verdict rests on attestations, not traces.
MIN_DERIVED_SLOTS = 4

# Finding statuses. FAILING statuses red the verdict; the others are printed
# loudly but honestly do not pretend to be derivations.
DERIVED_PASS = "DERIVED-PASS"
DERIVED_FAIL = "DERIVED-FAIL"
NOT_DERIVED = "NOT-DERIVED"  # trace should exist but could not be read
ATTESTED = "ATTESTED"  # honest non-derivation, reason given
NA_FILED = "NA-FILED"  # N/A citing a filed, referenced decision
NA_MOMENT = "NA-BY-MOMENT"  # evidence structurally postdates this moment
FAILING = {DERIVED_FAIL, NOT_DERIVED}

STEP_NAMES = [
    ("1-2", "spar AADL->WIT"),
    ("3", "rivet artifacts"),
    ("4", "oracle-gated"),
    ("5", "witness MC/DC"),
    ("6", "sigil signing"),
    ("7", "clean-room review"),
    ("8", "release-exec"),
]


def run(cmd: list[str]) -> tuple[int, str]:
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr)


def git(*args: str) -> tuple[int, str]:
    return run(["git", *args])


def tree_has(ref: str, path: str) -> bool:
    rc, _ = git("cat-file", "-e", f"{ref}:{path}")
    return rc == 0


def tree_read(ref: str, path: str) -> str | None:
    rc, out = git("show", f"{ref}:{path}")
    return out if rc == 0 else None


def tree_ls(ref: str, path: str) -> list[str]:
    rc, out = git("ls-tree", "--name-only", ref, path)
    if rc != 0:
        return []
    return [line for line in out.splitlines() if line.strip()]


def gh_api(path: str) -> object | None:
    rc, out = run(["gh", "api", path])
    if rc != 0:
        return None
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return None


def http_status(url: str) -> int:
    # crates.io rejects requests without a User-Agent (measured, v0.58 hub).
    req = urllib.request.Request(
        url, headers={"User-Agent": "synth-loop-conformance-check (pulseengine/synth)"}
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return resp.status
    except urllib.error.HTTPError as e:
        return e.code
    except (urllib.error.URLError, OSError):
        return 0


# ---------------------------------------------------------------------------
# Pure derivation helpers (unit-tested on fixtures, no git / no network).
# ---------------------------------------------------------------------------


def find_filed_steps12_decision(docs: list[tuple[str, object]]) -> dict | None:
    """A filed steps-1-2 decision: a release artifact tagged feature-loop AND
    aadl|spar, carrying a non-empty fields.issue. Matched by SHAPE, not by a
    hardcoded id, so the citation is to the artifact that actually exists."""
    for fname, doc in docs:
        if not isinstance(doc, dict):
            continue
        for a in doc.get("artifacts") or []:
            if not isinstance(a, dict):
                continue
            tags = set(a.get("tags") or [])
            issue = str((a.get("fields") or {}).get("issue") or "").strip()
            if "feature-loop" in tags and tags & {"aadl", "spar"} and issue:
                return {
                    "id": a.get("id"),
                    "issue": issue,
                    "status": a.get("status"),
                    "file": fname,
                }
    return None


def artifacts_missing_done_when(docs: list[tuple[str, object]]) -> tuple[int, list[str]]:
    """Count visible release artifacts and list ids lacking fields.done-when."""
    total = 0
    missing: list[str] = []
    for _fname, doc in docs:
        if not isinstance(doc, dict):
            continue
        for a in doc.get("artifacts") or []:
            if not isinstance(a, dict):
                continue
            total += 1
            dw = str((a.get("fields") or {}).get("done-when") or "").strip()
            if not dw:
                missing.append(str(a.get("id")))
    return total, missing


def ci_emulation_floor(ci_text: str) -> int:
    """The pinned oracle floor in ci.yml; 0 when absent (presence != potency)."""
    m = re.search(r"--min-emulation-floor\s+(\d+)", ci_text)
    return int(m.group(1)) if m else 0


def signing_workflow_tag_triggered(wf_text: str) -> bool:
    m = re.search(r"^on:\s*$(.*?)^\S", wf_text, re.M | re.S)
    body = m.group(1) if m else wf_text
    return bool(re.search(r"tags:\s*(\n\s*-\s*[\"']?v\*|\s*\[[^\]]*v\*)", body))


def review_record_shas(text: str) -> list[str]:
    """Candidate reviewed-commit shas named by a cold-review record."""
    return re.findall(r"\b[0-9a-f]{8,40}\b", text)


# ---------------------------------------------------------------------------
# The check itself.
# ---------------------------------------------------------------------------


class Check:
    def __init__(self, version: str, repo: str):
        m = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)", version)
        if not m:
            raise SystemExit(f"loop-conformance: version must be vX.Y.Z, got {version!r}")
        self.version = version
        self.bare_version = version[1:]
        self.majmin = (int(m.group(1)), int(m.group(2)))
        self.rid = f"v{m.group(1)}.{m.group(2)}"
        self.repo = repo
        self.findings: list[tuple[str, str, str, str]] = []  # (step, label, status, detail)

        rc, out = git("rev-parse", "--verify", "-q", f"{version}^{{commit}}")
        if rc == 0:
            self.mode = "retro"
            self.ref = version
            self.sha = out.strip()
        else:
            self.mode = "pretag"
            self.ref = "HEAD"
            _, out = git("rev-parse", "HEAD")
            self.sha = out.strip()

    def add(self, step: str, label: str, status: str, detail: str) -> None:
        self.findings.append((step, label, status, detail))

    # -- evidence loading ---------------------------------------------------

    def load_release_docs(self) -> list[tuple[str, object]]:
        """The release's artifact files as seen AT THE RELEASE REF."""
        docs: list[tuple[str, object]] = []
        for path in tree_ls(self.ref, f"artifacts/release-{self.rid}/"):
            if not path.endswith((".yaml", ".yml")):
                continue
            if Path(path).name in ("_release.yaml", "_release.yml"):
                continue  # comments-only by rule; status_evidence_check polices it
            text = tree_read(self.ref, path)
            if text is not None:
                docs.append((path, self._safe_yaml(path, text)))
        flat = f"artifacts/release-{self.rid}.yaml"
        text = tree_read(self.ref, flat)
        if text is not None:
            docs.append((flat, self._safe_yaml(flat, text)))
        return docs

    def load_checkout_docs(self) -> list[tuple[str, object]]:
        """ALL release-artifact files in the checkout (programme-scoped scan)."""
        docs: list[tuple[str, object]] = []
        root = Path(".")
        for p in sorted(root.glob("artifacts/release-v*")):
            if p.is_dir():
                for f in sorted(p.glob("*.yam*")):
                    docs.append((str(f), self._safe_yaml(str(f), f.read_text())))
            elif p.suffix in (".yaml", ".yml"):
                docs.append((str(p), self._safe_yaml(str(p), p.read_text())))
        return docs

    @staticmethod
    def _safe_yaml(name: str, text: str) -> object:
        try:
            return yaml.safe_load(text)
        except yaml.YAMLError:
            return None

    def check_run_conclusion(self, name_prefix: str) -> str | None:
        """Conclusion of the check-run named (by prefix) on the release commit."""
        data = gh_api(f"repos/{self.repo}/commits/{self.sha}/check-runs?per_page=100")
        if not isinstance(data, dict):
            return None
        for cr in data.get("check_runs") or []:
            if str(cr.get("name", "")).startswith(name_prefix):
                return cr.get("conclusion") or "pending"
        return "absent"

    # -- steps --------------------------------------------------------------

    def step_1_2(self) -> None:
        rc, out = git("ls-files", "*.aadl")
        aadl = [line for line in out.splitlines() if line.strip()] if rc == 0 else []
        if aadl:
            self.add(
                "1-2",
                "architecture model",
                DERIVED_PASS,
                f"synth-owned AADL model tracked in-repo: {', '.join(aadl[:3])}",
            )
            return
        decision = find_filed_steps12_decision(self.load_checkout_docs())
        if decision:
            self.add(
                "1-2",
                "filed decision",
                NA_FILED,
                "decided, artifact scoped, not yet built: "
                f"{decision['id']} ({decision['issue']}, status {decision['status']}) "
                f"in {decision['file']} [programme-scoped, evaluated at checkout]",
            )
        else:
            self.add(
                "1-2",
                "filed decision",
                DERIVED_FAIL,
                "no AADL model and no filed steps-1-2 decision artifact "
                "(tags feature-loop + aadl|spar with fields.issue) — an N/A "
                "asserted fresh by whoever is cutting is the #1136 class",
            )

    def step_3(self) -> None:
        docs = self.load_release_docs()
        total, missing = artifacts_missing_done_when(docs)
        if total == 0:
            self.add(
                "3",
                "artifact set",
                DERIVED_FAIL,
                f"no visible release artifacts for {self.rid} at {self.ref} "
                "(the #1064 zero-artifact shape)",
            )
        elif missing:
            self.add(
                "3",
                "done-when regime",
                DERIVED_FAIL,
                f"{len(missing)}/{total} artifacts lack fields.done-when "
                f"(evidenced-status regime, RQ-60-FLIPCOUPLE): {', '.join(missing[:5])}"
                + ("..." if len(missing) > 5 else ""),
            )
        else:
            self.add("3", "artifact set", DERIVED_PASS, f"{total} artifacts, {total}/{total} done-when")

        ci = tree_read(self.ref, ".github/workflows/ci.yml") or ""
        if tree_has(self.ref, "scripts/status_evidence_check.py") and "status_evidence_check.py" in ci:
            self.add("3", "status-evidence gate", DERIVED_PASS, "present and wired in ci.yml at ref")
        else:
            self.add(
                "3",
                "status-evidence gate",
                DERIVED_FAIL,
                "scripts/status_evidence_check.py absent or unwired at ref",
            )

        if self.mode == "retro":
            concl = self.check_run_conclusion("Claim Check")
            if concl == "success":
                self.add("3", "Claim Check ran", DERIVED_PASS, f"check-run success on {self.sha[:8]}")
            else:
                self.add(
                    "3",
                    "Claim Check ran",
                    NOT_DERIVED if concl is None else DERIVED_FAIL,
                    f"check-run on {self.sha[:8]}: {concl or 'API unavailable'}",
                )
        else:
            rc, _ = run([sys.executable, "scripts/status_evidence_check.py"])
            self.add(
                "3",
                "status-evidence live run",
                DERIVED_PASS if rc == 0 else DERIVED_FAIL,
                f"exit {rc}",
            )

    def step_4(self) -> None:
        ci = tree_read(self.ref, ".github/workflows/ci.yml") or ""
        floor = ci_emulation_floor(ci)
        if tree_has(self.ref, "scripts/oracle_wiring_check.py") and floor > 0:
            self.add(
                "4",
                "oracle wiring + floor",
                DERIVED_PASS,
                f"wired with --min-emulation-floor {floor} at ref",
            )
        else:
            self.add(
                "4",
                "oracle wiring + floor",
                DERIVED_FAIL,
                "oracle_wiring_check.py absent, unwired, or floor-less at ref "
                "(presence is not potency, #1113)",
            )
        if self.mode == "retro":
            concl = self.check_run_conclusion("Claim Check")
            status = DERIVED_PASS if concl == "success" else (NOT_DERIVED if concl is None else DERIVED_FAIL)
            self.add(
                "4",
                "wiring gate ran",
                status,
                f"via Claim Check check-run on {self.sha[:8]}: {concl or 'API unavailable'}",
            )
        else:
            rc, _ = run(
                [
                    sys.executable,
                    "scripts/oracle_wiring_check.py",
                    "--min-emulation-floor",
                    str(floor),
                ]
            )
            self.add("4", "wiring gate live run", DERIVED_PASS if rc == 0 else DERIVED_FAIL, f"exit {rc}")

    def step_5(self) -> None:
        gate = tree_read(self.ref, "scripts/mcdc_gate.py")
        ci = tree_read(self.ref, ".github/workflows/ci.yml") or ""
        if gate is None or "mcdc_gate.py" not in ci:
            self.add("5", "mcdc gate", DERIVED_FAIL, "scripts/mcdc_gate.py absent or unwired at ref")
        elif "BRANCH_POPULATION" not in gate:
            self.add(
                "5",
                "mcdc gate",
                DERIVED_FAIL,
                "gate present but carries no BRANCH_POPULATION pin at ref "
                "(#1100 — without the pin a deleted branch is invisible)",
            )
        else:
            self.add("5", "mcdc gate", DERIVED_PASS, "present, wired, BRANCH_POPULATION-pinned at ref")

        concl = self.check_run_conclusion("MC/DC structural coverage")
        if concl == "success":
            self.add("5", "mcdc ran on commit", DERIVED_PASS, f"check-run success on {self.sha[:8]}")
        else:
            self.add(
                "5",
                "mcdc ran on commit",
                NOT_DERIVED if concl is None else DERIVED_FAIL,
                f"check-run on {self.sha[:8]}: {concl or 'API unavailable'}"
                + (" — push the candidate and let CI finish" if self.mode == "pretag" else ""),
            )

    def step_6(self) -> None:
        wf = tree_read(self.ref, ".github/workflows/signing-e2e.yml")
        if wf is None or not signing_workflow_tag_triggered(wf):
            self.add(
                "6",
                "signing workflow",
                DERIVED_FAIL,
                "signing-e2e.yml absent or not v*-tag-triggered at ref",
            )
        else:
            self.add("6", "signing workflow", DERIVED_PASS, "present with v* tag trigger at ref")

        if self.mode == "retro":
            data = gh_api(
                f"repos/{self.repo}/actions/workflows/signing-e2e.yml/runs?head_sha={self.sha}"
            )
            runs = (data or {}).get("workflow_runs") if isinstance(data, dict) else None
            if runs is None:
                self.add("6", "Signing E2E ran", NOT_DERIVED, "API unavailable")
            else:
                ok = [r for r in runs if r.get("conclusion") == "success"]
                if ok:
                    where = ", ".join(sorted({str(r.get("head_branch")) for r in ok}))
                    self.add(
                        "6",
                        "Signing E2E ran",
                        DERIVED_PASS,
                        f"success on {self.sha[:8]} (runs: {where})",
                    )
                else:
                    self.add(
                        "6",
                        "Signing E2E ran",
                        DERIVED_FAIL,
                        f"no successful Signing E2E run on {self.sha[:8]} "
                        f"({len(runs)} runs found)",
                    )
        else:
            data = gh_api(
                f"repos/{self.repo}/actions/workflows/signing-e2e.yml/runs"
                "?branch=main&status=completed&per_page=1"
            )
            runs = (data or {}).get("workflow_runs") if isinstance(data, dict) else None
            if not runs:
                self.add("6", "Signing E2E (pre-tag form)", NOT_DERIVED, "API unavailable or no runs")
            elif runs[0].get("conclusion") == "success":
                self.add(
                    "6",
                    "Signing E2E (pre-tag form)",
                    DERIVED_PASS,
                    f"latest completed main run success ({runs[0].get('created_at')}); "
                    "the tag's own run is created by the tag push this gate precedes",
                )
            else:
                self.add(
                    "6",
                    "Signing E2E (pre-tag form)",
                    DERIVED_FAIL,
                    f"latest completed main run concluded {runs[0].get('conclusion')}",
                )

    def step_7(self) -> None:
        candidates = [
            p
            for p in tree_ls(self.ref, "docs/reviews/")
            if self.rid in p or self.version in p
        ]
        if candidates:
            text = tree_read(self.ref, candidates[0]) or ""
            for sha in review_record_shas(text):
                rc_eq, full = git("rev-parse", "--verify", "-q", f"{sha}^{{commit}}")
                if rc_eq != 0:
                    continue
                full = full.strip()
                rc_anc, _ = git("merge-base", "--is-ancestor", full, self.sha)
                if rc_anc == 0 or full == self.sha:
                    self.add(
                        "7",
                        "cold-review record",
                        DERIVED_PASS,
                        f"{candidates[0]} names reviewed commit {sha[:12]} "
                        f"(ancestor of release commit); reviewer independence "
                        "remains attested inside the record",
                    )
                    return
            self.add(
                "7",
                "cold-review record",
                DERIVED_FAIL,
                f"{candidates[0]} exists but names no commit that is an "
                "ancestor of the release commit",
            )
        elif self.majmin >= REVIEW_REGIME_START:
            self.add(
                "7",
                "cold-review record",
                DERIVED_FAIL,
                f"no docs/reviews/ record for {self.rid} at {self.ref}; write "
                f"docs/reviews/{self.rid}-cold-review.md naming the reviewed "
                "commit and the findings (required from v0.62)",
            )
        else:
            self.add(
                "7",
                "cold-review record",
                ATTESTED,
                f"pre-{'.'.join(map(str, REVIEW_REGIME_START))} release: review "
                "happened but left no machine-readable record; record regime "
                "starts v0.62 (#1091 decided the same boundary for done-when)",
            )

    def step_8(self) -> None:
        if not tree_has(self.ref, "scripts/check_version_pins.py"):
            self.add("8", "pin sweep", DERIVED_FAIL, "scripts/check_version_pins.py absent at ref")
        elif self.mode == "retro":
            concl = self.check_run_conclusion("Version Pin Sweep")
            status = DERIVED_PASS if concl == "success" else (NOT_DERIVED if concl is None else DERIVED_FAIL)
            self.add(
                "8",
                "pin sweep",
                status,
                f"Version Pin Sweep check-run on {self.sha[:8]}: {concl or 'API unavailable'}",
            )
        else:
            rc, _ = run([sys.executable, "scripts/check_version_pins.py"])
            self.add("8", "pin sweep live run", DERIVED_PASS if rc == 0 else DERIVED_FAIL, f"exit {rc}")

        self.add(
            "8",
            "PR-head-vs-merge diff",
            ATTESTED,
            "squash-merge head refs are not durably fetchable at audit time; "
            "run `git diff <PR head> <merged commit>` = 0 lines pre-tag and "
            "record the result in the step-7 review record",
        )

        if self.mode == "pretag":
            self.add(
                "8",
                "crates live",
                NA_MOMENT,
                "publish happens after the tag; demanding it pre-tag would "
                "invent evidence — audited by retro mode",
            )
            return
        pub = tree_read(self.ref, "scripts/publish.rs") or ""
        m = re.search(r"CRATES_TO_PUBLISH[^=]*=\s*&\[(.*?)\];", pub, re.S)
        crates = re.findall(r'"([a-z0-9-]+)"', m.group(1)) if m else []
        if not crates:
            self.add("8", "crates live", NOT_DERIVED, "CRATES_TO_PUBLISH not parseable at ref")
            return
        dead = []
        checked = 0
        for c in crates:
            code = http_status(f"https://crates.io/api/v1/crates/{c}/{self.bare_version}")
            if code == 0:
                self.add("8", "crates live", NOT_DERIVED, f"crates.io unreachable checking {c}")
                return
            checked += 1
            if code != 200:
                dead.append(f"{c} ({code})")
        if dead:
            self.add(
                "8",
                "crates live",
                DERIVED_FAIL,
                f"{len(dead)}/{checked} not live at {self.bare_version}: {', '.join(dead)}",
            )
        else:
            self.add(
                "8",
                "crates live",
                DERIVED_PASS,
                f"{checked}/{checked} crates resolve on crates.io at {self.bare_version}",
            )

    # -- verdict ------------------------------------------------------------

    def verdict(self) -> dict:
        by_step: dict[str, list] = {}
        for step, label, status, detail in self.findings:
            by_step.setdefault(step, []).append((label, status, detail))
        failures = sum(1 for _, _, s, _ in self.findings if s in FAILING)
        derived_slots = sum(
            1
            for step, _ in STEP_NAMES
            if any(s == DERIVED_PASS for _, s, _ in by_step.get(step, []))
            and not any(s in FAILING for _, s, _ in by_step.get(step, []))
        )
        attested = sum(1 for _, _, s, _ in self.findings if s == ATTESTED)
        vacuous = failures == 0 and derived_slots < MIN_DERIVED_SLOTS
        conforms = failures == 0 and not vacuous
        return {
            "version": self.version,
            "rid": self.rid,
            "mode": self.mode,
            "ref": self.ref,
            "sha": self.sha,
            "findings": [
                {"step": s, "label": l, "status": st, "detail": d}
                for s, l, st, d in self.findings
            ],
            "failures": failures,
            "derived_slots": derived_slots,
            "attested": attested,
            "vacuous": vacuous,
            "conforms": conforms,
        }

    def check_release_identity(self) -> None:
        """pretag mode must be aimed at the release the checkout is cutting —
        otherwise the gate could be pointed at a version name and pass on a
        tree that is not that release."""
        if self.mode != "pretag":
            return
        try:
            cargo = Path("Cargo.toml").read_text()
        except OSError:
            cargo = ""
        m = re.search(
            r"\[workspace\.package\].*?^version\s*=\s*\"([^\"]+)\"", cargo, re.S | re.M
        )
        ws = m.group(1) if m else None
        if ws == self.bare_version:
            self.add("0", "release identity", DERIVED_PASS, f"workspace version {ws} matches")
        else:
            self.add(
                "0",
                "release identity",
                DERIVED_FAIL,
                f"workspace version {ws!r} != requested {self.bare_version!r} — "
                "pretag mode must run on the checkout being cut",
            )

    def run_all(self) -> dict:
        self.check_release_identity()
        self.step_1_2()
        self.step_3()
        self.step_4()
        self.step_5()
        self.step_6()
        self.step_7()
        self.step_8()
        return self.verdict()


def render(v: dict) -> str:
    lines = [
        f"loop-conformance: release {v['version']} (rid {v['rid']}) "
        f"mode={v['mode']} ref={v['ref']} sha={v['sha'][:8]}"
    ]
    step_titles = dict(STEP_NAMES) | {"0": "release identity"}
    for f in v["findings"]:
        title = step_titles.get(f["step"], "?")
        lines.append(
            f"  step {f['step']:<3} {title:<18} {f['label']:<26} "
            f"{f['status']:<12} {f['detail']}"
        )
    if v["vacuous"]:
        lines.append(
            f"  VERDICT VACUOUS: only {v['derived_slots']} step-slots derived "
            f"(< {MIN_DERIVED_SLOTS}) — a verdict resting on attestations is refused"
        )
    lines.append(
        f"loop-conformance: {v['version']} slots=7 derived={v['derived_slots']} "
        f"attested={v['attested']} failures={v['failures']} "
        f"verdict={'CONFORMS' if v['conforms'] else 'DOES-NOT-CONFORM'}"
    )
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("version", help="release version, vX.Y.Z")
    ap.add_argument("--repo", default=REPO_DEFAULT)
    ap.add_argument("--json", help="write the machine-readable verdict here")
    args = ap.parse_args()

    chk = Check(args.version, args.repo)
    v = chk.run_all()
    print(render(v))
    if args.json:
        Path(args.json).write_text(json.dumps(v, indent=2) + "\n")
    return 0 if v["conforms"] else 1


if __name__ == "__main__":
    sys.exit(main())
