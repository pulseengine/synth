#!/usr/bin/env python3
"""RQ-72-CIPOOL (#1062 increment 3): a CEILING on how much of CI queues against
the GitHub-hosted `ubuntu-latest` quota, and a DEADLOCK GUARD on the required
contexts.

WHY A STRUCTURAL PIN AND NOT A QUEUE-DEPTH CHECK
------------------------------------------------
The obvious gate samples the live queue and fails when it is deep. That gate
would be red during a merge burst and green ten minutes later on an UNCHANGED
repository — a verdict that depends on when it ran. Measured at the v0.72 cut,
three samples 50 s apart on run 35888386080 all read `queued={}`; the v0.71
readings of the same pool read 55 and 57 queued. BOTH are real. The pool is not
saturated, it is BURST-SENSITIVE, and the thing that makes bursts hurt is
structural: what share of the job definitions point at one quota.

So this pins the SHARE OF JOB DEFINITIONS, which is a fact about `ci.yml`:
identical for every observer, stable between runs, and the actual cause.
(#1062's own history records the same correction — "sampled rather than read
off one instant" — after an earlier 7/7 point reading turned out to be a
merge-wave transient.)

MATCH THE LABEL EXACTLY, NEVER BY SUBSTRING
-------------------------------------------
A first pass at this counted `ubuntu` as a substring and reported 56/68. That
swept in `ubuntu-24.04-arm`, which is a DIFFERENT hosted pool with its own
queue, and inflated the number this lane exists to reduce — in the flattering
direction. The honest figure is 55/68. Exact-label matching is not a style
preference here; it is the difference between a true and a false number.

THE DEADLOCK GUARD
------------------
Retargeting a REQUIRED context is the one unsafe move: a required NAME that
never runs blocks every merge with no red to revert. So this also asserts that
every required context is still DEFINED and still has a `runs-on` — catching a
rename or a deletion before it can deadlock the branch, rather than after.

(v0.90, RQ-90-SPECEXEC #1636) A required context is RESOLVED ACROSS EVERY
workflow file under `.github/workflows/`, not only `ci.yml` — branch protection
names check-run contexts, and a job in `spec-suite.yml` reports one exactly as a
`ci.yml` job does. The POOL-SHARE count and its ceiling still read `ci.yml`
ONLY, deliberately: widening the count's population would move the ceiling
silently. See `resolve_required_contexts` for what resolves and what does not.
"""
import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
CI = ROOT / ".github" / "workflows" / "ci.yml"
WORKFLOWS = ROOT / ".github" / "workflows"

# The ceiling. It is a CEILING and not an equality: a PR may add an
# `ubuntu-latest` job when it also moves others off, and a ratchet that
# punishes net progress is a ratchet people route around. Lower it in the same
# PR that earns the lower number — never raise it without a written reason
# here, which is the #911 rule applied to pool share.
#
#   v0.72 (RQ-72-CIPOOL): 55 -> 52. Measured on ff7a8dd1, then EARNED in
#   this same PR by moving three PURE-cargo, NON-required jobs to
#   [self-hosted, linux, x64, rust-cpu]: vcr-ra-003-alloc-validator-gate,
#   vcr-ra-003-rv32-alloc-validator-gate and
#   vcr-sel-005-cross-backend-op-parity-gate. Each uses only
#   checkout + rust-toolchain + cache, which is the shape `Clippy` (a
#   REQUIRED context) has run on this pool with since increment 2. The programme's earlier
#   readings were 56/65 (86.2%, #1062 increment 2) and 55/68 (81%) here — the
#   share is falling because v0.71's musl job and v0.72's litpool-islands job
#   were placed on the self-hosted pool rather than defaulting.
# RQ-73-CIPOOL (#1062 increment 4): 52 -> 46. Six oracle jobs moved to
# self-hosted now that every `pip install` in this file carries the PEP 668
# fallback — measured before the guard, 37 of the 40 candidates were blocked on
# exactly that, so the guard is what made the move possible rather than an
# incidental tidy-up. 34 remain PEP668_POOL_READY and are a one-line retarget
# each; they are left for a measured follow-up rather than moved in one burst,
# because a pool change that goes wrong takes every lane's CI with it.
# v0.88 (#1564): 46 -> 44. aarch64-oracle and repro-sweep-memory-oracle were
# pinned to ubuntu-24.04 because the ubuntu-26.04 image ubuntu-latest began
# rolling to on 2026-10-21 changed their apt toolchain underneath them.
# v0.90 (RQ-90-SPECEXEC, #1636): the population of this count is UNCHANGED —
# ci.yml's job definitions only — even though required contexts now resolve
# across every workflow. Counting the other workflows' jobs too would move the
# number with no job having moved, which is the silent drift this ceiling
# exists to make visible. Widen it only with a re-derived ceiling and a reason.
UBUNTU_LATEST_CEILING = 44

EXACT_LABEL = "ubuntu-latest"


# RQ-73-CIPOOL (#1062 increment 4): WHICH ubuntu-latest jobs can move, derived
# rather than asserted.
#
# v0.72 held four required contexts back on a HEURISTIC ("they carry an
# external-toolchain marker"). The real reason is STRUCTURAL and was measured
# during that release:
#
#   sudo: The "no new privileges" flag is set, which prevents sudo from
#         running as root.
#
# `no_new_privs` on the self-hosted containers means NO job needing `apt-get`
# can ever run there, however the plan evolves — not a scheduling preference
# and not something a later increment can work around. pip is different: it
# needs no sudo, and works under the PEP 668 `--break-system-packages` fallback
# v0.72 proved.
#
# So a job is PEP668_POOL_READY when it is on ubuntu-latest, is NOT a required
# context, needs NO apt/sudo, and every `pip install` it runs already carries
# the PEP 668 fallback. That last clause is the one that makes this a
# precondition rather than a wish: measured at this release, all 40 candidate
# jobs lacked the fallback, so a bare `runs-on` retarget would have broken
# every one of them on the first self-hosted run.
# (v0.74, RQ-74-APTBLIND #1062) `apt-get` is not the only spelling. v0.73's
# round-2 gate review moved a REQUIRED context to the self-hosted pool with its
# install step written as `apt update` / `apt install -y` — no `-get`, no
# `sudo` — and this guard returned rc=0, "0 failure(s)", on the exact deadlock
# it exists to prevent. `apt` alone is now matched.
APT_RE = re.compile(r"\bapt(-get)?\b|\bsudo\b")
# A `run:` body that invokes a repo script hides everything that script does.
# Round 2's other walk-around moved the apt lines into
# `run: bash scripts/install-llvm-dwarfdump.sh` and the guard went quiet. Not
# hypothetical: scripts/install-qemu.sh already contains apt-get today (no
# required context invokes it, which is why this is a latent hole and not a live
# deadlock). Followed ONE level, for REQUIRED self-hosted contexts only — the
# only population where the deadlock exists — because a repo-wide "any job that
# mentions an installer" rule is the nuisance that gets a guard routed around.
# NOTE the lookbehind, and why it is not `(?:^|[\\s;&|])`: the job body this
# ran against was `str(job)`, a dict REPR (v0.75 replaced it with `job_text(j)`,
# which is why the position blindness below is closed; this paragraph describes
# the OLD input and is kept because the walk-arounds it lists still hold). In a
# repr the command appears as
# {'run': 'bash scripts/install-qemu.sh'} — preceded by a QUOTE, not by
# whitespace. The first version of this regex required whitespace and
# silently matched nothing; the potency test below is what caught it.
SCRIPT_RE = re.compile(r"(?<![\w/-])(?:bash|sh|source|\.)\s+(scripts/[\w./-]+)")
# WHAT THIS PAIR STILL MISSES (v0.74 cold review round 1, ENUMERATED so the
# boundary is a list rather than a feeling). Each was applied with the required
# context moved to self-hosted AND the ratchet ceiling lowered, so nothing could
# supply a red for the wrong reason; all returned "0 failure(s)":
#   `aptitude install`      — `\bapt\b` does not match `aptitude`
#   `dpkg -i`               — a different installer entirely
#   two script levels       — A invokes B, apt lives in B
#   `./scripts/x.sh`        — no `bash `/`sh ` prefix
#   `bash .github/x.sh`     — outside `scripts/`
#   `python3 scripts/x.py`  — SCRIPT_RE follows only bash/sh/source/.
#   `make -f scripts/x.mk`  — same
#   a `bash <<'EOS'` heredoc
#   `uses: some/install-action` — the `uses:` surface is unguarded; one such
#       mutation WAS caught, but only because that action's NAME contains "apt"
# Widening this piecemeal is whack-a-mole: the real check is whether the job's
# install step can run under `no_new_privs`, which needs executing it, not
# grepping it. Recorded as a v0.76 candidate.
#
# WHAT IS LATENT HERE, stated precisely because the loose version was FALSE and
# this very file refuted it 240 lines down. FIVE required contexts DO run
# self-hosted today — Clippy, Format, Version Pin Sweep, Claim Check and Rivet
# Validation — so "no required context is on the self-hosted pool" is wrong. What
# is empty is the INTERSECTION this guard exists for: a required context that is
# self-hosted AND needs apt. Re-derive with `python3 scripts/ci_pool_tripwire.py`,
# which prints the pools, rather than trusting this sentence.
PIP_RE = re.compile(r"\bpip install\b")
PEP668_RE = re.compile(r"--break-system-packages")


def job_text(job) -> str:
    """Every string a job carries, joined by REAL newlines.

    RQ-75-APTSHAPE (#1062), v0.75 — THE ROOT CAUSE, not another spelling.
    Both scans below used to read `str(job)`, a dict REPR. In a repr a newline
    renders as the two characters backslash and `n`, so a `run:` block like

        run: |
          set -euo pipefail
          apt-get install -y x

    became `...pipefail\\napt-get install...` — and `\\bapt` CANNOT match there,
    because the `n` of the escaped newline sits directly before `apt` and both
    are word characters. So the detector only ever saw an installer that was the
    FIRST TOKEN of its `run:` value. Swapping two lines flipped CAUGHT to
    MISSED, measured in v0.74's round 2 and re-measured at this lane's cut.

    Widening the alternation would not have touched this: the pattern was
    already correct and was being handed text that could not match it. That is
    why v0.74's nine enumerated spellings are NOT the thing this lane fixes —
    the detector was blind to a position, not to a word.

    STILL A LIST, disclosed rather than implied: `aptitude`, `dpkg -i`, a second
    script level, `./scripts/x.sh`, `.github/x.sh`, a python or make wrapper and
    the `uses:` surface remain unmatched, and no amount of pattern widening
    settles it. The real check is whether the job's install step can RUN under
    `no_new_privs`, which needs executing it. That is a v0.76 candidate and is
    NOT claimed here.
    """
    out = []

    def walk(v):
        if isinstance(v, str):
            out.append(v)
        elif isinstance(v, dict):
            for k, x in v.items():
                out.append(str(k))
                walk(x)
        elif isinstance(v, (list, tuple)):
            for x in v:
                walk(x)
        elif v is not None:
            out.append(str(v))

    walk(job)
    return "\n".join(out)


def pep668_pool_ready(jobs, required):
    """(ready, blocked) — blocked maps job name -> why it cannot move."""
    ready, blocked = [], {}
    for jid, j in jobs.items():
        if pool_of(j.get("runs-on")) != EXACT_LABEL:
            continue
        name = j.get("name") or jid
        body = job_text(j)
        if name in required:
            blocked[name] = "required context (moving one DEADLOCKS every merge)"
        elif APT_RE.search(body):
            blocked[name] = "needs apt/sudo — impossible under no_new_privs"
        elif PIP_RE.search(body) and not PEP668_RE.search(body):
            blocked[name] = "pip install without the PEP 668 fallback"
        else:
            ready.append(name)
    return ready, blocked


def pool_of(runs_on):
    """The pool a `runs-on:` names. Self-hosted is a LABEL SET, everything else
    is a single string; neither is matched by substring."""
    if isinstance(runs_on, list):
        return "self-hosted" if "self-hosted" in runs_on else ",".join(runs_on)
    return str(runs_on)


def load_jobs():
    doc = yaml.safe_load(CI.read_text())
    return doc["jobs"]


def load_workflows():
    """{relative path: parsed document} for every workflow file, sorted."""
    out = {}
    for p in sorted(list(WORKFLOWS.glob("*.yml")) + list(WORKFLOWS.glob("*.yaml"))):
        out[str(p.relative_to(ROOT))] = yaml.safe_load(p.read_text()) or {}
    return out


CI_REL = ".github/workflows/ci.yml"


def _triggers(doc):
    # PyYAML (YAML 1.1) parses the bare key `on` as the boolean True. Reading
    # only "on" would see NO triggers on every workflow and the trigger check
    # below would be blind; reading only True would break on a quoted "on".
    on = doc.get("on", doc.get(True))
    if isinstance(on, str):
        return {on: None}
    if isinstance(on, list):
        return {k: None for k in on}
    return on if isinstance(on, dict) else {}


def trigger_problem(doc):
    """Why this workflow may NEVER report on a pull request, or None.

    A required context that does not run on a PR is a NAME that never reports:
    the deadlock, reached through the workflow's `on:` rather than the job."""
    trig = _triggers(doc)
    if "pull_request" not in trig:
        return (f"its workflow does not trigger on `pull_request` "
                f"(triggers: {sorted(map(str, trig))})")
    pr = trig.get("pull_request") or {}
    if isinstance(pr, dict):
        for k in ("paths", "paths-ignore"):
            if k in pr:
                return (f"its workflow's `pull_request` trigger carries a `{k}:` "
                        f"filter, so a PR outside it never reports the context")
    return None


def job_contexts(path, jobs):
    """The check-run contexts a workflow's jobs report, as {context: job}.

    A job reports its `name:`, or its job id when it has no name. What does NOT
    resolve, on purpose — each would make a required context look defined when
    the context GitHub actually reports is a different string:
      * a `name:` containing `${{` — the reported name is the EXPANSION;
      * a job with `strategy.matrix` — GitHub appends the matrix values, so even
        a literal name reports as `name (a, b)`;
      * a job-level `uses:` (a reusable-workflow call) — it reports as
        `caller / callee`.
    ci.yml ALONE also keeps its historical job-id alias (`by_name.setdefault`),
    so ci.yml's resolution is byte-identical to the pre-v0.90 guard. It is NOT
    extended to other workflows: there a required context spelled `publish` or
    `fuzz` would resolve to a job that reports a different name."""
    out = {}
    for key, j in (jobs or {}).items():
        if not isinstance(j, dict):
            continue
        name = j.get("name", key)
        if path == CI_REL:
            out[name] = j
            out.setdefault(key, j)
            continue
        if "${{" in str(name):
            continue
        if isinstance(j.get("strategy"), dict) and "matrix" in j["strategy"]:
            continue
        if "uses" in j:
            continue
        out[str(name)] = j
    return out


def resolve_required_contexts(contexts, workflows):
    """({context: (path, job)}, [failure]) for the pinned required contexts.

    TWO WORKFLOWS DEFINING ONE REQUIRED CONTEXT is a failure (AMBIGUOUS): GitHub
    would carry two check runs with the same name, and which one satisfies the
    branch rule is not something this repository controls — a green one can
    stand in for a red one. A context defined in NO workflow is the DEADLOCK it
    always was. (Duplicates INSIDE ci.yml keep their pre-v0.90 behaviour, the
    later definition wins, so the ci.yml path is unchanged.)"""
    defs = {}
    for path, doc in workflows.items():
        for ctx, j in job_contexts(path, (doc or {}).get("jobs")).items():
            defs.setdefault(ctx, []).append((path, j, doc))
    resolved, failures = {}, []
    for c in contexts:
        hits = defs.get(c, [])
        if not hits:
            failures.append(
                f"DEADLOCK: required context `{c}` is not defined in any "
                f"workflow under .github/workflows/. "
                f"A required NAME that never runs blocks every merge, with no "
                f"red to revert — this is the one unsafe move in this lane. "
                f"If the context was deliberately renamed or retired, update "
                f"REQUIRED_CONTEXTS and the branch protection TOGETHER.")
            continue
        if len(hits) > 1:
            failures.append(
                f"AMBIGUOUS: required context `{c}` is defined by "
                f"{len(hits)} jobs ({', '.join(h[0] for h in hits)}). Two check "
                f"runs with one name let a green one stand in for a red one. "
                f"Rename all but one.")
            continue
        path, j, doc = hits[0]
        why = trigger_problem(doc)
        if why is not None:
            failures.append(
                f"DEADLOCK: required context `{c}` ({path}) may never report: "
                f"{why}.")
            continue
        resolved[c] = (path, j)
    return resolved, failures


# The required contexts, PINNED. Read from
# `repos/<repo>/branches/main/protection/required_status_checks/contexts`
# on 2026-09-23 and committed here on purpose:
#
#   1. The deadlock guard must run WITHOUT the network. The first version
#      called `gh` and skipped when it was unavailable — and no other job in
#      this workflow calls `gh`, so on the runner it skipped (or crashed)
#      every time. A guard that never executes is the "gate nobody asks"
#      defect RQ-72-ISSUEGATE is about, reproduced by the lane meant to fix
#      the pool.
#   2. A committed list is a CONTRACT. If branch protection changes, the
#      cross-check below says so instead of silently adopting the new set —
#      a required context appearing or vanishing is exactly the event worth
#      a visible diff.
REQUIRED_CONTEXTS = [
    "Format",
    "Clippy",
    "Test",
    "Z3 Verification",
    "Claim Check",
    "Version Pin Sweep",
    "Bazel Build & Proofs",
    "Kani Verification",
    "Rivet Validation",
]

# v0.90 (RQ-90-SPECEXEC, #1636): contexts ABOUT TO BE required — the maintainer
# has decided to add them to branch protection, and protection does not carry
# them yet. Kept apart from REQUIRED_CONTEXTS on purpose, because that list is
# also the merge gate's CONTRACT (`merge_gate.py` imports it, CHECK1 compares it
# with the live API by name): pinning a context protection does not have yet
# would make CHECK1 refuse EVERY PR until protection caught up.
#
# What a pending context gets, and what it does not:
#   * the DEADLOCK guard below resolves it exactly like a required one — a
#     pending context defined in no workflow, gated off by `if:`, or in a
#     workflow that does not run on `pull_request` FAILS. Adding a context
#     to protection is only safe once that holds, which is why it is checked
#     BEFORE the flip.
#   * the merge gate tolerates protection carrying it or not (CHECK1:
#     REQUIRED <= api <= REQUIRED | PENDING), and once protection carries it,
#     CHECK1's `missing` demands it SUCCESS like any required context.
#   * the drift cross-check FAILS (PROMOTE) once protection carries it, so the
#     window ends in a one-line diff moving it into REQUIRED_CONTEXTS rather
#     than lasting forever.
# The two lists must be disjoint; the cross-check below fails if not.
PENDING_REQUIRED_CONTEXTS = [
    # defined in spec-suite.yml, not ci.yml — the reason the guard now
    # resolves required contexts across every workflow file.
    "spec-suite execution (#1636)",
]


def live_required_contexts(repo):
    """The API's view, or None when it cannot be read.

    `gh` may be absent from a runner entirely, in which case `subprocess.run`
    RAISES rather than returning non-zero — the first version of this function
    did not catch that and turned a missing tool into a failed required
    context."""
    try:
        out = subprocess.run(
            ["gh", "api",
             f"repos/{repo}/branches/main/protection/required_status_checks/contexts",
             "--jq", ".[]"],
            capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return [l.strip() for l in out.stdout.splitlines() if l.strip()]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default="pulseengine/synth")
    ap.add_argument("--offline", action="store_true",
                    help="skip the required-context deadlock guard (no network)")
    args = ap.parse_args()

    jobs = load_jobs()
    counts = Counter(pool_of(j.get("runs-on")) for j in jobs.values())
    total = sum(counts.values())
    ubl = counts.get(EXACT_LABEL, 0)

    print(f"ci-pool: {total} job definitions in ci.yml")
    for pool, n in counts.most_common():
        print(f"ci-pool:   {n:3d}  {pool}")
    pct = (100.0 * ubl / total) if total else 0.0
    print(f"ci-pool: {EXACT_LABEL} share = {ubl}/{total} = {pct:.0f}% "
          f"(ceiling {UBUNTU_LATEST_CEILING})")

    failures = []
    if ubl > UBUNTU_LATEST_CEILING:
        failures.append(
            f"CEILING: {ubl} job definitions target `{EXACT_LABEL}`, above the "
            f"pinned ceiling of {UBUNTU_LATEST_CEILING}. A new job defaulting to "
            f"the GitHub-hosted quota makes every other lane queue longer during "
            f"a merge burst. Put it on `[self-hosted, linux, x64, rust-cpu]` or "
            f"`light`, or lower something else in this PR and move the ceiling "
            f"with a written reason.")
    if ubl < UBUNTU_LATEST_CEILING:
        # A ratchet that lets a win be silently given back is not a ratchet.
        failures.append(
            f"RATCHET: {ubl} is BELOW the pinned ceiling {UBUNTU_LATEST_CEILING} "
            f"— lower `UBUNTU_LATEST_CEILING` to {ubl} in this PR so the win "
            f"cannot be given back without a visible diff (the claims.yaml "
            f"baseline rule, applied here).")

    # ---- the deadlock guard: ALWAYS runs, from the pinned contract ---------
    # GUARDED = the required contexts AND the pending ones: a context about to
    # be required must already pass every check a required one does.
    overlap = sorted(set(REQUIRED_CONTEXTS) & set(PENDING_REQUIRED_CONTEXTS))
    if overlap:
        failures.append(
            f"CONTRACT: {overlap} is in BOTH REQUIRED_CONTEXTS and "
            f"PENDING_REQUIRED_CONTEXTS. A context is required or pending, "
            f"never both — remove it from PENDING when promoting it.")
    guarded = list(REQUIRED_CONTEXTS) + [
        c for c in PENDING_REQUIRED_CONTEXTS if c not in REQUIRED_CONTEXTS]
    resolved, res_failures = resolve_required_contexts(
        guarded, load_workflows())
    failures.extend(res_failures)
    on_hosted = 0
    for c in guarded:
        if c not in resolved:
            continue
        path, j = resolved[c]
        kind = "pending" if c in PENDING_REQUIRED_CONTEXTS else "required"
        if path != CI_REL:
            print(f"ci-pool: {kind} context {c!r} resolves in {path}")
        if not j.get("runs-on"):
            failures.append(f"DEADLOCK: required context `{c}` has no `runs-on:`.")
            continue
        # (v0.72 cold review, F3) A rename was caught; GATING THE JOB OFF was
        # not — and a required context that never REPORTS is the same deadlock
        # as one that does not exist, reached by a one-line `if:` instead of a
        # rename. Demonstrated: adding
        # `if: github.event_name == 'schedule'` to `Kani Verification` left
        # this guard at rc=0 with 0 failures. No required job carries an `if:`
        # today, so this is a latent class closed before it fires.
        if j.get("if") is not None:
            failures.append(
                f"DEADLOCK: required context `{c}` carries an `if:` "
                f"({j['if']!r}). A required NAME that is conditionally skipped "
                f"never reports, and a never-reporting required context blocks "
                f"every merge with no red to revert. Remove the condition, or "
                f"retire the context from branch protection FIRST.")
            continue
        if pool_of(j.get("runs-on")) == EXACT_LABEL and kind == "required":
            on_hosted += 1
    print(f"ci-pool: {len(REQUIRED_CONTEXTS)} required contexts (pinned), "
          f"{on_hosted} on {EXACT_LABEL}, "
          f"{len(REQUIRED_CONTEXTS) - on_hosted} elsewhere")
    if PENDING_REQUIRED_CONTEXTS:
        print(f"ci-pool: {len(PENDING_REQUIRED_CONTEXTS)} pending context(s) "
              f"guarded as if required: {PENDING_REQUIRED_CONTEXTS}")

    # RQ-73-CIPOOL (#1062 increment 4): the migration-ready set, DERIVED.
    ready, blocked = pep668_pool_ready(jobs, set(guarded))
    n_req = sum(1 for v in blocked.values() if v.startswith("required"))
    n_apt = sum(1 for v in blocked.values() if "apt/sudo" in v)
    n_pip = sum(1 for v in blocked.values() if "PEP 668" in v)
    print(f"ci-pool: PEP668_POOL_READY = {len(ready)} job(s) may move; "
          f"blocked {n_req} required, {n_apt} apt/sudo, {n_pip} unguarded pip")
    # A required context must NEVER be reported movable: retargeting one leaves
    # a NAME that never runs, which blocks every merge with no red to revert.
    for name in ready:
        if name in set(guarded):
            failures.append(
                f"ci-pool: {name!r} is a REQUIRED context and was reported "
                f"PEP668_POOL_READY. Moving it deadlocks every merge.")

    # (v0.73 cold review, gate finding F8) POOL SUITABILITY, which the deadlock
    # guard never checked. Its scope is "defined / has `runs-on` / no `if:`" —
    # all properties of the job's DECLARATION, none of the pool it declares.
    # DEMONSTRATED by the reviewer: moving a required context to self-hosted
    # produced ZERO deadlock failures; it red only on the RATCHET, and lowering
    # the ceiling exactly as the ratchet instructs gave "0 failure(s)".
    #
    # The hazard is specific and derivable: `no_new_privs` on the self-hosted
    # containers makes `apt-get` impossible there, so a required context that
    # needs apt would never run — a NAME permanently pending, which is the
    # deadlock with no red to revert.
    #
    # NOTE what this does NOT claim, because the artifact overstated it and the
    # refuting command caught that: of the four required contexts on
    # ubuntu-latest, only TWO need apt (`Test`, `Z3 Verification`). `Kani
    # Verification` and `Bazel Build & Proofs` do not, and five required
    # contexts already run self-hosted today. "Required contexts can never move"
    # is false as a general statement; "a required context that needs apt can
    # never run self-hosted" is the true one, and is what this checks.
    # v0.90: walks the RESOLVED required jobs, so a required context defined
    # outside ci.yml is checked too (it used to walk ci.yml's jobs only).
    for name, (_path, j) in resolved.items():
        if pool_of(j.get("runs-on")) != "self-hosted":
            continue
        body = job_text(j)
        via = ""
        if not APT_RE.search(body):
            # Follow a repo script the job invokes (one level). See SCRIPT_RE.
            for rel in SCRIPT_RE.findall(body):
                p = ROOT / rel
                if p.is_file() and APT_RE.search(p.read_text(errors="ignore")):
                    via = f" (via {rel}, which the job invokes)"
                    break
        if APT_RE.search(body) or via:
            failures.append(
                f"ci-pool: REQUIRED context {name!r} is on the self-hosted pool "
                f"AND needs apt/sudo{via}. `no_new_privs` makes that impossible, "
                f"so the context would never conclude — every merge blocks on a "
                f"name that never runs, with no red to revert.")

    # ---- and the API as a CROSS-CHECK, never as the source -----------------
    if not args.offline:
        live = live_required_contexts(args.repo)
        if live is None:
            print("ci-pool: live required-context list UNAVAILABLE (no gh, no "
                  "network, or no token) — the pinned contract above still ran; "
                  "only the drift cross-check is skipped")
        else:
            live_s, req_s = set(live), set(REQUIRED_CONTEXTS)
            pend_s = set(PENDING_REQUIRED_CONTEXTS)
            promoted = sorted(live_s & pend_s)
            if not (req_s <= live_s <= req_s | pend_s):
                failures.append(
                    f"CONTRACT DRIFT: branch protection requires {sorted(live)} but "
                    f"REQUIRED_CONTEXTS pins {sorted(REQUIRED_CONTEXTS)} (pending "
                    f"{sorted(pend_s)}). A context "
                    f"appearing or vanishing is worth a visible diff, not a silent "
                    f"adoption — reconcile them in one PR.")
            elif promoted:
                failures.append(
                    f"PROMOTE: branch protection now requires pending context(s) "
                    f"{promoted}. Move them from PENDING_REQUIRED_CONTEXTS into "
                    f"REQUIRED_CONTEXTS in one PR, so the merge gate's contract "
                    f"equals protection again (merge_gate CHECK1 accepts both "
                    f"states, so that PR can merge).")
            else:
                print("ci-pool: pinned required contexts match branch protection")
                for c in sorted(pend_s):
                    print(f"ci-pool: pending context {c!r} is not yet in branch "
                          f"protection")

    for f in failures:
        print(f"FAIL {f}")
    print(f"ci-pool: {len(failures)} failure(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
