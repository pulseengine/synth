# RQ-62-LOOPCONFORM (#1136) — red-first evidence for the loop-conformance gate

The standing release authorization (2026-09-02) is conditional on the release
running the feature loop. `scripts/loop_conformance_check.py` derives that
conformance from artifacts that already exist — release trees, CI check-run
conclusions on the release commit, the tag's Signing E2E workflow run, the
crates.io index — instead of the cutter's say-so. This file holds the
red-first transcripts, both directions, run 2026-09-05 from commit `12a01a32`.

Reproduce any of them with:

```sh
python3 scripts/loop_conformance_check.py v0.61.0   # expect exit 0
python3 scripts/loop_conformance_check.py v0.57.0   # expect exit 1
python3 scripts/loop_conformance_check.py v0.56.2   # expect exit 1
```

(The retro runs query the GitHub check-runs / workflow-runs APIs and
crates.io; `scripts/test_loop_conformance_check.py` replays the same three
release shapes as offline fixtures so the red stays committed.)

## GREEN — v0.61.0 (exit 0)

```
loop-conformance: release v0.61.0 (rid v0.61) mode=retro ref=v0.61.0 sha=d4f935c1
  step 1-2 spar AADL->WIT     filed decision             NA-FILED     decided, artifact scoped, not yet built: RQ-62-ARCHMODEL (#1136, status proposed) in artifacts/release-v0.62/RQ-62-ARCHMODEL.yaml [programme-scoped, evaluated at checkout]
  step 3   rivet artifacts    artifact set               DERIVED-PASS 15 artifacts, 15/15 done-when
  step 3   rivet artifacts    status-evidence gate       DERIVED-PASS present and wired in ci.yml at ref
  step 3   rivet artifacts    Claim Check ran            DERIVED-PASS check-run success on d4f935c1
  step 4   oracle-gated       oracle wiring + floor      DERIVED-PASS wired with --min-emulation-floor 322754 at ref
  step 4   oracle-gated       wiring gate ran            DERIVED-PASS via Claim Check check-run on d4f935c1: success
  step 5   witness MC/DC      mcdc gate                  DERIVED-PASS present, wired, BRANCH_POPULATION-pinned at ref
  step 5   witness MC/DC      mcdc ran on commit         DERIVED-PASS check-run success on d4f935c1
  step 6   sigil signing      signing workflow           DERIVED-PASS present with v* tag trigger at ref
  step 6   sigil signing      Signing E2E ran            DERIVED-PASS success on d4f935c1 (runs: v0.61.0)
  step 7   clean-room review  cold-review record         ATTESTED     pre-0.62 release: review happened but left no machine-readable record; record regime starts v0.62 (#1091 decided the same boundary for done-when)
  step 8   release-exec       pin sweep                  DERIVED-PASS Version Pin Sweep check-run on d4f935c1: success
  step 8   release-exec       PR-head-vs-merge diff      ATTESTED     squash-merge head refs are not durably fetchable at audit time; run `git diff <PR head> <merged commit>` = 0 lines pre-tag and record the result in the step-7 review record
  step 8   release-exec       crates live                DERIVED-PASS 12/12 crates resolve on crates.io at 0.61.0
loop-conformance: v0.61.0 slots=7 derived=5 attested=2 failures=0 verdict=CONFORMS
```

## RED — v0.57.0 (exit 1), with a premise correction

The brief said v0.57.0 "predates the witness gate entirely". Measured, that is
WRONG: RQ-57-MCDC shipped **in** v0.57.0 and its check-run succeeded on the
tag commit (`91e6be66`, "MC/DC structural coverage ..." = success). What
v0.57.0 predates is the `BRANCH_POPULATION` pin (#1100, v0.61) and the
evidenced-status regime (`fields.done-when` + `status_evidence_check.py`,
RQ-60-FLIPCOUPLE, v0.60). The gate reds on exactly those, with attribution —
not on a vague "old release":

```
loop-conformance: release v0.57.0 (rid v0.57) mode=retro ref=v0.57.0 sha=91e6be66
  step 1-2 spar AADL->WIT     filed decision             NA-FILED     decided, artifact scoped, not yet built: RQ-62-ARCHMODEL (#1136, status proposed) in artifacts/release-v0.62/RQ-62-ARCHMODEL.yaml [programme-scoped, evaluated at checkout]
  step 3   rivet artifacts    done-when regime           DERIVED-FAIL 16/16 artifacts lack fields.done-when (evidenced-status regime, RQ-60-FLIPCOUPLE): RQ-561-ZEROMEM, RQ-57-SENTINEL, RQ-57-COUNTPARAMS, RQ-57-SKIPEXIT, RQ-57-BRTARGET...
  step 3   rivet artifacts    status-evidence gate       DERIVED-FAIL scripts/status_evidence_check.py absent or unwired at ref
  step 3   rivet artifacts    Claim Check ran            DERIVED-PASS check-run success on 91e6be66
  step 4   oracle-gated       oracle wiring + floor      DERIVED-PASS wired with --min-emulation-floor 295726 at ref
  step 4   oracle-gated       wiring gate ran            DERIVED-PASS via Claim Check check-run on 91e6be66: success
  step 5   witness MC/DC      mcdc gate                  DERIVED-FAIL gate present but carries no BRANCH_POPULATION pin at ref (#1100 — without the pin a deleted branch is invisible)
  step 5   witness MC/DC      mcdc ran on commit         DERIVED-PASS check-run success on 91e6be66
  step 6   sigil signing      signing workflow           DERIVED-PASS present with v* tag trigger at ref
  step 6   sigil signing      Signing E2E ran            DERIVED-PASS success on 91e6be66 (runs: main, v0.57.0)
  step 7   clean-room review  cold-review record         ATTESTED     pre-0.62 release: review happened but left no machine-readable record; record regime starts v0.62 (#1091 decided the same boundary for done-when)
  step 8   release-exec       pin sweep                  DERIVED-PASS Version Pin Sweep check-run on 91e6be66: success
  step 8   release-exec       PR-head-vs-merge diff      ATTESTED     squash-merge head refs are not durably fetchable at audit time; run `git diff <PR head> <merged commit>` = 0 lines pre-tag and record the result in the step-7 review record
  step 8   release-exec       crates live                DERIVED-PASS 12/12 crates resolve on crates.io at 0.57.0
loop-conformance: v0.57.0 slots=7 derived=3 attested=2 failures=3 verdict=DOES-NOT-CONFORM
```

## RED — v0.56.2 (exit 1), the release that DOES predate the witness gate

This is the corpus the artifact's `done-when` letter asks for
("a pre-witness-gate release"): no `scripts/mcdc_gate.py` in the tree, no
MC/DC check-run on the commit.

```
loop-conformance: release v0.56.2 (rid v0.56) mode=retro ref=v0.56.2 sha=dad414f4
  step 1-2 spar AADL->WIT     filed decision             NA-FILED     decided, artifact scoped, not yet built: RQ-62-ARCHMODEL (#1136, status proposed) in artifacts/release-v0.62/RQ-62-ARCHMODEL.yaml [programme-scoped, evaluated at checkout]
  step 3   rivet artifacts    done-when regime           DERIVED-FAIL 8/8 artifacts lack fields.done-when (evidenced-status regime, RQ-60-FLIPCOUPLE): RQ-56-CITE, RQ-56-PINS, RQ-56-COV, RQ-56-PLAN, RQ-56-CONF...
  step 3   rivet artifacts    status-evidence gate       DERIVED-FAIL scripts/status_evidence_check.py absent or unwired at ref
  step 3   rivet artifacts    Claim Check ran            DERIVED-PASS check-run success on dad414f4
  step 4   oracle-gated       oracle wiring + floor      DERIVED-PASS wired with --min-emulation-floor 295726 at ref
  step 4   oracle-gated       wiring gate ran            DERIVED-PASS via Claim Check check-run on dad414f4: success
  step 5   witness MC/DC      mcdc gate                  DERIVED-FAIL scripts/mcdc_gate.py absent or unwired at ref
  step 5   witness MC/DC      mcdc ran on commit         DERIVED-FAIL check-run on dad414f4: absent
  step 6   sigil signing      signing workflow           DERIVED-PASS present with v* tag trigger at ref
  step 6   sigil signing      Signing E2E ran            DERIVED-PASS success on dad414f4 (runs: v0.56.2)
  step 7   clean-room review  cold-review record         ATTESTED     pre-0.62 release: review happened but left no machine-readable record; record regime starts v0.62 (#1091 decided the same boundary for done-when)
  step 8   release-exec       pin sweep                  DERIVED-PASS Version Pin Sweep check-run on dad414f4: success
  step 8   release-exec       PR-head-vs-merge diff      ATTESTED     squash-merge head refs are not durably fetchable at audit time; run `git diff <PR head> <merged commit>` = 0 lines pre-tag and record the result in the step-7 review record
  step 8   release-exec       crates live                DERIVED-PASS 12/12 crates resolve on crates.io at 0.56.2
loop-conformance: v0.56.2 slots=7 derived=3 attested=2 failures=4 verdict=DOES-NOT-CONFORM
```

## PRETAG — v0.62.0 today (exit 1, correctly)

The mode the standing authorization actually consumes. Run before the v0.62
tag, it refuses today for exactly the right reasons: the checkout is not yet
the release being cut (workspace still 0.61.0), and no cold-review record
exists yet — the record regime this gate introduces.

```
loop-conformance: release v0.62.0 (rid v0.62) mode=pretag ref=HEAD sha=12a01a32
  step 0   release identity   release identity           DERIVED-FAIL workspace version '0.61.0' != requested '0.62.0' — pretag mode must run on the checkout being cut
  step 1-2 spar AADL->WIT     filed decision             NA-FILED     decided, artifact scoped, not yet built: RQ-62-ARCHMODEL (#1136, status proposed) in artifacts/release-v0.62/RQ-62-ARCHMODEL.yaml [programme-scoped, evaluated at checkout]
  step 3   rivet artifacts    artifact set               DERIVED-PASS 12 artifacts, 12/12 done-when
  step 3   rivet artifacts    status-evidence gate       DERIVED-PASS present and wired in ci.yml at ref
  step 3   rivet artifacts    status-evidence live run   DERIVED-PASS exit 0
  step 4   oracle-gated       oracle wiring + floor      DERIVED-PASS wired with --min-emulation-floor 322754 at ref
  step 4   oracle-gated       wiring gate live run       DERIVED-PASS exit 0
  step 5   witness MC/DC      mcdc gate                  DERIVED-PASS present, wired, BRANCH_POPULATION-pinned at ref
  step 5   witness MC/DC      mcdc ran on commit         DERIVED-PASS check-run success on 12a01a32
  step 6   sigil signing      signing workflow           DERIVED-PASS present with v* tag trigger at ref
  step 6   sigil signing      Signing E2E (pre-tag form) DERIVED-PASS latest completed main run success (2026-09-05T08:46:29Z); the tag's own run is created by the tag push this gate precedes
  step 7   clean-room review  cold-review record         DERIVED-FAIL no docs/reviews/ record for v0.62 at HEAD; write docs/reviews/v0.62-cold-review.md naming the reviewed commit and the findings (required from v0.62)
  step 8   release-exec       pin sweep live run         DERIVED-PASS exit 0
  step 8   release-exec       PR-head-vs-merge diff      ATTESTED     squash-merge head refs are not durably fetchable at audit time; run `git diff <PR head> <merged commit>` = 0 lines pre-tag and record the result in the step-7 review record
  step 8   release-exec       crates live                NA-BY-MOMENT publish happens after the tag; demanding it pre-tag would invent evidence — audited by retro mode
loop-conformance: v0.62.0 slots=7 derived=5 attested=1 failures=2 verdict=DOES-NOT-CONFORM
```

## What is DERIVED vs ATTESTED, stated once

- **Derived**: steps 3, 4, 5, 6, and step 8's pin sweep + crates-live — from
  the release ref's tree, check-run conclusions on the release commit, the
  tag's workflow runs, and the crates.io index. Step 7 becomes derived from
  v0.62 on via the `docs/reviews/<rid>-cold-review.md` record (presence,
  reviewed-sha ancestry — the reviewer's *independence* stays attested inside
  the record, and the gate's output says so).
- **N/A citing a filed decision**: steps 1-2 — `RQ-62-ARCHMODEL` (#1136,
  maintainer decision: not permanently N/A, timing first). Matched by shape
  (tags `feature-loop` + `aadl|spar`, non-empty `fields.issue`), not by a
  hardcoded id; an UNFILED N/A is red. Evaluated at the checkout because a
  filed decision is programme-scoped, covering every release's historical
  N/A from the moment it is decided.
- **Attested, with the reason recorded** (a negative result is a real
  result): PR-head-vs-merge diff = 0 (squash-merge head refs are not durably
  fetchable at audit time — record it in the review file); pre-v0.62 cold
  reviews (no record regime existed to leave a trace in).
- **Non-vacuity of the verdict itself**: `CONFORMS` requires zero failures
  AND >= 4 derived step-slots — a verdict resting on attestations alone is
  refused (unit-tested in `test_attestations_alone_are_vacuous_not_conforming`).
