# RQ-65-FLOORSHAPE (#1183) — the population floors, anchored at the release tag

`scripts/status_evidence_check.py` guards its own scan population with two
non-vacuity floors. Until v0.65 both were hand-pinned lower bounds that only
ever lagged:

```
DELIVERY_FLOOR   pinned 28   live 67   (58 % slack)
PROGRAMME_FLOOR  pinned 379  live 408  ( 7 % slack)
```

This note records what was measured before choosing a shape, the shape, and
the red-first transcripts — both directions, on the real repository — run
2026-09-09 from `af819788` (origin/main) plus the lane's change.

Reproduce:

```sh
python3 scripts/floorshape_1183_churn.py          # the churn series (~3 min, full history)
python3 scripts/status_evidence_check.py           # prints `status-evidence-anchor: ...`
python3 scripts/test_status_evidence_check.py      # AnchorRule1183 + ProgrammeVisibility1183
```

The churn script lives in `scripts/`, not `scripts/repro/`: it is a
measurement over git history, not an execution oracle over compiled output,
and `scripts/repro/`'s `manual` census is a ceiling whose own text says an
eighth entry needs a conversation, not a commit. Nothing about the anchor
depends on the script — the checker re-derives the anchor from git on every
run; the script only justifies the shape.

## 1. A premise correction, first

The issue's canonical case — "a shallow checkout fetching 30 commits would
pass" — is wrong about the OLD gate. Measured on main: only **4 of the last 30**
first-parent commits are id-first delivery commits, so `--depth=30` scores 4
and the floor of 28 already reddened it. The 28th hit is first reached at
first-parent depth **79**, and the 67th at depth 204: any `--depth` in
**79..203** passed the old gate while losing up to 39 of 67 delivery commits
— every one from v0.56 through v0.61. The transcripts below therefore run at
depth 79 (old green, new red) as well as at 30 (both red), because a
demonstration at a depth the old gate already caught proves nothing about the
new shape.

## 2. The churn, measured with the checker's own instruments

`delivery` = id-first first-parent delivery commits reachable from the ref
whose id is a release artifact in the tree at that ref (`ARTIFACT_ID` +
`RELEASE_GLOB` as shipped); `programme` = artifacts `check_programme`
status-checks over the tree at that ref. Moves = first-parent commits inside
the interval at which the count changed (the programme series evaluated at
every one of the 129 commits touching `artifacts/` since v0.56.0):

```
ref       fp-commits  delivery  programme
v0.56.0          865         2        275
v0.56.1          868         2        287
v0.56.2          874         3        289
v0.57.0          887         3        290
v0.58.0          911        10        301
v0.59.0          954        26        322
v0.60.0          972        37        331
v0.61.0          998        53        367
v0.62.0         1019        61        385
v0.63.0         1031        64        391
v0.64.0         1048        67        401
HEAD            1055        67        408

interval             fp-commits  delivery  programme  dips
v0.56.0..v0.56.1              3         0          2     0
v0.56.1..v0.56.2              6         1          1     0
v0.56.2..v0.57.0             13         0          1     0
v0.57.0..v0.58.0             24         7          2     0
v0.58.0..v0.59.0             43        16          3     0
v0.59.0..v0.60.0             18        11          2     0
v0.60.0..v0.61.0             26        16          7     0
v0.61.0..v0.62.0             21         8          7     0
v0.62.0..v0.63.0             12         3          3     0
v0.63.0..v0.64.0             17         3          2     0
v0.64.0..HEAD                 7         0          1     0
```

**65 delivery moves and 31 programme moves in 11 release intervals**, never a
decrease. RQ-64-SCOPEGAP measured `STALENESS_CITATIONS` at 2 moves in 7
intervals and chose equality; an equality at HEAD here would cost roughly 6
delivery bumps and 3 programme bumps per release, each a `claims.yaml` diff
on the most merge-contended file (RQ-64-FLOORPROSE's measurement of where
v0.63's largest merge cost sat). That is the churn people route around.

## 3. The shape, per count

Pin what is **constant between releases** as an equality, re-derived from git
on every run:

| rule | statement | sees |
|---|---|---|
| A1 | id-first delivery commits reachable from `ANCHOR_TAG` `==` `ANCHOR_DELIVERY`; a repo declaring itself shallow is red outright | truncated history, id-regex / release-glob rot |
| A2 | artifacts the P-scan finds in `git archive ANCHOR_TAG artifacts` `==` `ANCHOR_PROGRAMME`, same glob/loader/filter as the live scan | programme-glob / loader rot on an unchanged tree |
| A3 | live counts `>=` anchor (`DELIVERY_FLOOR`, `PROGRAMME_FLOOR` are now *derived* from the anchor) | loss at HEAD; slack bounded to one release's growth |
| A0 | `ANCHOR_TAG` is the release window's previous minor tag; lag 1 warns with the three lines to paste, lag 2 is red | a forgotten move |
| P3 | every yaml under `artifacts/`, any depth, is one `PROGRAMME_GLOB` scans | one file invisible (a SUM floor cannot see this) |
| P4 | every scanned yaml contributes `>= 1` artifact (`_release.yaml` excepted) | the #1064 skipped-file shape on topic files |

Main history is immutable and shipped release artifacts are frozen, so the
two anchored counts cannot change until the tag does — the move is once per
release, and A0 forces it. The programme count differs from the delivery
count in one respect: it is tree-derived, so a shallow checkout cannot touch
it, and its loss class is a single file going invisible — hence P3/P4
(measured 89/89 visible, only the five comments-only `_release.yaml` empty).

Rejected on the measurement: `direction: track` *is* the equality at HEAD
(section 2); a relative floor derived with the same instrument cannot see
that instrument rot, because a rotted regex lowers both sides. The
`PROGRAMME_DELETED_SINCE_ANCHOR` waiver channel exists because A3-programme
is a floor over a tree that could legitimately lose an artifact; it is 0,
has never been needed (0 dips in 129 commits), and a declaration the live
count does not need is a dead waiver and red.

## 4. Red-first on the real repository

`old` = `scripts/status_evidence_check.py` as on origin/main; `new` = the
lane's. Each run with `--root` against a `git clone [--depth N]` of the same
tree (the CI failure shape, not a hand-truncated subjects list).

### `--depth=30` — 30 first-parent commits, shallow=true (both red)

```
--- OLD: EXIT=1
    FAIL VACUOUS: only 4 delivery commits matched (floor 28) — shallow checkout or scan rot; the floor never comes down to pass
    status-evidence: 114 artifacts across 59 release files, 4 delivery commits matched, ... 1 failures
--- NEW: EXIT=1
    FAIL VACUOUS: only 4 delivery commits matched (floor 67) — ...
    FAIL A1 anchor v0.64.0: history is SHALLOW — `git rev-parse --is-shallow-repository` says the ancestry is truncated ...
    FAIL A1 anchor v0.64.0: 4 id-first delivery commits reachable from the tag != pinned ANCHOR_DELIVERY 67 (BELOW by 63) — ...
    FAIL A0 anchor v0.64.0: the release window's previous tag is underivable (None), ...
    FAIL A3: live delivery scan 4 < anchor 67 — ...
    status-evidence-anchor: v0.64.0 — 4 delivery commits (pinned 67), 401 artifacts (pinned 401), lag UNDERIVABLE
```

### `--depth=79` — 79 first-parent commits, shallow=true (OLD GREEN, new red)

```
--- OLD: EXIT=0
    status-evidence: 114 artifacts across 59 release files, 28 delivery commits matched, 62 done-when predicates evaluated, 0 release-scope archaeology checks (17 skipped), 0 failures
--- NEW: EXIT=1
    FAIL VACUOUS: only 28 delivery commits matched (floor 67) — ...
    FAIL A1 anchor v0.64.0: history is SHALLOW — ...
    FAIL A1 anchor v0.64.0: 28 id-first delivery commits reachable from the tag != pinned ANCHOR_DELIVERY 67 (BELOW by 39) — truncated history or instrument rot ...
    FAIL A0 anchor v0.64.0: the release window's previous tag is underivable (None), ...
    FAIL A3: live delivery scan 28 < anchor 67 — ...
    status-evidence-anchor: v0.64.0 — 28 delivery commits (pinned 67), 401 artifacts (pinned 401), lag UNDERIVABLE
```

Note `401 artifacts (pinned 401)` even at depth 30: the programme anchor is
shallow-insensitive by design (a tree is complete however shallow the
ancestry); it exists to see instrument rot, which the unit tests exercise.

### full clone — 1055 first-parent commits, shallow=false (both green)

```
--- OLD: EXIT=0
    status-evidence: 114 artifacts across 59 release files, 67 delivery commits matched, 62 done-when predicates evaluated, 17 release-scope archaeology checks (0 skipped), 0 failures
--- NEW: EXIT=0
    status-evidence: 114 artifacts across 59 release files, 67 delivery commits matched, 62 done-when predicates evaluated, 17 release-scope archaeology checks (0 skipped), 0 failures
    status-evidence-anchor: v0.64.0 — 67 delivery commits (pinned 67), 401 artifacts (pinned 401), lag 0
```

## 5. Both pin directions and instrument rot (unit tests, fixture repo)

`AnchorFixture` is a real git repo: two artifacts delivered id-first before
`v0.64.0`, one after (anchor truth 2 delivery / 3 artifacts; live 3 / 4).

| test | mutation of the world | verdict |
|---|---|---|
| `test_pin_below_and_above_are_both_red` | delivery pinned 1 / 3, programme pinned 2 / 4 | `ABOVE by 1` / `BELOW by 1` each |
| `test_id_regex_rot_is_red` | `ARTIFACT_ID` narrowed to `RQ-99-*` | A1 `0 id-first ... BELOW by 2` |
| `test_release_glob_rot_is_red` | `glob.glob` drops `release-v*` | A2 `1 artifacts ... BELOW by 2` on the unchanged tag tree |
| `test_shallow_clone_tag_unreachable_is_red` | `git clone --depth 2` | A1 + A2 underivable, SHALLOW |
| `test_shallow_clone_truncated_ancestry_is_red` | `--depth 4` | A1 `1 ... BELOW by 1`; A2 green |
| `test_shallow_clone_with_equal_count_is_still_red` | `--depth 5` (count happens to equal) | red on the SHALLOW declaration |
| `test_full_clone_is_green` | `git clone` | green, exact |
| `test_lag_one_warns_with_the_values_to_paste` / `test_lag_two_is_red` | next minor tagged | `ANCHOR-LAG` warning carrying `ANCHOR_TAG = "v0.65.0" / ANCHOR_DELIVERY = 3 / ANCHOR_PROGRAMME = 4`; two minors red |

## 6. Mutation sensitivity of the tests

Ten mutations applied to the checker, suite run, checker restored
byte-identical (baseline 96 tests, 0 failing):

```
M1  drop the shallow/no-git red            3 killed  no_git, tag_unreachable, equal_count_still_red
M2  drop the A1 equality                   3 killed  id_regex_rot, pin_below_and_above, truncated_ancestry
M3  drop the A2 equality                   2 killed  pin_below_and_above, release_glob_rot
M4  drop the P3 walk                       1 killed  yaml_in_unscanned_subdir_is_p3
M5  skip artifact-less yaml silently       1 killed  artifactless_topic_yaml_is_p4
M6  tolerate two minors of lag             1 killed  lag_two_is_red
M7  drop the dead-waiver rule              1 killed  waiver_channel_cannot_stand
M8  drop the A3 live-delivery floor        1 killed  live_delivery_below_anchor_is_red
M9  mis-copy ANCHOR_DELIVERY 67 -> 66      1 killed  live_repo_anchor_is_exact_and_current
M10 hand-pin PROGRAMME_FLOOR = 379 again   1 killed  live_repo_is_green_and_meets_the_floor
```

## 7. Moving the anchor at the next release

After `v0.65.0` is tagged the checker prints, on every run until it is done:

```
ANCHOR-LAG: v0.64.0 is one minor behind the window's previous tag v0.65.0; move it in the post-tag PR —
ANCHOR_TAG = "v0.65.0" / ANCHOR_DELIVERY = <derived> / ANCHOR_PROGRAMME = <derived> / PROGRAMME_DELETED_SINCE_ANCHOR = 0
```

Paste the three lines into `scripts/status_evidence_check.py` and the pin
`SYNTH-STATUS-EVIDENCE-ANCHOR-1183` in `claims.yaml` (the post-tag "fill the
step-8 attestation" PR is the natural place). The values are the checker's
own derivation; a mis-copy fails A1/A2 in the same PR, and a skipped release
is red at lag 2.
