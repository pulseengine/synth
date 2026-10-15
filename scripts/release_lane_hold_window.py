#!/usr/bin/env python3
"""RQ-87-BASEMOVE (#1269) — does a release lane survive a moving base, or must
the hold window be stated?

THE REFUTING COMMAND, run first: "Count open dependabot PRs with auto-merge
ENABLED during a release window; a zero means the hazard is not live that cycle."

MEASURED: ONE open dependabot PR, auto-merge ENABLED on ZERO of them (and zero
across ALL authors). So BY THE STATED CRITERION THE LANE IS REFUTED for this
cycle — and that refutation is reported rather than worked around.

BUT THE CRITERION IS NARROWER THAN THE HAZARD IT NAMES, which is this lane's
actual finding. #1269 established that CHECK2 is branch CURRENCY: a lane PR goes
behind when its BASE MOVES, by whatever mechanism. Auto-merge is one mechanism.
A manual dependabot merge is another. AND THE RELEASE'S OWN SERIALIZED LANE
MERGES ARE A THIRD — each merge moves main, so every remaining lane PR is stale
the moment the previous one lands. That third route needs no dependabot at all,
it is guaranteed rather than contingent, and an auto-merge census cannot see it.
It is also why v0.86 consolidated six PRs into one.

SO THE HOLD WINDOW IS STATED, with numbers, which is the done-when's second
branch. The two inputs are DERIVED rather than assumed:

  the lane count   -> open PRs partitioned by `user.type == "Bot"`, NOT by a
                      login spelling. This is load-bearing: the REST API reports
                      dependabot as `dependabot[bot]` while the `gh` CLI renders
                      the same account as `app/dependabot`, so a filter written
                      against the CLI spelling silently fails against REST and
                      counts the bot as a lane. That exact error inflated this
                      lane's first reading from 3 to 4.
  the cycle cost   -> the MEDIAN wall-clock of completed CI runs in the sampled
                      window, not a best case. The spread is the point: a
                      three-minute run and a five-hour run are both in it.

The product of the two is the window, and it is reported with its own inputs so
a reader can re-derive it rather than trust it.

WHAT FOLLOWS FROM IT, stated because the number is otherwise just alarming:
CONSOLIDATE lanes into one PR rather than serialize them. The hold window scales
with the NUMBER OF PRs, not with the amount of work, so N lanes in one PR cost
one cycle and N lanes in N PRs cost N.

AND THE WINDOW IS A POLICY COST, NOT A PLATFORM ONE — measured, and it changes
what the number means. This repository's branch protection has
`required_status_checks.strict = FALSE`, so GitHub does NOT require a PR to be
up to date with its base and does NOT invalidate a stale-base PR's green checks.
Verified live: after a lane merged, the three remaining open PRs kept their
checks and all three still merged cleanly onto the new main. So the serialization
is imposed by the release loop's OWN CHECK2 (baseRefOid == origin/main), not by
the platform.

That is a deliberate choice with a recorded reason rather than an accident: a
stale-base PR can merge cleanly at the TEXT level and still break semantically —
this repository has a patch against a moved main that undid an already-merged
dependency bump while presenting three green gates. So CHECK2 stays. But the
honest framing of the window is "the cost of a policy that prevents a measured
failure mode", and the lever is therefore the NUMBER OF PRs, which the loop
controls, rather than the platform setting, which it should not relax.

NOT a CI gate — the report samples the live API and is window-dependent by
construction. CI gates the SELF-TEST.
"""
import argparse
import json
import os
import subprocess
import sys
from datetime import datetime

REPO = "pulseengine/synth"
# HOME is REQUIRED, not incidental: `gh` reads its auth from the user config
# under $HOME, so a stripped env makes every call fail with "please run gh auth
# login" — an authentication error that looks nothing like the missing variable
# that caused it. A stripped env is a broken control, not a clean one.
ENV = {"PATH": os.environ.get("PATH", "/opt/homebrew/bin:/usr/bin:/bin"),
       "HOME": os.environ.get("HOME", "")}


def api(path: str):
    r = subprocess.run(["gh", "api", path], capture_output=True, text=True, env=ENV)
    if r.returncode != 0 or not r.stdout.strip():
        raise RuntimeError(f"API FAILED for {path}: {r.stderr[:160]}")
    return json.loads(r.stdout)


def ts(s: str) -> datetime:
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def partition_prs(prs: list[dict]) -> tuple[list, list]:
    """(lane PRs, bot PRs), split on `user.type` and NOT on a login spelling.

    REST says `dependabot[bot]`; the gh CLI renders it `app/dependabot`. A filter
    written against either spelling fails against the other, silently, and counts
    a bot PR as a lane.
    """
    bots = [p for p in prs if (p.get("user") or {}).get("type") == "Bot"]
    lanes = [p for p in prs if (p.get("user") or {}).get("type") != "Bot"]
    return lanes, bots


def median_cycle_minutes(runs: list[dict]) -> tuple[int | None, list[int]]:
    durs = sorted(
        round((ts(r["updated_at"]) - ts(r["run_started_at"])).total_seconds() / 60)
        for r in runs
        if r.get("name") == "CI" and r.get("status") == "completed"
        and r.get("run_started_at") and r.get("updated_at"))
    return (durs[len(durs) // 2] if durs else None), durs


def held_branches(open_heads: set[str]) -> list[str]:
    """Local lane branches with no open PR — DERIVED, never passed in.

    It was passed in at first, as `--held 7`, and the number went stale inside
    the hour: committing one more lane made it eight while the record still said
    seven. A count of the thing the count lives in has to be derived or it is
    false by construction, which is this repository's own named class.
    """
    r = subprocess.run(["git", "branch", "--list", "v087-*",
                        "--format=%(refname:short) %(objectname)"],
                       capture_output=True, text=True)
    out = []
    for line in r.stdout.strip().split("\n"):
        if not line.strip():
            continue
        name, sha = line.split()
        if sha not in open_heads:
            out.append(name)
    return out


def report(held: int | None = None) -> int:
    prs = api(f"repos/{REPO}/pulls?state=open&per_page=100")
    lanes, bots = partition_prs(prs)
    automerge = [p for p in prs if p.get("auto_merge")]
    print("THE REFUTING COMMAND:")
    print(f"  open PRs {len(prs)}  ->  lanes {len(lanes)}, bots {len(bots)} "
          f"(partitioned by user.type, not a login spelling)")
    print(f"  bot PRs with auto-merge ENABLED: "
          f"{len([p for p in bots if p.get('auto_merge')])}")
    print(f"  ANY author with auto-merge ENABLED: {len(automerge)}")
    print(f"  -> {'REFUTED by the stated criterion: the AUTO-MERGE hazard is not live this cycle' if not automerge else 'auto-merge hazard LIVE'}")

    runs = api(f"repos/{REPO}/actions/runs?per_page=100")["workflow_runs"]
    med, durs = median_cycle_minutes(runs)
    if med is None:
        print("\nVACUOUS: no completed CI run in the window — refusing to state a cycle cost")
        return 1
    print(f"\nCI cycle, completed runs n={len(durs)}: "
          f"min={durs[0]} median={med} max={durs[-1]} minutes")
    open_heads = {p["head"]["sha"] for p in prs}
    heldb = held_branches(open_heads)
    n_held = len(heldb) if held is None else held
    total = len(lanes) + n_held
    print(f"\nheld branches (DERIVED: local v087-* with no open PR): {len(heldb)}")
    for b in heldb:
        print(f"    {b}")
    print(f"\nHOLD WINDOW: {len(lanes)} open lane PR(s) + {n_held} held branch(es) = {total} lanes")
    print(f"  serialized at the median cycle => {total * med} min "
          f"({total * med / 60:.1f} h) of rebase-and-revalidate, before queue starvation")
    print(f"\nBUT THE CRITERION IS NARROWER THAN THE HAZARD: CHECK2 is branch CURRENCY, so")
    print(f"  the release's OWN serialized merges stale every remaining lane with no")
    print(f"  dependabot involved at all — guaranteed, not contingent, and invisible to an")
    print(f"  auto-merge census. CONSOLIDATE: the window scales with the NUMBER OF PRs,")
    print(f"  not the amount of work.")
    return 0


def self_test() -> int:
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    # THE SPELLING TRAP, both directions — this is the case that caught the
    # lane's own first reading (3 lanes read as 4).
    sample = [
        {"number": 1, "user": {"login": "avrabe", "type": "User"}},
        {"number": 2, "user": {"login": "dependabot[bot]", "type": "Bot"}},
    ]
    lanes, bots = partition_prs(sample)
    ok(len(lanes) == 1 and len(bots) == 1,
       "user.type partitions a REST `dependabot[bot]` correctly")
    cli_spelled = [dict(sample[1], user={"login": "app/dependabot", "type": "Bot"})]
    ok(partition_prs(cli_spelled) == ([], cli_spelled),
       "and the gh-CLI spelling `app/dependabot` lands in the SAME partition, so "
       "the derivation is spelling-independent")
    # NEGATIVE CONTROL: a login-based filter must be shown to FAIL, or the case
    # above proves nothing about why user.type was chosen.
    by_login = [p for p in cli_spelled if p["user"]["login"] != "dependabot[bot]"]
    ok(len(by_login) == 1,
       "NEGATIVE CONTROL: a filter written on the REST spelling KEEPS the "
       "CLI-spelled bot — the silent failure this derivation avoids")

    # The cycle cost must come from a MEDIAN over real runs, and an empty
    # population must be refused rather than defaulted.
    med, durs = median_cycle_minutes([])
    ok(med is None and durs == [],
       "an empty run population yields no median — the report REFUSES it as "
       "VACUOUS rather than stating a cycle cost over nothing")
    runs = [{"name": "CI", "status": "completed",
             "run_started_at": "2026-10-15T00:00:00Z", "updated_at": f"2026-10-15T0{h}:00:00Z"}
            for h in (1, 2, 3)]
    med2, durs2 = median_cycle_minutes(runs)
    ok(med2 == 120 and durs2 == [60, 120, 180],
       f"the median is computed over the real spread, not a best case (got {med2})")
    ok(median_cycle_minutes(runs + [{"name": "Other", "status": "completed",
                                     "run_started_at": "2026-10-15T00:00:00Z",
                                     "updated_at": "2026-10-15T09:00:00Z"}])[0] == 120,
       "and a non-CI workflow does not enter the CI cycle population")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--held", type=int, default=None,
                    help="override the DERIVED held-branch count (normally omit it: the "
                         "count is derived from local v087-* branches with no open PR, "
                         "because a passed-in count goes stale the moment another lane lands)")
    a = ap.parse_args()
    return self_test() if a.self_test else report(a.held)


if __name__ == "__main__":
    sys.exit(main())
