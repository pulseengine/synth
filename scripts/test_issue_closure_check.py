#!/usr/bin/env python3
"""Unit tests for scripts/issue_closure_check.py (RQ-71-ISSUESCOPE, #1250).

The gate that polices which issues a release may close does not get to be the
unchecked one. Every rule here is proven RED-FIRST against a synthetic artifact
set, so the suite fails if the rule stops firing — a check that cannot fail on
its own definition of failure is not a check (the v0.57 lesson, and v0.70 found
four such gates in this very family).

The synthetic sets are deliberately NOT the live repo: a test bound to the
repo's current artifacts goes vacuous the moment the release moves on.
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import issue_closure_check as C  # noqa: E402
from status_evidence_check import authorised_close_set  # noqa: E402

FAILS = 0


def check(name: str, cond: bool, detail: str = "") -> None:
    global FAILS
    if cond:
        print(f"  ok   {name}")
    else:
        FAILS += 1
        print(f"  FAIL {name}{(' — ' + detail) if detail else ''}")


def art(art_id: str, status: str, issue: str, version=(0, 71), scope=None):
    """One artifact tuple in load_release_artifacts' shape:
    (path, version, id, status, fields, links, release)."""
    fields = {"issue": issue}
    if scope is not None:
        fields["issue-scope"] = scope
    return (Path(f"artifacts/release-v{version[0]}.{version[1]}/{art_id}.yaml"),
            version, art_id, status, fields, [], f"v{version[0]}.{version[1]}")


def run(artifacts, closed, allow_unclosed=False, open_issues=None):
    """Drive C.check without touching disk, by stubbing the loader.

    `open_issues=None` means "live state unavailable" and exercises the WINDOW
    fallback; a list (even an empty one) exercises the STATE path, which is the
    one the gate should normally take."""
    orig = C.load_release_artifacts
    C.load_release_artifacts = lambda root, glob: (artifacts, [])
    try:
        return C.check(Path("."), "v0.71", set(closed), allow_unclosed,
                       None if open_issues is None else set(open_issues))
    finally:
        C.load_release_artifacts = orig


def main() -> int:
    # ---- the authorised set is derived, not declared -----------------------
    delivered = art("RQ-71-A", "implemented", "#100")
    undelivered = art("RQ-71-B", "proposed", "#200")
    outlives = art("RQ-71-C", "implemented", "#300", scope="outlives")
    auth, held = authorised_close_set([delivered, undelivered, outlives], (0, 71))
    check("a delivered artifact authorises closing its issue", auth.keys() == {100})
    check("an UNdelivered artifact authorises nothing", 200 not in auth)
    check("`issue-scope: outlives` moves the issue to held-open",
          held.keys() == {300} and 300 not in auth)

    # ---- version scoping ---------------------------------------------------
    older = art("RQ-70-Z", "implemented", "#900", version=(0, 70))
    auth70, _ = authorised_close_set([delivered, older], (0, 71))
    check("another release's artifact is out of scope", auth70.keys() == {100})

    # ---- RED 1: closed but not authorised (the v0.69 shape) ----------------
    f, _w, _a, _h = run([delivered], closed=[100, 999])
    check("RED closed-but-not-authorised fires",
          any("CLOSED BUT NOT AUTHORISED: #999" in x for x in f), str(f))

    # ---- RED 2: a held-open issue was closed anyway ------------------------
    f, _w, _a, _h = run([delivered, outlives], closed=[100, 300])
    check("RED held-open-but-closed fires",
          any("HELD OPEN BUT CLOSED: #300" in x for x in f), str(f))
    check("held-open-but-closed is NOT reported as merely unauthorised",
          not any("CLOSED BUT NOT AUTHORISED: #300" in x for x in f),
          "the specific diagnosis must win over the generic one")

    # ---- RED 3: authorised but left open -----------------------------------
    #
    # RQ-72-ISSUEGATE (#1250) deliverable (e): with no live state this can only
    # speak about the WINDOW, and the message now says so. Answering "did it
    # close since the tag?" while appearing to answer "is it closed?" is what
    # made the gate state a falsehood at the v0.71 tag.
    f, _w, _a, _h = run([delivered], closed=[])
    check("RED authorised-but-not-closed fires (window wording, no state)",
          any("AUTHORISED BUT NOT CLOSED IN THIS WINDOW: #100" in x for x in f),
          str(f))
    check("the window message ADMITS it did not check state",
          any("live issue state was not available" in x for x in f), str(f))
    f, w, _a, _h = run([delivered], closed=[], allow_unclosed=True)
    check("--allow-unclosed downgrades it to a warning",
          not f and any("AUTHORISED BUT NOT CLOSED IN THIS WINDOW: #100" in x
                        for x in w))

    # ---- RED 3b: judged by STATE, which is the honest question --------------
    f, _w, _a, _h = run([delivered], closed=[], open_issues=[100])
    check("STATE: an authorised issue that is OPEN fires",
          any("AUTHORISED BUT STILL OPEN: #100" in x for x in f), str(f))

    # THE v0.71 CASE, as a regression. #1250 was authorised AND closed — just
    # closed BEFORE the tag, so it was absent from the window. The old gate
    # printed "AUTHORISED BUT NOT CLOSED" about an issue that was closed.
    f, _w, _a, _h = run([delivered], closed=[], open_issues=[])
    check("STATE: authorised + closed-before-the-window is SATISFIED",
          not f, str(f))

    # ---- RED 3c: the mirror the window could not see ------------------------
    # An `issue-scope: outlives` issue closed OUTSIDE the window is invisible to
    # the closed-set, because the closed-set only holds what closed since the tag.
    f, _w, _a, _h = run([outlives], closed=[], open_issues=[])
    check("STATE: held-open but already closed (outside the window) fires",
          any("HELD OPEN BUT ALREADY CLOSED: #300" in x for x in f), str(f))
    f, _w, _a, _h = run([outlives], closed=[], open_issues=[300])
    check("STATE: held-open and genuinely open is SATISFIED", not f, str(f))

    # ---- GREEN: the authorised set closed exactly, held-open left open -----
    f, _w, _a, _h = run([delivered, undelivered, outlives], closed=[100])
    check("GREEN when closures equal the authorised set", not f, str(f))

    # ---- ANTI-VACUITY: the check must refuse to pass on an empty basis -----
    f, _w, _a, _h = run([], closed=[100])
    check("VACUOUS on zero artifacts", any("VACUOUS" in x for x in f), str(f))
    f, _w, _a, _h = run([art("RQ-71-N", "implemented", "")], closed=[100])
    check("VACUOUS when no artifact names an issue",
          any("VACUOUS" in x for x in f), str(f))

    # ---- parse_version refuses silently-unscoped input ---------------------
    ok = False
    try:
        C.parse_version("main")
    except ValueError:
        ok = True
    check("an unparseable release raises instead of scoping to nothing", ok)

    # ---- THE v0.70 REPLAY, against the real shipped release ---------------
    # The synthetic sets above prove each rule fires. This proves the rule
    # would have caught the thing it was built for, using the REAL artifacts
    # of a SHIPPED release.
    #
    # RQ-72-ISSUEGATE (#1250) deliverable (d) — THE PREVIOUS SENTENCE HERE WAS
    # FALSE and is corrected rather than deleted. It said the replay was
    # "frozen, so it cannot go vacuous as the programme moves on". It is not
    # frozen: `C.check(root, ...)` loads the LIVE artifacts under
    # artifacts/release-v0.70/, which are editable files. v0.71 is what made
    # this replay pass, by retroactively adding `issue-scope: outlives` to two
    # already-shipped v0.70 artifacts — so the expected values were reached by
    # editing the data the test reads.
    #
    # It is kept live, not snapshotted, deliberately: the thing worth asserting
    # is that the SHIPPED artifacts still express v0.70's decision, and a
    # snapshot would assert only that a copy in this file still does. What it
    # therefore is NOT is protection against someone changing those artifacts —
    # it is the DETECTOR for exactly that. Deleting either `issue-scope:
    # outlives` line reds four assertions below, which is the property that
    # matters and is a different property from "frozen".
    #
    # v0.70 closed exactly five issues on its tag and deliberately left #1331
    # (RQ-70-NPA) and #1318 (RQ-70-FALCONCORPUS) OPEN, because each issue asks
    # a wider question than its artifact delivered. That decision lived in
    # prose and nothing checked it.
    root = Path(__file__).resolve().parent.parent
    V70_CLOSED = {1321, 1333, 1334, 1335, 1337}
    f, _w, auth, held = C.check(root, "v0.70", set(V70_CLOSED))
    check("v0.70 replay: the real close-set passes", not f, str(f))
    check("v0.70 replay: #1331 and #1318 are held open",
          set(held) == {1331, 1318}, str(sorted(held)))
    check("v0.70 replay: the five closed issues are the authorised set",
          set(auth) == V70_CLOSED, str(sorted(auth)))
    f, _w, _a, _h = C.check(root, "v0.70", V70_CLOSED | {1331})
    check("v0.70 replay: closing #1331 anyway is CAUGHT",
          any("HELD OPEN BUT CLOSED: #1331" in x for x in f), str(f))

    print(f"issue-closure-tests: {FAILS} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
