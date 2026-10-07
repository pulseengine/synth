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

import pathlib
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


def art(art_id: str, status: str, issue: str, version=(0, 71), scope=None,
        disposition=None):
    """One artifact tuple in load_release_artifacts' shape:
    (path, version, id, status, fields, links, release)."""
    fields = {"issue": issue}
    if scope is not None:
        fields["issue-scope"] = scope
    if disposition is not None:
        fields["disposition"] = disposition
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


# ---------------------------------------------------------------------------
# RQ-75-CLOSEWINDOW (#1391): drive `closed_since` — the NETWORK path — against
# a recorded `gh` response.
#
# v0.74 found this function truncating its own window to a DAY
# (`closed:>={date[:10]}`, which GitHub reads as MIDNIGHT), fixed it, and did
# NOT test it: the evidence was a measurement recorded in the docstring. A
# regression would have been silent again, and the failure mode is not a missed
# closure — it is the gate reporting an EXTERNAL reporter's correctly-closed
# issue as `CLOSED BUT NOT AUTHORISED`, whose prescribed remedy is "Reopen it".
#
# The recorded table encodes what the LIVE API actually returned at the v0.74
# cut, both halves measured on one tree:
#
#     closed:>=2026-09-24            -> #1341, #1349, #1269, #1331   (4)
#     closed:>=2026-09-24T15:02:41Z  ->               #1269, #1331   (2)
#
# where 15:02:41Z is v0.73.0's own commit and #1341/#1349 closed at 03:34Z, in
# v0.72's wave. So the day-granular qualifier is not a hypothetical: it is the
# contaminated answer, keyed separately, and a `closed_since` that builds it
# gets it. No assertion inspects the qualifier string — the WINDOW's content is
# what matters, and asserting on the string would pass a rewrite that formatted
# it differently while still reading midnight.
#
# An unrecorded call RAISES. A recorder that returned empty would let this pass
# while reaching nothing, which is the vacuity being tested for.
#
# PROVEN POTENT, each mutation verified present on disk before measuring:
#
#     the pre-v0.74 day-granular truncation `{date[:10]}`      -> RED
#     a "normalising" rewrite: date.split("T")[0]              -> RED
#
# The second one is why no assertion reads the qualifier STRING: a rewrite that
# spells midnight differently is still midnight, and a string assertion would
# have passed it. Both mutations fail with the window naming #1341 and #1349 —
# the two v0.72 closures a midnight window swallows.

CW_REPO = "pulseengine/synth"
CW_TAG = "v0.73.0"
CW_STAMP = "2026-09-24T15:02:41Z"
CW_DAY_SET = [1341, 1349, 1269, 1331]     # midnight window: v0.72's wave too
CW_EXACT_SET = [1269, 1331]               # the correct window


class CwUnrecorded(AssertionError):
    pass


class _CwRecorder:
    def __init__(self, table):
        self.table = table
        self.calls = []

    def __call__(self, args, **kw):
        key = tuple(args)
        self.calls.append(key)
        if key not in self.table:
            raise CwUnrecorded(f"unrecorded call: {key!r}")
        rc, out = self.table[key]
        import subprocess as _sp
        return _sp.CompletedProcess(args=list(args), returncode=rc,
                                    stdout=out, stderr="")


def _cw_table():
    import json as _json
    body = lambda ns: _json.dumps([{"number": n} for n in ns])
    return {
        ("gh", "api", f"repos/{CW_REPO}/commits/{CW_TAG}",
         "--jq", ".commit.committer.date"): (0, CW_STAMP),
        # the two qualifiers are DIFFERENT keys, and answer differently
        ("gh", "issue", "list", "--repo", CW_REPO, "--state", "closed",
         "--limit", "200", "--search", f"closed:>={CW_STAMP[:10]}",
         "--json", "number"): (0, body(CW_DAY_SET)),
        ("gh", "issue", "list", "--repo", CW_REPO, "--state", "closed",
         "--limit", "200", "--search", f"closed:>={CW_STAMP}",
         "--json", "number"): (0, body(CW_EXACT_SET)),
    }


def _cw_run(table):
    import types
    rec = _CwRecorder(table)
    orig, C.subprocess = C.subprocess, types.SimpleNamespace(run=rec)
    try:
        return C.closed_since(CW_TAG, CW_REPO), rec
    finally:
        C.subprocess = orig


def next_release_tag_tests() -> None:
    """v0.81 round-2 cold review, finding 9.

    `next_release_tag` was CHANGED by round 1 (mixed-arity tuple comparison) and
    pinned by nothing, while every other correction in that commit got a test.
    Its own comment names the risk it leaves: the live caller passes three
    components, so the defect was latent — and the next caller would not have
    known. Driven through a stub so it needs no network.
    """
    print("  -- next_release_tag: arity and ordering --")
    TAGS = ("refs/tags/v0.76.0\nrefs/tags/v0.77.0\nrefs/tags/v0.78.0\n"
            "refs/tags/v0.81.0\nrefs/tags/not-a-version\n")

    def _stub(tag):
        import subprocess
        real = subprocess.run
        class R:
            stdout = TAGS
        subprocess.run = lambda *a, **k: R()
        try:
            return C.next_release_tag(tag, "owner/repo")
        finally:
            subprocess.run = real

    # THE DEFECT: `(0,77,0) > (0,77)` is True, so a 2-component release name
    # matched its OWN tag and bounded the window at the release being audited —
    # excluding the whole closure wave the gate exists to read.
    check("next_release_tag: a 2-component name does NOT match its own tag",
          _stub("v0.77") == "v0.78.0", f"got {_stub('v0.77')!r}")
    check("next_release_tag: the 3-component form agrees with it",
          _stub("v0.77.0") == "v0.78.0", f"got {_stub('v0.77.0')!r}")
    check("next_release_tag: the NEWEST release has no successor",
          _stub("v0.81.0") is None and _stub("v0.81") is None)
    check("next_release_tag: it returns the IMMEDIATE successor, not the newest",
          _stub("v0.76.0") == "v0.77.0", f"got {_stub('v0.76.0')!r}")
    check("next_release_tag: a non-version tag is ignored, not crashed on",
          _stub("v0.78.0") == "v0.81.0", f"got {_stub('v0.78.0')!r}")
    check("next_release_tag: a non-version RELEASE name returns None",
          _stub("not-a-version") is None)


def r11conflict_tests() -> None:
    """RQ-81-R11CONFLICT (#1430): the two directions, and the controls.

    Every assertion here was run against the PRE-FIX gate first. Recorded
    results, so a later reader can tell which of these could ever have failed:
    the five marked (RED) failed, and the three CONTROLS passed throughout —
    which is what attributes the reds to the new rules rather than to the
    fixture.
    """
    print("  -- RQ-81-R11CONFLICT: the third remedy (direction 2) --")

    # (RED) The conflict itself: a REFUTED artifact that declares `closes`
    # authorises its issue WITHOUT a claiming status, so R11 never has to be
    # lied to. Pre-fix this returned an EMPTY authorised set.
    refuted = [art("RQ-X-REFUTED", "proposed", "#1243", (0, 77),
                   scope="closes", disposition="refuted")]
    auth, held = authorised_close_set(refuted, (0, 77))
    check("R11CONFLICT: refuted + `issue-scope: closes` AUTHORISES without claiming",
          auth.get(1243) == "RQ-X-REFUTED" and not held, f"auth={auth} held={held}")

    # CONTROL, and the half that could make the gate WEAKER. A refutation alone
    # must authorise NOTHING — the declaration is what carries the intent, so an
    # operator cannot close an issue by recording a refutation and saying no more.
    bare = [art("RQ-X-BARE", "proposed", "#1243", (0, 77), disposition="refuted")]
    auth, _h = authorised_close_set(bare, (0, 77))
    check("R11CONFLICT CONTROL: a refutation ALONE authorises nothing",
          1243 not in auth, f"auth={auth}")

    # CONTROL: the scoping. `deferred` and `partial` did NOT ship their scope, so
    # `closes` beside them must stay inert — otherwise this remedy becomes a way
    # to close an issue no release delivered, which is the v0.69 accident.
    for disp in ("deferred", "partial"):
        a = [art("RQ-X-" + disp.upper(), "proposed", "#1243", (0, 77),
                 scope="closes", disposition=disp)]
        auth, _h = authorised_close_set(a, (0, 77))
        check(f"R11CONFLICT CONTROL: `{disp}` + closes authorises NOTHING",
              1243 not in auth, f"auth={auth}")

    # CONTROL: `outlives` still wins over the new branch. A refuting artifact
    # that says "do not close this" must be HELD, not authorised.
    both = [art("RQ-X-OUT", "proposed", "#1243", (0, 77),
                scope="outlives", disposition="refuted")]
    auth, held = authorised_close_set(both, (0, 77))
    check("R11CONFLICT CONTROL: `outlives` still outranks the refuted-closes branch",
          1243 not in auth and held.get(1243) == "RQ-X-OUT", f"auth={auth} held={held}")

    print("  -- RQ-81-R11CONFLICT: forward blindness (direction 1) --")

    # THE NON-WEAKENING PROPERTY, pinned rather than asserted in prose: when
    # auditing the release being CUT, no artifact carries a higher version, so
    # the later-set is empty and every live verdict is untouched.
    cut = [art("RQ-A", "implemented", "#10", (0, 77)),
           art("RQ-B", "implemented", "#11", (0, 76))]
    check("R11CONFLICT: later_attribution is EMPTY for the release being cut",
          C.later_attribution(cut, (0, 77)) == {},
          str(C.later_attribution(cut, (0, 77))))

    # (RED) A LATER release delivered it. Auditing the earlier one must NOT say
    # "Reopen it". Pre-fix: `CLOSED BUT NOT AUTHORISED ... Reopen it`.
    hist = [art("RQ-OLD", "implemented", "#10", (0, 77)),
            art("RQ-NEW", "implemented", "#99", (0, 80))]
    f, w, _a, _h = run(hist, {10, 99}, allow_unclosed=True, open_issues=[])
    check("R11CONFLICT: an issue a LATER release delivered is NOT a failure",
          not any("#99" in x for x in f), str(f))
    check("R11CONFLICT: and it is reported, attributed to that later release",
          any("ATTRIBUTED TO v0.80: #99" in x for x in w), str(w))
    check("R11CONFLICT: the attribution says NOT to reopen it",
          any("#99" in x and "NOT something to reopen" in x for x in w), str(w))

    # (RED) LAUNDERING REFUSED FORWARD. A later release saying `outlives` is a
    # refusal to close, and a closure overrides it. This must stay a FAILURE —
    # the assertion that keeps direction 1 from becoming an excuse-generator.
    laund = [art("RQ-OLD", "implemented", "#10", (0, 77)),
             art("RQ-HOLD", "implemented", "#99", (0, 80), scope="outlives")]
    f, _w, _a, _h = run(laund, {10, 99}, allow_unclosed=True, open_issues=[])
    check("R11CONFLICT: a LATER `outlives` + a closure is still a FAILURE",
          any("HELD OPEN BY v0.80 BUT CLOSED: #99" in x for x in f), str(f))

    # (RED) THE PRECEDENCE, and the bug this function shipped in its first draft.
    # v0.78 held #99 open; v0.80 then DELIVERED it. Hold-open, continue, deliver,
    # close is the normal progression of a long-running issue, and the draft read
    # it as v0.78's refusal being overridden — emitting "Reopen it" for a
    # correctly-closed issue. The MOST RECENT decision governs.
    prog = [art("RQ-OLD", "implemented", "#10", (0, 77)),
            art("RQ-HELD", "implemented", "#99", (0, 78), scope="outlives"),
            art("RQ-DELIVERED", "implemented", "#99", (0, 80))]
    f, w, _a, _h = run(prog, {10, 99}, allow_unclosed=True, open_issues=[])
    check("R11CONFLICT: hold-open in v0.78 then DELIVERED in v0.80 is NOT a reopen",
          not any("#99" in x for x in f), str(f))
    check("R11CONFLICT: and it attributes to v0.80, the release that delivered it",
          any("ATTRIBUTED TO v0.80: #99" in x for x in w), str(w))

    # ...and the MIRROR of that precedence: delivered in v0.78, then a LATER
    # release declares `outlives`. The newest word is the refusal, so it holds.
    rev = [art("RQ-OLD", "implemented", "#10", (0, 77)),
           art("RQ-DELIVERED", "implemented", "#99", (0, 78)),
           art("RQ-HELD", "implemented", "#99", (0, 80), scope="outlives")]
    f, _w, _a, _h = run(rev, {10, 99}, allow_unclosed=True, open_issues=[])
    check("R11CONFLICT: delivered in v0.78 then HELD in v0.80 -> the hold governs",
          any("HELD OPEN BY v0.80 BUT CLOSED: #99" in x for x in f), str(f))

    # (v0.81 round-1 cold review, finding 7.) THE ORDERING OF `prior_attribution`
    # WAS UNTESTED while its new twin's was. `sorted(versions)` -> reverse=True
    # survived this suite at rc=0, while the identical mutation on
    # `later_attribution` reds with 3 failures. On real data the reversal flips
    # 21 of 86 attributions at v0.81 and converts a "Reopen it" FAILURE into a
    # warning. The docstring claims the two functions differ in ONE CHARACTER —
    # "a property a reviewer can check at a glance" — and only one of the two
    # characters was pinned.
    lo = art("RQ-70-LOW", "implemented", "#900", (0, 70))
    hi = art("RQ-76-HIGH", "implemented", "#900", (0, 76), scope="outlives")
    pa = C.prior_attribution([lo, hi], (0, 77))
    check("prior_attribution keeps the HIGHEST release below the target",
          pa.get(900, (None,))[0] == (0, 76),
          f"got {pa.get(900)} — a reversed sort would return v0.70 and turn a "
          f"later hold-open into an earlier authorisation")
    check("...and it reports that release's OWN verdict, not the other's",
          pa.get(900, (None, None))[1] == "held-open", str(pa.get(900)))
    # the MIRROR, so the pair is pinned symmetrically
    la = C.later_attribution([lo, hi], (0, 69))
    check("later_attribution keeps the HIGHEST release above the target",
          la.get(900, (None,))[0] == (0, 76), str(la.get(900)))

    # And the two functions differ in ONE comparison, which is the property a
    # reviewer checks: the same artifact set, audited from both sides.
    pair = [art("RQ-LOW", "implemented", "#1", (0, 70)),
            art("RQ-HIGH", "implemented", "#2", (0, 80))]
    check("R11CONFLICT: prior sees only BELOW, later sees only ABOVE",
          set(C.prior_attribution(pair, (0, 77))) == {1}
          and set(C.later_attribution(pair, (0, 77))) == {2},
          f"prior={C.prior_attribution(pair,(0,77))} later={C.later_attribution(pair,(0,77))}")


def closed_since_tests() -> None:
    got, rec = _cw_run(_cw_table())
    check("closed_since: window excludes the PREVIOUS release's closure wave",
          got == set(CW_EXACT_SET),
          f"got {sorted(got)}, want {CW_EXACT_SET} — "
          f"{sorted(set(CW_DAY_SET) - set(CW_EXACT_SET))} closed before the tag")

    # RED-FIRST, in the direction that matters: if the only recorded answer is
    # the day-granular one, a correct `closed_since` must MISS and raise rather
    # than silently accept the contaminated set.
    day_only = _cw_table()
    del day_only[("gh", "issue", "list", "--repo", CW_REPO, "--state", "closed",
                  "--limit", "200", "--search", f"closed:>={CW_STAMP}",
                  "--json", "number")]
    try:
        _cw_run(day_only)
        check("closed_since: a day-granular-only table is REFUSED", False,
              "it answered from the midnight window")
    except CwUnrecorded:
        check("closed_since: a day-granular-only table is REFUSED", True)

    # and the recorder is loud in general, or every assertion above is vacuous
    try:
        _cw_run({})
        check("closed_since recorder: an unrecorded call raises", False)
    except CwUnrecorded:
        check("closed_since recorder: an unrecorded call raises", True)


def main_exit_code_tests() -> None:
    """RQ-76-CLOSUREMAIN (#1404): drive `main()` and assert its EXIT CODE.

    v0.75 drove `closed_since` and left its two callers undriven, and said so.
    `main()`'s exit code is what every caller consumes — the merge ritual, the
    tag script, a human reading `$?` — so an assertion about `check()` is an
    assertion about something no caller reads.

    The three codes are distinguished on purpose. 0 and 1 are "the gate ran";
    2 is "the gate REFUSED to run", which a caller must be able to tell apart
    from "ran and found nothing wrong". A refusal collapsed into 0 is the
    vacuous pass this lane exists to remove.
    """
    import contextlib
    import io

    def run_main(argv: list[str]) -> tuple[int, str]:
        buf = io.StringIO()
        orig = sys.argv
        sys.argv = ["issue_closure_check.py", *argv]
        try:
            with contextlib.redirect_stdout(buf):
                rc = C.main()
        except SystemExit as ex:          # argparse errors must not read as 0
            rc = ex.code if isinstance(ex.code, int) else 1
        finally:
            sys.argv = orig
        return rc, buf.getvalue()

    root = str(pathlib.Path(__file__).resolve().parents[1])

    # (a) a clean judgement exits 0
    rc, out = run_main(["--release", "v0.75.0", "--root", root,
                        "--closed", "1223,1391", "--open", "1062,1318",
                        "--allow-unclosed"])
    check("main(): a clean judgement exits 0", rc == 0, f"- rc={rc}")

    # (b) a real failure exits 1 — an issue closed that nothing authorises
    rc, out = run_main(["--release", "v0.75.0", "--root", root,
                        "--closed", "999999", "--open", "1062,1318"])
    check("main(): an unauthorised closure exits 1", rc == 1, f"- rc={rc}")
    check("main(): ...and says which issue", "999999" in out, f"- {out[:120]}")

    # (c) an EMPTY live-open read REFUSES with 2 rather than judging
    rc, out = run_main(["--release", "v0.75.0", "--root", root,
                        "--closed", "", "--open", ""])
    check("main(): an EMPTY open set REFUSES with exit 2", rc == 2, f"- rc={rc}")
    check("main(): ...and the refusal names the count it will not judge",
          "REFUSED" in out and "authorised" in out, f"- {out[:120]}")
    # The two wrong behaviours it replaces, asserted as ABSENT rather than
    # described: no vacuous pass, and no sentence claiming a live issue is
    # not open.
    check("main(): the refusal emits NO held-open-already-closed sentence",
          "HELD OPEN BUT ALREADY CLOSED" not in out)


def main() -> int:
    main_exit_code_tests()

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

    # ---- RQ-76-CLOSUREMAIN: the PREVIOUS release's own closure wave -------
    #
    # Found by RUNNING the gate at the v0.76 cut, not by reading it. The ritual
    # closes issues AFTER the tag (the tag is the evidence the comment cites)
    # and `closed_since` opens its window AT the tag, so a release's own
    # closures land inside the NEXT release's window, where
    # `authorised_close_set(artifacts, version)` cannot see the artifact that
    # authorised them. MEASURED: v0.75.0's commit is 2026-09-25T06:52:31Z and
    # #1223/#1391 closed at 07:27:31Z/07:27:33Z, named by RQ-75-PINDEBT3 /
    # RQ-75-CLOSEWINDOW / RQ-75-PROBEINPUT. The gate said
    # `CLOSED BUT NOT AUTHORISED`, whose prescribed remedy is "Reopen it" —
    # the second time this file was one step from a wrong REOPENING.
    prev_ok = art("RQ-70-PREV", "implemented", "#700", version=(0, 70))
    f, w, _a, _h = run([delivered, prev_ok], closed=[100, 700])
    check("prior release's post-tag closure is ATTRIBUTED, not a failure",
          not f, str(f))
    check("...and the attribution names the release and the artifact",
          any("ATTRIBUTED TO v0.70: #700" in x and "RQ-70-PREV" in x
              for x in w), str(w))

    # LAUNDERING IS REFUSED. This is the half that could make the gate WEAKER:
    # a prior release that declared `issue-scope: outlives` said explicitly DO
    # NOT close this, and attribution must not convert that refusal into a
    # permission.
    prev_held = art("RQ-70-HELD", "implemented", "#701", version=(0, 70),
                    scope="outlives")
    f, _w, _a, _h = run([delivered, prev_held], closed=[100, 701])
    check("a PRIOR release's held-open issue closed in this window still FAILS",
          any("HELD OPEN BY v0.70 BUT CLOSED: #701" in x for x in f), str(f))
    check("...and the laundering path is NOT reported as attribution",
          not any("ATTRIBUTED" in x for x in f), str(f))

    # An issue NO release accounts for is still the v0.69 shape.
    f, _w, _a, _h = run([delivered, prev_ok], closed=[100, 999])
    check("an issue no release accounts for is still CLOSED BUT NOT AUTHORISED",
          any("CLOSED BUT NOT AUTHORISED: #999" in x for x in f), str(f))

    # Only releases STRICTLY BELOW the target attribute. A LATER release's
    # artifact must not retro-AUTHORISE a closure in this window.
    #
    # THE ASSERTION MOVED IN v0.81 AND THE PROPERTY DID NOT. (RQ-81-R11CONFLICT,
    # #1430.) It used to be written as "...therefore CLOSED BUT NOT AUTHORISED
    # fires", which conflated the property with one particular verdict. A later
    # release's artifact is now reported as an ATTRIBUTION WARNING instead,
    # because "Reopen it" was the wrong instruction — measured: auditing v0.78.0
    # emitted it for five issues that v0.79 and v0.80 had legitimately delivered
    # and closed. What this test is actually about is that the later artifact
    # must not land in the AUTHORISED map, and that is asserted directly now, on
    # `_a`, where no change to the message wording can make it vacuous.
    later = art("RQ-72-LATER", "implemented", "#702", version=(0, 72))
    f, w, a, _h = run([delivered, later], closed=[100, 702])
    check("a LATER release's artifact does not retro-AUTHORISE",
          702 not in a, f"authorised={a}")
    check("...and it is reported, as an attribution rather than a reopen order",
          any("ATTRIBUTED TO v0.72: #702" in x for x in w)
          and not any("#702" in x for x in f), f"warnings={w} failures={f}")

    # The mirror direction, same blindness one level in: an issue THIS release
    # held open that a LATER release went on to DELIVER is correctly closed.
    held_then_done = [art("RQ-71-HOLD", "implemented", "#703", (0, 71),
                          scope="outlives"),
                      art("RQ-72-DONE", "implemented", "#703", (0, 72))]
    f, w, _a, _h = run(held_then_done, closed=[], open_issues=[])
    check("held open here but DELIVERED later is not a reopen order",
          not any("#703" in x for x in f)
          and any("DELIVERED LATER: #703" in x for x in w),
          f"failures={f} warnings={w}")

    # CONTROL for that branch: with NO later delivery, the hold-open-but-closed
    # finding must still fire. This is the assertion that keeps the new branch
    # from being a blanket excuse.
    held_only = [art("RQ-71-HOLD", "implemented", "#703", (0, 71),
                     scope="outlives")]
    f, _w, _a, _h = run(held_only, closed=[], open_issues=[])
    check("CONTROL: held open and closed with NO later delivery still FAILS",
          any("HELD OPEN BUT ALREADY CLOSED: #703" in x for x in f), str(f))

    # ---- ANTI-VACUITY: the check must refuse to pass on an empty basis -----
    f, _w, _a, _h = run([], closed=[100])
    check("VACUOUS on zero artifacts", any("VACUOUS" in x for x in f), str(f))
    f, _w, _a, _h = run([art("RQ-71-N", "implemented", "")], closed=[100])
    check("VACUOUS when no artifact names an issue",
          any("VACUOUS" in x for x in f), str(f))

    # ---- RQ-80-CLOSEGATE (#1454): VACUITY MUST NOT SWALLOW THE PER-ISSUE
    # VERDICT. The vacuous branch used to RETURN before the closure loop, so a
    # release whose artifacts are ALL non-claiming lost every named instruction.
    # `prior_attribution` is built from EARLIER releases, so the "a prior release
    # held this open and someone closed it anyway" branch is fully derivable with
    # nothing authorised in THIS release. Measured on the live v0.80 tree before
    # the fix: closing #1318 — held open by v0.77, and an EXTERNAL reporter's
    # issue — produced no mention of #1318 and never said "Reopen it".
    held_prev = art("RQ-77-HELD", "implemented", "#1318", version=(0, 77),
                    scope="outlives")
    silent = art("RQ-80-SILENT", "proposed", "")      # names nothing: vacuous
    f, _w, a, h = run([held_prev, silent], closed=[1318])
    check("RQ-80-CLOSEGATE: the authorised set really is vacuous here",
          not a and not h, f"- authorised={a} held={h}")
    check("RQ-80-CLOSEGATE: vacuity is still REPORTED as a failure",
          any("VACUOUS" in x for x in f), str(f))
    check("RQ-80-CLOSEGATE: ...and the per-issue verdict SURVIVES it, by name",
          any("#1318" in x for x in f), str(f))
    check("RQ-80-CLOSEGATE: ...and still says to reopen it",
          any("Reopen it" in x for x in f), str(f))

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
    # (v0.81 round-1 cold review, finding 1.) This asserted that closing #1331
    # against v0.70's close-set is CAUGHT as a failure. On the REAL tree that is
    # no longer the right answer, and the measurement says so: v0.70 held #1331
    # open (RQ-70-NPA), v0.72 held it open again (RQ-72-ISLANDS), and v0.73,
    # v0.74 and v0.75 each AUTHORISED it (RQ-73-ISLANDPASS, RQ-74-ISLANDREACH,
    # RQ-75-FLOORBIND). `later_attribution(v0.70)[1331]` is
    # `((0, 75), "authorised", "RQ-75-FLOORBIND")`, the issue is closed today,
    # and that closure is correct — so "Reopen it" would be the wrong
    # instruction, which is this file's most expensive failure mode.
    #
    # THE LAUNDERING PROPERTY IS NOT WEAKENED, and it is tested separately above
    # with #701, an issue NO later release delivers: that case still FAILS. The
    # rescue fires only when a later release AUTHORISED the issue, which means a
    # later artifact delivered it under a claiming status. Hold open, continue,
    # deliver, close is a progression, not an override.
    f, w, _a, _h = C.check(root, "v0.70", V70_CLOSED | {1331})
    check("v0.70 replay: closing #1331 is NOT a reopen order — v0.75 delivered it",
          not any("HELD OPEN BUT CLOSED: #1331" in x for x in f), str(f))
    check("v0.70 replay: ...and it is reported, naming the release that delivered it",
          any("DELIVERED LATER: #1331" in x and "v0.75" in x for x in w), str(w))

    next_release_tag_tests()
    r11conflict_tests()
    closed_since_tests()

    print(f"issue-closure-tests: {FAILS} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
