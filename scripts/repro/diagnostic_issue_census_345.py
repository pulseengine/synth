#!/usr/bin/env python3
# ci-status: manual (measurement) — a CENSUS with no verdict about the compiler.
# RQ-74-STALEMSG (#345) set out to build a tripwire refusing a diagnostic that
# cites a CLOSED issue, and this census REFUTED that plan before it was built:
# 93% of the citations point at closed issues, so the refusal would red 363
# sites and be routed around within a release. The artifact's own "what would
# make this wrong" named exactly this outcome. What ships instead is this
# script plus the convention recorded in CLAUDE.md. There is nothing here for
# CI to fail on, which is why it is `manual` and not `wired`.
"""RQ-74-STALEMSG (#345): what does an issue number in a diagnostic MEAN?

WHY THIS WAS ASKED. v0.73 cost real time twice to one diagnostic:

    LdrSym literal pool out of range (#345): imm12={} > 4095 for symbol ...

#345 has been CLOSED since 2026-06-14, verified on real G474RE silicon — its
asks were a bounded `.data` and no absolute MOVW relocs, delivered in v0.11.43.
The message reuses the number for an unrelated function-size limit. An external
reporter asked "is #345 already tracked for large functions, or should this be
filed separately?", and the v0.73 coordinator read that issue's BODY without its
STATE and nearly held a closed issue open.

The obvious fix was a tripwire. The census says no.

WHAT IT MEASURES. Every `#N` inside a string literal in `crates/**/*.rs`,
excluding `tests/` and everything from each file's first `#[cfg(test)]` — a test
assertion is not a user-facing diagnostic — and excluding `#N` preceded by `,`
or `[`, which is ARM immediate syntax (`AND R12,#31`, `ldr r0,[ip,#4095]`) and
not an issue reference at all. Both exclusions were added AFTER a first pass
reported 663 sites whose "not an issue" bucket was dominated by those two
shapes: the denominator was contaminated and the headline was computed off it.

WHICH EXCLUSION ACTUALLY DID THE WORK, measured in round 1 of the v0.74 cold
review, because the sentence above invites the wrong inference: the
`#[cfg(test)]` cut removes 264 of the 274 sites (663 -> 653 -> 389). The ARM
immediate lookbehind removes 10, and ALL TEN fall inside the region the test cut
already discards — so on the shipped population it excludes ZERO sites and is
inert. It is kept because it is correct, not because it is load-bearing.

AND THE TEST CUT OVER-EXCLUDES. `txt.find("#[cfg(test)]")` is a marker-to-EOF
scan: in `crates/synth-synthesis/src/instruction_selector.rs` the FIRST marker is
at line 308 on a single test-only helper, while `mod tests` is at line 9205, so
the census discards lines 308-19797 of that file. A brace-balanced cut recovers
+54 sites (389 -> 443), all in that one file. The stated population is therefore
short by 54 sites and 4 numbers. The CONCLUSION survives every alternative the
reviewer tried — 93%, 93%, 93%, 94% across {marker cut, brace cut} x {all string
literals, diagnostic position}, and 90% counted by distinct numbers rather than
sites — which is why the verdict stands and only the population is corrected.

MEASURED at the v0.74 cut (RE-RUN IT — and note these figures are restated by
hand in CLAUDE.md, ORACLE_WIRING.md, claims.yaml's manual-ceiling comment and
RQ-74-STALEMSG, so `claim_check` does not bind them and re-running here does
not update those copies):

    117 numbers, 389 sites
      OPEN issue    9 numbers,  21 sites
      CLOSED issue 105 numbers, 363 sites   <- 93% of sites
      not an issue  3 numbers,   5 sites    (31, 32, 46 — residual immediates)

WHAT THAT MEANS, and it is the finding. Citing a CLOSED issue is not an anomaly
in this codebase; it is the CONVENTION, at 93%. The number records WHERE THE
LIMITATION WAS ANALYSED — the issue that has the measurement, the repro and the
decision — and that issue is normally closed precisely BECAUSE the analysis
finished. #345 is not a broken citation. It is a correctly-formed one that a
reader reasonably misread as "open and tracked".

So the defect is not the citations. It is that nothing ever said what they mean.
That is a documentation fix, recorded in CLAUDE.md, not a gate.

WHY NO TRIPWIRE SHIPS. A rule refusing closed-issue citations would red 363
sites on the day it landed. A gate people cannot move honestly is a gate they
route around — this repository has written that down and then had to learn it
again twice. The honest output is the measurement plus the convention.

WHAT WOULD CHANGE THIS VERDICT. If the share inverted — if most citations
pointed at OPEN issues — then a closed-issue citation would be the exception and
a tripwire could name it. Re-run this census before assuming that has happened.

DELIBERATELY NOT DONE: re-pointing or rewording the #345 message. Exactly ONE
oracle pins the CITATION: `litpool_islands_345.py`'s `REFUSAL` regex, which
spells out `\(#345\)` and matches on the islands-OFF leg every CI round.
Mutating `#345` to `#999` in `arm_backend.rs` reds that one and nothing else.

TWO EARLIER DRAFTS OF THIS PARAGRAPH WERE WRONG, and both are recorded because
the correction is where the next false statement goes. The first named
`islandpass_1331_execution_differential.py`'s `PINNED_REFUSAL` alone — but that
constant sits in the STATE-1 branch, reached only when a fixture fails to
compile, which the fixed point's own success prevents. The second said "three
places", counting `litpool_islands_345_differential.py` — whose `REFUSAL` is the
PREFIX only (`"LdrSym literal pool out of range"`, no number), so it does not
pin the citation at all.

The conclusion is unchanged and now rests on the one pin that exists: changing
user-facing text an oracle matches is a separate, gated change, not something to
do inside a census lane.
"""
import collections
import json
import pathlib
import re
import subprocess
import sys

STR = re.compile(r'"([^"\\]*(?:\\.[^"\\]*)*)"', re.S)
# NOT preceded by `,` or `[` — that shape is an ARM immediate, not an issue ref.
ISSUE = re.compile(r'(?<![,\[])#(\d{2,5})\b')
ROOT = pathlib.Path(__file__).resolve().parents[2]


def citations() -> dict[int, list[str]]:
    hits: dict[int, list[str]] = collections.defaultdict(list)
    for p in sorted((ROOT / "crates").rglob("*.rs")):
        if "/tests/" in str(p) or p.name.startswith("test"):
            continue
        txt = p.read_text(errors="ignore")
        cut = txt.find("#[cfg(test)]")
        body = txt[:cut] if cut != -1 else txt
        for m in STR.finditer(body):
            for n in ISSUE.findall(m.group(1)):
                line = body[: m.start()].count("\n") + 1
                hits[int(n)].append(f"{p.relative_to(ROOT)}:{line}")
    return hits


def issue_states() -> dict[int, str]:
    try:
        out = subprocess.run(
            ["gh", "issue", "list", "--repo", "pulseengine/synth", "--state", "all",
             "--limit", "2000", "--json", "number,state"],
            capture_output=True, text=True)
    except FileNotFoundError:
        # `gh` absent is the SAME condition as `gh` failing, and it must produce
        # the same refusal rather than a traceback: an unreadable board is never
        # a clean one. Without this the script died before the returncode check.
        raise SystemExit(
            "REFUSE: `gh` is not available — could not read the issue board. "
            "An unreadable board is not an empty one.") from None
    if out.returncode != 0:
        raise SystemExit(
            "REFUSE: could not read the issue board — an unreadable board is "
            "not an empty one, and a census over a board it could not read "
            "would report every citation as 'not an issue'.")
    return {i["number"]: i["state"] for i in json.loads(out.stdout)}


def main() -> int:
    hits = citations()
    states = issue_states()
    tot = sum(len(v) for v in hits.values())
    if tot == 0:
        raise SystemExit("REFUSE: zero citations found — the scan matched "
                         "nothing, which is a broken scan, not a clean tree.")
    closed = {n: v for n, v in hits.items() if states.get(n) == "CLOSED"}
    openi = {n: v for n, v in hits.items() if states.get(n) == "OPEN"}
    unknown = {n: v for n, v in hits.items() if n not in states}
    cs = sum(len(v) for v in closed.values())
    print(f"diagnostic-issue-census: {len(hits)} numbers, {tot} sites")
    print(f"  OPEN issue   : {len(openi):3d} numbers, {sum(len(v) for v in openi.values()):3d} sites")
    print(f"  CLOSED issue : {len(closed):3d} numbers, {cs:3d} sites  ({100 * cs // tot}% of sites)")
    print(f"  not an issue : {len(unknown):3d} numbers, {sum(len(v) for v in unknown.values()):3d} sites"
          f"  {sorted(unknown, key=int)}")
    print()
    print("Most-cited CLOSED issues (the population a tripwire would have red):")
    for n, v in sorted(closed.items(), key=lambda kv: -len(kv[1]))[:10]:
        print(f"  #{n:<5} {len(v):3d} site(s)")
    print()
    print("VERDICT: none. This is a measurement, not a gate — see the module "
          "docstring for why no tripwire ships.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
