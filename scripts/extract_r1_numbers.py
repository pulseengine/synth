#!/usr/bin/env python3
"""Extract the NUMBERS a cold-review record introduces, frequency-ordered.

WHY THIS IS A TRACKED SCRIPT. v0.84's review record cites
`extract_r1_numbers.py` as the method by which round 2's queue was derived, and
says in its own residue note that the file was "the tool copied in for me" —
untracked. (An earlier version of this paragraph said v0.83's record cited it
too; it does not — it mentions the name once, in a list of untracked paths, and
its round 2 worked from round 1's own "what round 2 should attack" section.
Corrected after this release's round 1 found the same error at two other sites,
which is why it is fixed here as a FACT rather than at the site that was flagged.)
It was in no commit on any branch until this one: the commit that adds this file
is the repair, so the sentence above is in the past tense on purpose. So ONE
shipped record names a method a reader cannot run: the same defect
RQ-85-PROVENANCE measured for commit citations, one token class over. A record's
method must be as checkable as its figures.

WHAT IT IS FOR. "A correction is an unreviewed claim": the numbers a round-1
correction introduces have had zero review passes. Round 2 attacks them BY NAME,
and the queue must come from the text rather than from reading for importance —
reading for importance is how the loop re-reviews what it already believes.

WHAT IT SCRUBS, and why each class is noise rather than a claim: identifiers
carry digits that are not quantities. v0.84's record notes its own run left ISO
fragments (`09`, `57`, `26`, `58`, `51`, `53`) in the list, and an unscrubbed run
reported a two-digit runner fragment repeatedly from runner names. THE FIGURE THIS
DOCSTRING FIRST CARRIED FOR THAT — nineteen — IS NOT REPRODUCIBLE and was corrected
here: the record the sentence is about yields 2, and no tracked file in this
repository yields more than 8. The scrubber is justified by the class existing,
which is measurable, not by that count. Order matters — the longest,
most specific forms are removed first, or a shorter pattern eats part of a longer
token and leaves a digit behind.

Run:
  python3 scripts/extract_r1_numbers.py docs/reviews/v0.85-cold-review.md
  python3 scripts/extract_r1_numbers.py --self-test
"""
import collections
import pathlib
import re
import sys

# ORDER IS LOAD-BEARING: longest/most-specific first.
SCRUBBERS: list[tuple[str, str]] = [
    # ISO timestamps, full form, with or without a trailing Z/offset
    ("iso-datetime", r"\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}(?::\d{2})?(?:Z|[+-]\d{2}:?\d{2})?"),
    # ISO dates alone
    ("iso-date", r"\d{4}-\d{2}-\d{2}"),
    # BARE CLOCK TIMES, date-less, with or without seconds and with or without
    # a trailing Z. MEASURED against the v0.84 record rather than assumed: the
    # form it actually carries is `started_at=09:51:39Z`, which a seconds-less
    # `\d{1,2}:\d{2}Z` pattern misses and a date-anchored ISO pattern also
    # misses, so the whole class leaked and produced the `09`/`51`/`57`/`58`
    # fragments that record complains about in its own text. Seconds are
    # optional and Z is optional, in that order, or the `:\d{2}` tail survives.
    ("bare-clock", r"\b\d{1,2}:\d{2}(?::\d{2})?Z?\b"),
    # artifact ids: RQ-85-FALCON2, BR-001
    ("artifact-id", r"\b(?:RQ|BR|LS|VCR|GI)-[0-9A-Za-z-]+"),
    # runner names: ci-01-8, pulseengine-ci-01-10
    ("runner", r"\b(?:[a-z]+-)*ci-\d+-\d+\b"),
    # file:line citations: foo.rs:118, CHANGELOG.md:10
    ("file-line", r"\b[\w./-]+\.[A-Za-z]{1,6}:\d+\b"),
    # version and layer strings: v0.85.0, 0.85.0, 2026.10.9
    ("version", r"\bv?\d+\.\d+(?:\.\d+)*\b"),
    # issue/PR refs
    ("ref", r"#\d+\b"),
    # bare shas (7-40 hex) — AFTER the above so it cannot eat a version
    ("sha", r"\b[0-9a-f]{7,40}\b"),
]


def scrub(text: str) -> str:
    for _name, pat in SCRUBBERS:
        text = re.sub(pat, " ", text)
    return text


def numbers(text: str) -> collections.Counter:
    return collections.Counter(re.findall(r"\b\d[\d,]*\b", scrub(text)))


def self_test() -> int:
    """Each scrubber must remove its OWN class, and a real claim must SURVIVE."""
    cases = [
        ("iso-datetime", "settled at 2026-10-13T17:42:09Z with"),
        ("iso-date", "measured 2026-10-09 and"),
        ("bare-clock-hhmmz", "settled at 17:42Z with"),
        ("bare-clock-hhmmssz", "started_at=09:51:39Z != completed_at=09:57:58Z"),
        ("bare-clock-naked", "between 09:51 and 09:57 it ran"),
        ("artifact-id", "RQ-85-FALCON2 and BR-001 say"),
        ("runner", "ran on pulseengine-ci-01-10 and ci-01-8"),
        ("file-line", "ARCHMODEL3.yaml:16 says exactly that"),
        ("version", "the layer 2026.10.9 pin at v0.85.0 and 0.84.0"),
        ("ref", "see #1318 and #1520"),
        ("sha", "declared 5a4092dac4bb68aa68acb9572475a4f268191e2a and b0395b69"),
    ]
    failures = []
    for name, sample in cases:
        left = numbers(sample)
        if left:
            failures.append(f"{name}: left {dict(left)} behind in {sample!r}")
        else:
            print(f"  ok  {name:<13} fully scrubbed")

    # POSITIVE CONTROL: the tool must not be a scrubber that eats everything.
    claim = "blocked lands green on 294 of the 594, and 177 files are R11-active"
    got = numbers(claim)
    want = {"294": 1, "594": 1, "177": 1}
    if got != collections.Counter(want):
        failures.append(f"POSITIVE CONTROL: claim numbers are {dict(got)}, expected {want}")
    else:
        print(f"  ok  positive-ctl  real claim numbers survive: {sorted(got)}")

    # A SECOND, DIFFERENT MECHANISM, asserted separately because conflating it
    # with the scrubbers would be the population error this programme keeps
    # finding. An identifier-embedded digit (`R11`, `x11y`) is not excluded by
    # any pattern above — it is unreachable BY CONSTRUCTION, because `\b` needs a
    # non-word character and `R`/`1` are both word characters. Written as its own
    # case so that a future edit to the extraction regex cannot silently start
    # counting rule numbers as quantities. (The authoring run of this file got
    # this wrong first: the control expected `11` from `R11-active`, the
    # self-test refused, and the EXPECTATION was what was wrong.)
    embedded = numbers("R11-active and x11y and VCR-SEL-005")
    if embedded:
        failures.append(f"BY-CONSTRUCTION: identifier digits leaked: {dict(embedded)}")
    else:
        print("  ok  by-construction  identifier-embedded digits are unreachable")

    # A derived population of zero is a refusal, not a pass.
    if not cases:
        failures.append("REFUSE: empty self-test population")

    if failures:
        for f in failures:
            print(f"  FAIL {f}")
        print(f"self-test: {len(failures)} failure(s)")
        return 1
    # `len(cases)` is NOT the scrubber count: bare-clock carries three cases. The
    # shipped line said "11 scrubbers" against 9, found by this release's round 1.
    print(f"self-test: {len(SCRUBBERS)} scrubbers over {len(cases)} cases "
          f"+ 2 mechanism checks, 0 failures")
    return 0


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__)
        return 2
    if argv[1] == "--self-test":
        return self_test()
    p = pathlib.Path(argv[1])
    if not p.exists():
        sys.exit(f"REFUSE: {p} does not exist")
    counts = numbers(p.read_text())
    if not counts:
        sys.exit(f"REFUSE: {p} yielded ZERO numbers after scrubbing — a derived "
                 f"population of zero is a refusal, not a pass; check the scrubbers")
    print(f"{p}: {len(counts)} distinct number(s), frequency-ordered")
    for val, n in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:>4}x  {val}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
