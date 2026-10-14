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
reported a two-digit runner fragment repeatedly from runner names. NO COUNT IS
CLAIMED FOR THAT, and the two earlier attempts to claim one were both wrong. The
first said nineteen. The correction said "the record the sentence is about yields 2,
and no tracked file in this repository yields more than 8" — and round 2 refuted the
ceiling under EVERY scrubber configuration: `crates/synth-backend/src/arm_encoder.rs`
yields 23 (ordinary Rust, real ARM bit-field comments `| 01 |`) and a `.wat` fixture
yields 101. The sweep behind the 8 was silently restricted to `.py`/`.yaml`/`.md`,
so its population was not the repository — the standing obligation failed inside the
correction of a figure whose defect was that it was unreproducible. And because 23
and 101 both exceed nineteen, "nineteen is not reproducible" did not follow from that
ceiling either; the honest statement is that nineteen was not reproduced on the
record the sentence describes, which yields 2, and that no repository-wide ceiling
has been established. The scrubber is justified by the class EXISTING, which is
measurable here, and not by any count. Order matters — the longest,
most specific forms are removed first, or a shorter pattern eats part of a longer
token and leaves a digit behind.

WHAT IT WITHHOLDS, and why that is a SECOND SECTION rather than a wider regex.
The `version` scrubber necessarily eats a bare two-component decimal, because a
crate version looks exactly like a ratio. Measured over the six `v0.8*` records
present at the v0.86 cut, that class is not noise and not signal but MIXED, and
reading the matches in context settles which is which: quantities `16.3` (a
`cargo check` duration in seconds), `99.1` and `0.7` (percentages of a job
census), `3.6` (GiB free) and `11.74` (a 364/31 ratio) against versions `1.252`
and `259.0` (crate deps), `27.0` (macOS), `0.69` (npm), plus `4.1` (a section
number) and `0.0` (an IEEE literal quoted in prose about `-0.0 == 0.0`). No
pattern separates a ratio from a crate version, so widening the scrubber trades
one error for the other. `11.74` is the case that forces the issue: v0.85's round
1 wrote "twelve", rounded up FROM that ratio, and the tool whose whole job is to
queue round 1's numbers for attack could not see the number the word came from.
A false positive costs round 2 one glance; a false negative means an unreviewed
figure is never reviewed, which is the defect this file exists to prevent. So the
withheld decimals are PRINTED, in their own labelled bucket, triaged by hand ---
nothing hidden and nothing asserted. An EMPTY bucket is a legitimate observation
here rather than a refusal, and that is measured too: two of the six records
carry no bare decimal at all.

WHAT WAS REFUTED, recorded so it is not re-attempted. The `sha` scrubber also
removes all-digit runs, which raised the same worry one class over: an uncommaed
seven-digit byte count would be eaten as a sha. Every all-digit token the
scrubber removes across those six records is an IDENTIFIER --- GitHub run and
comment ids, and two genuine all-digit eight-character git shas (`67217468`,
`00462031`). Requiring a hex letter, the obvious narrowing, would have leaked
those two real shas into the queue as quantities. The blind spot is real and has
no observed instance; v0.85's round-2 repair of this scrubber stands.

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


# A bare two-component decimal: no leading word character (so `v0.85` and the
# `85.0` inside it are both excluded) and no trailing digit or dot (so `0.85.0`
# and the layer string `2026.10.9` are excluded). What is left is the shape that
# a ratio, a duration, a percentage and a two-component crate version all share.
WITHHELD_DECIMAL = r"(?<![\w.])\d+\.\d+(?![\d.])"


def withheld_decimals(text: str) -> collections.Counter:
    """The bare two-component decimals `version` removes, for HAND triage.

    Not a claim that these are quantities --- a claim that the pipeline cannot
    tell, which is why they are reported separately instead of being dropped.
    """
    return collections.Counter(re.findall(WITHHELD_DECIMAL, text))


def scrub(text: str) -> str:
    for _name, pat in SCRUBBERS:
        text = re.sub(pat, " ", text)
    return text


def numbers(text: str) -> collections.Counter:
    return collections.Counter(re.findall(r"\b\d[\d,]*\b", scrub(text)))


def numbers_with(scrubbers, text: str) -> collections.Counter:
    """`numbers()` under an ARBITRARY scrubber list — the leave-one-out primitive."""
    for _name, pat in scrubbers:
        text = re.sub(pat, " ", text)
    return collections.Counter(re.findall(r"\b\d[\d,]*\b", text))


def self_test() -> int:
    r"""Each sample must be scrubbed, NO sample may be vacuous, and the per-scrubber
    claim is DERIVED by leave-one-out rather than asserted.

    ROUND 2 OF v0.85 FOUND THREE DEFECTS HERE, and the structure below is the repair:
      * the `sha` sample yielded nothing even with ZERO scrubbers, so `ok sha fully
        scrubbed` was a vacuous assertion inside a self-test and could never fail.
        Hex shas have letters beside their digits, so `\b\d[\d,]*\b` cannot reach
        them — an ALL-DIGIT sha is needed to make the case discriminating.
      * leave-one-out showed only 7 of 9 scrubbers were individually proven; the
        printed line claimed all of them. The count is now derived and labelled.
      * the by-construction sample contained `VCR-SEL-005`, which the `artifact-id`
        SCRUBBER removes — so dropping that scrubber leaked `005` and the failure was
        reported under the BY-CONSTRUCTION label, a misattributed diagnosis.
    """
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
        # An ALL-DIGIT sha: a mixed hex sha yields no bare number even unscrubbed,
        # which is what made this case vacuous before v0.85's round 2.
        ("sha", "declared 1234567890abcdef and 9876543"),
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
    # `VCR-SEL-005` was removed from this sample in v0.85: the `artifact-id`
    # SCRUBBER strips it, so it was never a by-construction case, and dropping that
    # scrubber leaked `005` under this label — a misattributed diagnosis, found by
    # round 2. Both survivors have no word boundary before their digits.
    embedded = numbers("R11-active and x11y")
    if embedded:
        failures.append(f"BY-CONSTRUCTION: identifier digits leaked: {dict(embedded)}")
    else:
        print("  ok  by-construction  identifier-embedded digits are unreachable")

    # VACUITY GUARD: a sample that yields nothing with ZERO scrubbers proves nothing.
    for label, sample in cases:
        if not numbers_with([], sample):
            failures.append(
                f"VACUOUS CASE {label}: the sample yields no number even with NO "
                f"scrubbers, so 'fully scrubbed' cannot fail — fix the sample")

    # LEAVE-ONE-OUT: derive which scrubbers are INDIVIDUALLY necessary. Overlap is
    # legitimate (a date is also caught by the clock pattern); claiming coverage the
    # pipeline does not individually owe is not.
    necessary = []
    for name, _pat in SCRUBBERS:
        others = [(n, p) for n, p in SCRUBBERS if n != name]
        if any(numbers_with(others, s) for _l, s in cases):
            necessary.append(name)
    redundant = [n for n, _ in SCRUBBERS if n not in necessary]
    print(f"  ok  leave-one-out   {len(necessary)} of {len(SCRUBBERS)} scrubbers are "
          f"individually necessary; {len(redundant)} covered redundantly: {redundant}")

    # WITHHELD-DECIMAL BUCKET, asserted as a PAIRED control. The positive half
    # proves the bucket surfaces a real quantity the `version` scrubber eats; the
    # negative half proves the bucket is not merely "every dotted token", which
    # is the shape a well-meaning widening would have produced. Either half alone
    # proves little: without the positive case the bucket may be inert, and
    # without the negative one its hits may be coming from the environment rather
    # than from the property.
    w_pos = withheld_decimals("fitted in 552 MB / 16.3 s and the 364/31 ratio is 11.74")
    if sorted(w_pos) != ["11.74", "16.3"]:
        failures.append(f"WITHHELD positive: expected the two quantities, got {dict(w_pos)}")
    else:
        print(f"  ok  withheld-pos   decimal quantities surface for triage: {sorted(w_pos)}")

    w_neg = withheld_decimals("v0.85.0 and 0.85.0 on layer 2026.10.9 at v0.69")
    if w_neg:
        failures.append(f"WITHHELD negative: version strings leaked into the bucket: {dict(w_neg)}")
    else:
        print("  ok  withheld-neg   v-prefixed and 3+-component versions do NOT")

    # VACUITY GUARD for the bucket: the positive sample must carry a decimal at
    # all, or `sorted(w_pos) != [...]` would be asserting about an empty string.
    if not re.search(r"\d+\.\d+", "fitted in 552 MB / 16.3 s and the 364/31 ratio is 11.74"):
        failures.append("VACUOUS withheld positive: the sample carries no decimal")

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
    print(f"self-test: {len(SCRUBBERS)} scrubbers over {len(cases)} cases, "
          f"{len(necessary)} individually necessary by leave-one-out, "
          f"+ positive control + by-construction + vacuity guard "
          f"+ withheld-decimal paired control, 0 failures")
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
    held = withheld_decimals(p.read_text())
    print(f"\nWITHHELD by the `version` scrubber --- {len(held)} bare two-component "
          f"decimal(s), MIXED class, triage by hand (a ratio and a crate version "
          f"share this shape; zero here is legitimate, not a refusal):")
    if not held:
        print("  (none)")
    for val, n in sorted(held.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:>4}x  {val}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
