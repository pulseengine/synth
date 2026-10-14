#!/usr/bin/env python3
"""RQ-86-SPELLSCAN (#1515) — a release file's statistics, in BOTH spellings.

WHY THIS EXISTS. A release file is comments-only by rule and must carry no
STATISTICS: a figure parked there is a second copy of a measured number, and a
second copy is how a number goes stale (#1286). Until this script the check was
an ad-hoc `grep -nE '[0-9]'` typed into a commit message, and it was BLIND BY
SPELLING.

MEASURED, which is why the blindness is not hypothetical. v0.85's `_release.yaml`
carried a figure its own round-1 review had already proven false, spelled as a
WORD. Across the whole window:

    commit                   "nineteen"   digit-scan survivors
    planning                      1                 0
    release prep                  1                 0
    cold review round 1           1                 0
    cold review round 2           0                 0

Three commits where the figure was LIVE and the digit scan read CLEAN at every
one of them -- and the commit that fixed the figure's twin elsewhere reported the
file "re-verified free of statistics", truthfully, by a scan that could not see
it. A census is bounded by its pattern's spellings.

THIS IS NOT AN ORACLE, AND SAYING SO IS THE POINT. `--all` over every release
file in the tree returns 300 word-number hits across 24 files and 234 digit hits
across 20, of a population of 26 release directories, 25 of which carry a
`_release.yaml` -- and the overwhelming majority of the word hits are IDIOMS
("every one of", "including this one", "the one-line key append"), not
statistics. An earlier version of this docstring said the word scan returns 560
across 29 of 30 files while the digit scan returns ZERO; NEITHER figure
reproduces, and neither could be checked, because until round two there was no
tree-wide mode to derive them from -- `release_file` returns ONE path. Two of
the four idioms this paragraph used to cite ("fired twice", "a single lane")
were not idioms: cold review showed both were unsourced counts of a shipped
release's outcomes, and they have been removed from the file rather than
reworded, which is what the report's own instruction demands. A
gate that red on a token match would be refused on day one and routed around,
which is the RQ-74-STALEMSG trap. So this REPORTS the population and the
operator RECORDS the judgement; it does not pretend a token match is a statistic.

Usage:
    python3 scripts/release_file_statistics_scan.py                # newest release
    python3 scripts/release_file_statistics_scan.py --release v0.86
    python3 scripts/release_file_statistics_scan.py --self-test
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Numbers spelled as words. Deliberately WIDE: the cost of a wide net here is a
# line the operator classifies, and the cost of a narrow one is a false figure
# shipped in a release record.
WORD_NUMBERS = (
    r"\b(one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|"
    r"thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|"
    r"thirty|forty|fifty|sixty|seventy|eighty|ninety|hundred|thousand|dozen|"
    r"half|twice|single|double|triple)\b"
)

# Version strings and issue references are NOT statistics -- they are
# identifiers. Two-component `v0.86` is included because omitting it was a real
# false positive while this script was being written: the stripper matched only
# `0.X.Y`, so the file's own title line `# v0.85 release scope` read as a digit
# survivor.
IDENTIFIERS = re.compile(r"v?\d+\.\d+(\.\d+)?|#\d+")


def scan(text: str) -> tuple[list[tuple[int, str]], list[tuple[int, str]]]:
    """(digit hits, word hits) as (line number, line)."""
    digits: list[tuple[int, str]] = []
    words: list[tuple[int, str]] = []
    for i, line in enumerate(text.split("\n"), 1):
        if re.search(r"\d", IDENTIFIERS.sub("", line)):
            digits.append((i, line.strip()))
        if re.search(WORD_NUMBERS, line, re.I):
            words.append((i, line.strip()))
    return digits, words


def matched_words(line: str) -> list[str]:
    """The word-numbers this scan actually MATCHED, lowercased.

    Exists because a self-test case that asserted on the LINE passed for the
    wrong reason: the probe line "...a two-digit runner fragment ... nineteen
    times" contains BOTH `two` and `nineteen`, so dropping `nineteen` from the
    pattern left the case green -- it was still finding one match and the word
    was still present in the text it was inspecting. A case must assert on what
    the instrument matched, not on what the input happens to contain.
    """
    return [m.group(0).lower() for m in re.finditer(WORD_NUMBERS, line, re.I)]


def release_file(release: str | None) -> Path:
    d = REPO_ROOT / "artifacts"
    dirs = sorted(p for p in d.glob("release-v0.*") if p.is_dir())
    if release:
        p = d / f"release-{release}" / "_release.yaml"
        if not p.exists():
            sys.exit(f"FAIL: {p} does not exist")
        return p
    if not dirs:
        sys.exit("FAIL: no release directories under artifacts/ — refusing to scan nothing")
    return dirs[-1] / "_release.yaml"


def population() -> tuple[list[Path], list[Path]]:
    """(release dirs, those carrying a `_release.yaml`) — the DENOMINATOR, derived.

    RQ-86-SPELLSCAN round two (#1515). Every tree-wide figure this lane ever
    reported came from an ad-hoc loop that was never committed, so none of them
    could be re-derived and three different ones circulated: the artifact said
    the digit half returns zero in all thirty files, cold review re-measured
    1162 across 25, and a loop over the files that actually exist gives a third
    answer again. The scan could not settle it because `release_file` returns
    ONE path and there was no tree-wide mode at all. A figure whose population
    is not part of the output is not a measurement.
    """
    d = REPO_ROOT / "artifacts"
    dirs = sorted(p for p in d.glob("release-v0.*") if p.is_dir())
    return dirs, [p for p in dirs if (p / "_release.yaml").exists()]


def report_all() -> int:
    """Scan EVERY release file, and state the population it was taken over."""
    dirs, files = population()
    if not files:
        # The single-file path already refuses an empty population; this one
        # must too, or `--all` reports a clean ZERO over nothing scanned --
        # which is exactly the blindness this lane exists to report.
        print("FAIL: no release file found under artifacts/ — refusing to "
              "report a figure over an empty population")
        return 1
    td = tw = nd = nw = both = 0
    for p in files:
        digits, words = scan((p / "_release.yaml").read_text())
        td += len(digits); tw += len(words)
        nd += bool(digits); nw += bool(words); both += bool(digits and words)
        print(f"  {p.name:16s} {len(digits):5d} digit  {len(words):5d} word")
    without = [q.name.replace("release-", "") for q in dirs if q not in files]
    print("")
    print(f"statistics-scan --all: POPULATION {len(dirs)} release directories, "
          f"{len(files)} carrying a `_release.yaml`"
          + (f" ({', '.join(without)} without one)" if without else ""))
    print(f"statistics-scan --all: {td} digit hit(s) across {nd} file(s); "
          f"{tw} word-number hit(s) across {nw}; both non-zero in {both}")
    return 0


def report(path: Path) -> int:
    text = path.read_text()
    digits, words = scan(text)
    print(f"statistics-scan: {path.relative_to(REPO_ROOT)} — "
          f"{len(digits)} digit hit(s), {len(words)} word-number hit(s)")
    for label, hits in (("DIGIT", digits), ("WORD", words)):
        for i, line in hits:
            print(f"  {label:5s} {i:4d}: {line[:150]}")
    if digits or words:
        print("\nJUDGEMENT REQUIRED — classify each line above as an IDIOM or a "
              "STATISTIC, and record that judgement in the release PR. A "
              "statistic must be REMOVED, not reworded: the release file is "
              "comments-only and a figure here is a second copy of a measured "
              "number. This scan does NOT decide for you; a token match is not "
              "a statistic.")
    return 0


def self_test() -> int:
    """POSITIVE CONTROL plus an inert control, because either alone proves little.

    The red case is the real figure at the real commit: the word scan must see
    `nineteen` in a line the digit scan is blind to. The inert case is that same
    line with the figure removed, where the word scan must still fire on the
    surrounding IDIOM -- which is what establishes that this is a reporting
    scan and not an oracle.
    """
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    live = "# reported a two-digit runner fragment as a finding nineteen times."
    d, w = scan(live)
    hits = matched_words(live)
    # Asserted on the MATCHED TOKENS. The first version of this case checked
    # `"nineteen" in w[0][1]` -- the LINE -- and stayed green when `nineteen`
    # was removed from the pattern, because this very line also contains `two`
    # in "two-digit" and the word was still in the text being inspected. A
    # negative control on this file's own self-test is what found that.
    ok("nineteen" in hits, "the live figure is MATCHED by the word scan")
    ok(len(w) == 1, "and the line is reported once")
    ok(len(d) == 0, "and is INVISIBLE to the digit scan — the blindness, reproduced")

    fixed = "# reported a runner fragment as a finding, a count not reproduced."
    d2, w2 = scan(fixed)
    ok(len(w2) == 0, "with the figure removed the word scan finds nothing here")

    idiom = "# AND THE POPULATION IS PART OF THE CLAIM. It fired twice inside a single run."
    d3, w3 = scan(idiom)
    ok(len(w3) == 1, "an IDIOM still fires — so this reports, it does not adjudicate")

    # The tree-wide mode, added in round two because every tree-wide figure
    # this lane reported came from an uncommitted loop. Its POPULATION must be
    # derived and non-empty, and it must REFUSE rather than report a clean
    # zero over nothing -- the vacuity the single-file path already refuses.
    dirs, files = population()
    ok(len(dirs) > 0 and len(files) > 0,
       "the tree-wide population is DERIVED and non-empty")
    ok(set(files) <= set(dirs),
       "every file counted sits in a directory that was counted")
    import contextlib, io, unittest.mock as _m
    with _m.patch(f"{__name__}.population", lambda: ([], [])):
        with contextlib.redirect_stdout(io.StringIO()):
            rc_empty = report_all()
    ok(rc_empty == 1, "--all REFUSES an empty population instead of reporting zero")
    ok(len(d3) == 0, "and carries no digit")

    ok(scan("# v0.85 release scope — COMMENTS ONLY.")[0] == [],
       "a two-component version is an identifier, not a digit survivor")
    ok(scan("# refs #1515 and v0.86.0")[0] == [],
       "issue refs and three-component versions are identifiers too")
    ok(scan("# 19 findings")[0] != [], "a bare digit IS a survivor")

    print(f"statistics-scan-self-test: {fails} failure(s)")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--release", help="release id, e.g. v0.86 (default: newest)")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--all", action="store_true",
                    help="scan every release file and state the population")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    if a.all:
        return report_all()
    return report(release_file(a.release))


if __name__ == "__main__":
    sys.exit(main())
