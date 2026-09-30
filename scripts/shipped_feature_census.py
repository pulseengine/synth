#!/usr/bin/env python3
# ci-status: wired — `--self-test` runs in the required `claim-check` job. The
# census itself prints a DERIVED list and asserts nothing about the compiler's
# output, so there is no expected value for CI to fail on beyond the self-test.
"""Which capabilities does the SHIPPED binary actually have? (#1437)

THE QUESTION, asked by the maintainer: "you need to be sure that the binary we
deliver is our full feature set — hiding behind features and other things".

A capability reachable only when an environment variable is set is NOT in the
delivered binary's behaviour. `synth compile` with no environment does not run
it. So "what does it compile, and what does that code cost" has an answer that
depends on flags nobody sets in production, and until this script existed the
only way to know which ones was to read 128 source files.

WHY THIS IS DERIVED AND NOT A LIST IN PROSE. A hand-written list of hand-written
flags is itself a hand-written table — the RQ-77-CENSUS lesson. This walks the
sources and evaluates each read.

TWO AXES, because the maintainer's word "features" names both mechanisms and a
census of one would read as the whole answer:

  AXIS 1  runtime `SYNTH_*` env reads. Derived from the sources.
  AXIS 2  CARGO features, which no census of runtime reads can see. TWO DIFFERENT
          BINARIES ARE DELIVERED and they do not carry the same set:
          `release.yml` builds `-p synth-cli --features verify`, while
          `cargo install synth-cli` takes `default = ["riscv"]` only — so `synth
          verify` is NOT compiled into the crates.io binary. It loud-declines,
          which is correct behaviour, but the two published artifacts answer
          differently and nothing recorded that.

STILL UNCENSUSED, named here rather than left to read as absent: the four
library-only crates that link into no binary at all (#1277 — `synth-analysis`,
`synth-abi`, `synth-memory`, `synth-wit`), and `--features z3-solver` on
`synth-verify`, which is a differential oracle rather than shipped capability.

=============================================================================
THE TRAP, WHICH COST THREE WRONG COUNTS BEFORE THIS FILE EXISTED
=============================================================================

**THE POLARITY OF THE BOOLEAN IS NOT THE POLARITY OF THE FEATURE.** The first
hand census matched `is_ok_and` as a substring and reported FIFTEEN capabilities
shipping off. The second evaluated the boolean correctly and still reported NINE,
because it read the boolean's polarity as the feature's. Two live sites in
`arm_backend.rs` show why that cannot work — their booleans are OPPOSITE and
their feature polarity is IDENTICAL:

    857:  let promote          = var("SYNTH_NO_LOCAL_PROMOTE").is_err();    // unset -> TRUE
    1684: let islands_disabled = var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some(); // unset -> FALSE

Both capabilities ship ON. The expression alone cannot tell you that; what closes
the gap is the BINDING NAME, which says what the boolean MEANS. `promote` is a
positive name, so true = enabled. `islands_disabled` is a negative name, so false
= enabled.

So the rule is one line and has no special cases:

    capability ships ON  <=>  (boolean when unset) XOR (binding name is negative)

An earlier draft of THIS FILE special-cased `SYNTH_NO_*` by name instead, and its
own self-test rejected it: keying on the prefix gets `is_err` sites backwards,
and it would have been a HAND-WRITTEN RULE about a naming convention rather than
a reading of the code — the mirror this project's North Star forbids. The prefix
now carries no weight at all; it merely correlates with a negative binding name.
The five `SYNTH_NO_*` flags classify correctly because of their BINDINGS.

A flag whose expression or binding this cannot read is reported UNDETERMINED and
counted separately. It is never silently bucketed — an unclassified flag
presented as "not shipping off" would be the wrong-subject class one level up.

Usage:
    python3 scripts/shipped_feature_census.py
    python3 scripts/shipped_feature_census.py --self-test
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
# THE SHIPPED SET, verified at authoring rather than assumed: of 270 `.rs` files
# under `crates/`, 128 match this glob and the other 142 are 135 `tests/`, 6
# `examples/` and 1 `benches/` — no shipped code sits outside `crates/*/src/`.
# Two flags are read ONLY out there (`SYNTH_EMIT_A64_SURFACE`,
# `SYNTH_REFREEZE_PRINT`, both in `tests/`) and are correctly absent here.
SRC_GLOB = "crates/*/src/**/*.rs"
# A build script can gate a capability at COMPILE time, which no runtime census
# can see. Nothing does today; if something starts, this census would silently
# describe a smaller feature set than the binary has, so it REFUSES instead.
BUILD_GLOB = "crates/*/build.rs"

# INSTRUMENTATION, decided by NAME — a JUDGEMENT, not a derivation, and printed
# as its own bucket for that reason. It decides 14 of 38 flags, so it is the
# largest hand-written rule left in this file and it is labelled rather than
# folded into the derived counts (the RQ-77-CENSUS convention: name the reading,
# do not merge a judgement into a measurement).
DIAG = re.compile(r"(DEBUG|STATS|VERBOSE|DUMP|REPORT|AUDIT|OBJDUMP|SOLVER_DIFF)$")

# NOT instrumentation, though an earlier draft of this file filed them there by
# the same name rule, under a bucket label asserting "no emitted byte changes".
# These are SOLVER BUDGETS with numeric defaults, and the budget decides what
# gets PROVEN: `synth-verify/src/solver.rs` documents that
# `SYNTH_ORDEAL_DEADLINE_MS=0` disables the wall-clock deadline and "re-opens the
# #849 hang class", and a query that times out answers `Unknown`, so a smaller
# budget admits fewer proof-carrying elisions. They ship ON with a default value,
# which is a third polarity this census does not otherwise model, so they are
# named here rather than bucketed by a regex that claims too much.
SOLVER_BUDGET = {"SYNTH_ORDEAL_DEADLINE_MS", "SYNTH_ORDEAL_MAX_CONFLICTS"}

# MEASURE-ONLY, and this entry is the PROOF THAT THE NAME RULE ABOVE IS NOT
# ENOUGH. `SYNTH_SHADOW_ALLOC` is named exactly like a capability — no DEBUG,
# STATS or DUMP suffix for `DIAG` to catch — and the first version of this census
# reported it as a capability the delivered binary lacks. It is not. Its own
# source says so at `arm_backend.rs:2014`: "the measure-only bridge between the
# built analysis layer and the eventual virtual-register wiring ... off by default
# and side-effect-free either way", and `:1954` groups it WITH the diagnostics —
# "Diagnostics inside (SYNTH_FUSE_STATS, SYNTH_SHADOW_ALLOC, SYNTH_SPILL_REPORT)
# ... never a byte change". Its guarded block contains three `eprintln!` and no
# mutation. So the earlier count of 5 OVER-reported hidden capability by one.
#
# A DERIVED DISCRIMINATOR WAS TRIED AND REJECTED, recorded so it is not re-tried
# blind: score each flag's guarded block by print macros versus mutation markers
# (`&mut`, `.push(`, `.insert(`, ...) and call a print-only block measure-only.
# It finds SHADOW_ALLOC — and also flags `SYNTH_GRAPH_ALLOC` and
# `SYNTH_GRAPH_ALLOC_FORCE`, which ARE real capabilities: their reads sit inside a
# tiny `fn enabled()` whose block is the boolean, not the capability's effect. TWO
# FALSE POSITIVES IN THREE HITS. A gate that noisy gets routed around, which this
# repo's own ratchet documentation warns about by name, so it is not shipped and
# the classification stays an explicit, grounded list of one.
MEASURE_ONLY = {"SYNTH_SHADOW_ALLOC"}

ON, OFF, UNKNOWN = "on-by-default", "SHIPS-OFF", "undetermined"

# An ARITHMETIC floor on the self-test's own work, checked in Python rather than
# by a CI grep. `grep -qE '[0-9]+ assertions'` is a DIGIT CLASS, not a floor — it
# accepts zero, so a self-test whose body stopped running passes it. That is the
# #1435 defect the v0.78 citation-floor lane fixed one layer up, and repeating it
# here would be the same mistake in a file whose subject is mechanical honesty.
# It is a FLOOR, not an equality: adding an assertion must never red CI, but
# losing one must.
MIN_ASSERTIONS = 39

# A binding whose NAME is negative inverts what its boolean means. These are the
# words this tree actually uses; an unmatched name is read as positive, which is
# the convention for `if <cond> { do_the_thing }`.
NEGATIVE_BINDING = re.compile(
    r"(?:^|_)(?:no|not|dis|disable[d]?|off|skip|suppress|reject|deny|forbid|"
    r"without|inhibit|block)(?:$|_)")


def _skip_scan(text: str, i: int) -> int:
    """Advance past a string, char, raw string or comment starting at `i`.

    A brace counter that does not do this is fooled by `"{"` in a literal — and
    this tree has plenty, including the Rocq emitter's own brace-heavy templates.
    Returns `i` unchanged when nothing special starts here.
    """
    if text.startswith("//", i):
        j = text.find("\n", i)
        return len(text) if j < 0 else j
    if text.startswith("/*", i):
        j = text.find("*/", i + 2)
        return len(text) if j < 0 else j + 2
    if text.startswith('r"', i) or text.startswith('r#', i):
        k = i + 1
        hashes = 0
        while k < len(text) and text[k] == "#":
            hashes += 1
            k += 1
        if k < len(text) and text[k] == '"':
            end = text.find('"' + "#" * hashes, k + 1)
            return len(text) if end < 0 else end + 1 + hashes
        return i
    if text[i] in "\"'":
        q = text[i]
        k = i + 1
        while k < len(text):
            if text[k] == "\\":
                k += 2
                continue
            if text[k] == q:
                return k + 1
            if q == "'" and k - i > 3:
                return i            # a lifetime like `'a`, not a char literal
            k += 1
        return len(text)
    return i


def non_test(text: str) -> str:
    """Shipped code only: every `#[cfg(test)]` ITEM removed, line count preserved.

    NOT a truncation at the first `#[cfg(test)]`. That was this file's own first
    implementation and it is a DOCUMENTED REPEAT of the v0.77 selector-classifier
    defect: `instruction_selector.rs` carries a `#[cfg(test)] fn aapcs_param_regs`
    helper at 1% of a 29,616-line file, so cutting there discarded 99% of the
    shipped selector — and `properties.rs` and `expansion_validator.rs` lost
    two thirds each. Four of 128 files cut early. No flag was lost at the
    measuring commit, which is luck, not a predicate: the sole read after a cut
    (`SYNTH_SEL_DSL_REGEN`) happens to sit in a genuine `mod tests`. One env read
    added to the selector's body would have vanished silently.

    Each `#[cfg(test)]` is removed together with the item it attributes, found by
    brace balance (`mod`/`fn`/`impl`) or by the terminating `;` (`use`). Removed
    spans become blank lines so reported line numbers stay true to the file.
    """
    out = list(text)
    for m in re.finditer(r"^[ \t]*#\[cfg\(test\)\]", text, re.M):
        i = m.end()
        depth = 0
        opened = False
        while i < len(text):
            j = _skip_scan(text, i)
            if j != i:
                i = j
                continue
            c = text[i]
            if c == "{":
                depth += 1
                opened = True
            elif c == "}":
                depth -= 1
                if opened and depth == 0:
                    i += 1
                    break
            elif c == ";" and not opened and depth == 0:
                i += 1
                break
            i += 1
        for k in range(m.start(), min(i, len(out))):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out)


def binding_of(expr: str) -> str | None:
    """The identifier this env read is bound to, or None for a bare condition.

    SCOPED TO THE ENCLOSING STATEMENT, not to a fixed line window. A forward-only
    `lines[i:i+3]` window misses every binding rustfmt wrapped onto its own line
    — measured: 13 of this tree's reads, including `SYNTH_GRAPH_ALLOC`'s `fn
    enabled()` and `SYNTH_SPILL_ON_EXHAUST`'s `spill_on_exhaust_enabled`. But
    naively widening BACKWARD is also wrong: two lines above `SYNTH_FUSE_STATS`
    sits an unrelated `let arm_instrs = ...`, and a window would adopt it as the
    binding. So the search runs back only to the enclosing statement boundary
    (`;`, `{` or `}`), which is where a binding for THIS read can legally be.
    """
    e = " ".join(expr.split())
    head = e[: e.find("env::var")] if "env::var" in e else e
    # Back up to the statement this read belongs to.
    cut = max(head.rfind(";"), head.rfind("{"), head.rfind("}"))
    stmt = head[cut + 1:]
    for pat in (r"\blet\s+(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]+)?=",
                r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(",
                r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*="):
        m = re.search(pat, stmt)
        if m:
            return m.group(1)
    # An `fn` signature ends with `{`, so the statement cut consumed it. The
    # function this read is the body of is the LAST `fn` declared before that
    # brace — scoped to before the brace so an unrelated earlier `fn` cannot be
    # adopted once any statement has intervened.
    brace = head.rfind("{")
    if brace < 0:
        return None
    names = re.findall(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", head[:brace])
    return names[-1] if names else None


def boolean_when_unset(flag: str, expr: str):
    """True/False if the expression's value with the variable UNSET is readable."""
    e = " ".join(expr.split())
    q = re.escape(flag)
    # unset -> True
    if re.search(rf'!\s*std::env::var\("{q}"\)\.is_ok_and\(\|v\|\s*v\s*==\s*"0"\)', e):
        return True
    if re.search(rf'std::env::var(?:_os)?\("{q}"\)\.is_err\(\)', e):
        return True
    if re.search(rf'std::env::var(?:_os)?\("{q}"\)\.is_none\(\)', e):
        return True
    if re.search(r'map_or\(\s*true', e) or re.search(r'unwrap_or(?:_else)?\([^)]*"1"', e):
        return True
    if re.search(rf'if\s+std::env::var\("{q}"\)\.is_ok_and\(\|v\|\s*v\s*==\s*"0"\)', e):
        return True
    # unset -> False
    if re.search(rf'std::env::var\("{q}"\)\.is_ok_and\(', e):
        return False
    if re.search(rf'std::env::var(?:_os)?\("{q}"\)\.is_(?:ok|some)\(\)', e):
        return False
    return None


def feature_polarity(flag: str, expr: str) -> str:
    """Is the CAPABILITY on or off when the variable is UNSET?

    ONE rule, no special cases:
        ON  <=>  (boolean when unset) XOR (binding name is negative)
    """
    b = boolean_when_unset(flag, expr)
    if b is None:
        return UNKNOWN
    name = binding_of(expr)
    negative = bool(name and NEGATIVE_BINDING.search(name.lower()))
    return ON if (b != negative) else OFF


def modifier_of(flag: str, all_flags) -> str | None:
    """The flag this one MODIFIES, if its name strictly extends another read flag.

    `SYNTH_GRAPH_ALLOC_FORCE` is not a seventh capability the binary is missing —
    it is a seam that only means anything once `SYNTH_GRAPH_ALLOC` is on. That
    relation is DERIVED from the flag set, not from a `_FORCE` suffix rule: a
    flag named `SYNTH_FOO_FORCE` with no `SYNTH_FOO` read anywhere gates its own
    capability and is reported as one. The longest match wins, so a two-level
    extension is attributed to its nearest parent.
    """
    parents = [f for f in all_flags
               if f != flag and flag.startswith(f + "_")]
    return max(parents, key=len) if parents else None


def census(root: pathlib.Path = ROOT):
    srcs = sorted(root.glob(SRC_GLOB))
    if not srcs:
        sys.exit(f"REFUSE: {SRC_GLOB} matched no files under {root} — every count "
                 f"below would be about the empty set")
    for b in sorted(root.glob(BUILD_GLOB)):
        if re.search(r'env::var(?:_os)?\s*\(\s*"SYNTH_', b.read_text(errors="ignore")):
            sys.exit(f"REFUSE: {b.relative_to(root)} reads a SYNTH_* variable. A "
                     f"build script gates a capability at COMPILE time, which a "
                     f"census of runtime reads cannot see — so this census would "
                     f"under-report the hidden feature set, which is the exact "
                     f"question it exists to answer. Classify it by hand and "
                     f"extend this script before trusting any count below.")
    # EVERY read site, not the first one. A flag read at several sites gets one
    # verdict per site and they must AGREE; first-match-wins is the shape behind
    # the `.position()`/`.rposition()` miscompile (#757) and behind this file's
    # own first test-module cut, so it is refused rather than trusted.
    sites: dict[str, list] = {}
    for p in srcs:
        lines = non_test(p.read_text(errors="ignore")).splitlines()
        for i, ln in enumerate(lines):
            for m in re.finditer(r'env::var(?:_os)?\s*\(\s*"(SYNTH_[A-Z0-9_]+)"', ln):
                flag = m.group(1)
                expr = " ".join(lines[max(0, i - 3): i + 3])
                sites.setdefault(flag, []).append(
                    (str(p.relative_to(root)), i + 1, expr))
    if not sites:
        sys.exit("REFUSE: zero SYNTH_* reads in non-test code across a non-empty "
                 "source set — the test-module cut or the pattern is broken, not "
                 "the tree")
    rows, disagree = [], []
    for flag, ss in sorted(sites.items()):
        if flag in SOLVER_BUDGET:
            kind, verdicts = "solver-budget", {"solver-budget"}
        elif flag in MEASURE_ONLY:
            kind, verdicts = "measure-only", {"measure-only"}
        elif DIAG.search(flag):
            kind, verdicts = "instrumentation", {"instrumentation"}
        else:
            verdicts = {feature_polarity(flag, e) for _p, _l, e in ss}
            kind = next(iter(verdicts)) if len(verdicts) == 1 else UNKNOWN
        if len(verdicts) > 1:
            disagree.append((flag, sorted((p, l, feature_polarity(flag, e))
                                          for p, l, e in ss)))
        path, line, _e = ss[0]
        rows.append((flag, f"{path}:{line}", kind, ss, modifier_of(flag, sites)))
    if disagree:
        lines = [f"  {f}: " + ", ".join(f"{p}:{l} => {v}" for p, l, v in ss)
                 for f, ss in disagree]
        sys.exit("REFUSE: these flags classify DIFFERENTLY at different read "
                 "sites, so no single verdict is true of the shipped binary:\n"
                 + "\n".join(lines))
    return len(srcs), rows


def cargo_feature_axis(root: pathlib.Path = ROOT):
    """The OTHER way capability hides: a Cargo feature that is not in the build.

    The maintainer's question said "features", and in this repo that word also
    names Cargo features — a mechanism no census of runtime env reads can see.
    Two DIFFERENT binaries are delivered and they do not carry the same set:
    `.github/workflows/release.yml` builds `-p synth-cli --features verify`,
    while `cargo install synth-cli` takes `default` only.
    """
    cli = root / "crates/synth-cli/Cargo.toml"
    if not cli.exists():
        sys.exit(f"REFUSE: {cli} not found — the feature axis would report an "
                 f"empty set and read as 'nothing is gated'")
    txt = cli.read_text()
    block = re.search(r"^\[features\](.*?)(?=^\[)", txt, re.M | re.S)
    if not block:
        sys.exit("REFUSE: synth-cli declares no [features] table; this function "
                 "asserts a feature axis that the manifest does not have")
    # THE CHARACTER CLASS IS THE DEFECT, for the THIRD time in this project's
    # history. `[a-z][a-z0-9-]*` silently dropped `exports_only_275_probe`
    # because of its UNDERSCORES — the same shape as `[a-z-]*` missing
    # `synth-backend-aarch64` for its DIGITS (reference_publishable_crates) and
    # as `[4-9][0-9]*` not being a floor (#1435). A feature this misses reads as
    # "not declared", which is indistinguishable from "not hidden".
    feats = dict(re.findall(r"^([A-Za-z_][A-Za-z0-9_-]*)\s*=\s*\[([^\]]*)\]",
                            block.group(1), re.M))
    if "default" not in feats:
        sys.exit("REFUSE: no `default` feature found, so 'not reachable from "
                 "default' has no meaning")
    reach, stack = set(), [f.strip().strip('"') for f in feats["default"].split(",") if f.strip()]
    while stack:
        f = stack.pop()
        if f in reach:
            continue
        reach.add(f)
        stack += [x.strip().strip('"') for x in feats.get(f, "").split(",") if x.strip()]
    rel = re.findall(r"cargo build --release[^\n]*?--features ([A-Za-z0-9_,-]+)",
                     (root / ".github/workflows/release.yml").read_text())
    release_extra = sorted({x for grp in rel for x in grp.split(",")})
    return feats, sorted(reach), release_extra


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    nsrc, rows = census()
    off_all = [r for r in rows if r[2] == OFF]
    ships_off = [r for r in off_all if r[4] is None]
    modifiers = [r for r in off_all if r[4] is not None]
    on = [r for r in rows if r[2] == ON]
    instr = [r for r in rows if r[2] == "instrumentation"]
    meas = [r for r in rows if r[2] == "measure-only"]
    budget = [r for r in rows if r[2] == "solver-budget"]
    unk = [r for r in rows if r[2] == UNKNOWN]

    print(f"AXIS 1 — RUNTIME ENV FLAGS, derived over {nsrc} shipped source files: "
          f"{len(rows)} SYNTH_* flags")
    print(f"\n  CAPABILITY NOT IN THE DELIVERED BINARY (unset => disabled): {len(ships_off)}")
    for flag, where, _k, _ss, _m in ships_off:
        print(f"    {flag:32} {where}")
    print(f"\n  ships off but MODIFIES one of the above rather than gating its own")
    print(f"  capability — derived from the flag set, not a suffix rule: {len(modifiers)}")
    for flag, _w, _k, _ss, parent in modifiers:
        print(f"    {flag:32} modifies {parent}")
    print(f"\n  on by default, the flag is an OPT-OUT: {len(on)}")
    for flag, where, _k, _ss, _m in on:
        print(f"    {flag:32} {where}")
    print(f"\n  SOLVER BUDGETS — on by default WITH A VALUE, and the value decides")
    print(f"  what gets proven, so these are not 'no emitted byte changes': {len(budget)}")
    for flag, where, _k, _ss, _m in budget:
        print(f"    {flag:32} {where}")
    print(f"\n  MEASURE-ONLY — off by default and side-effect-free, so being off is")
    print(f"  not missing capability. Named, with the source line as ground: {len(meas)}")
    for flag, where, _k, _ss, _m in meas:
        print(f"    {flag:32} {where}")
    print(f"\n  instrumentation, classified by NAME (a JUDGEMENT, not derived): {len(instr)}")
    print("    " + ", ".join(f for f, _w, _k, _s, _m in instr))
    print(f"\n  UNDETERMINED — read by hand, never bucketed silently: {len(unk)}")
    for flag, where, _k, ss, _m in unk:
        print(f"    {flag:32} {where}\n       {ss[0][2][:110]}")

    feats, reach, release_extra = cargo_feature_axis()
    gated = sorted(set(feats) - set(reach) - {"default"})
    print(f"\nAXIS 2 — CARGO FEATURES, which no census of runtime reads can see.")
    print(f"  TWO DIFFERENT BINARIES ARE DELIVERED and they are not the same set:")
    print(f"    release.yml  : default + {release_extra}")
    print(f"    cargo install: default only = {reach}")
    print(f"  declared but NOT reachable from `default`: {len(gated)}")
    for f in gated:
        if f in release_extra:
            note = "  <- IN the release binary, NOT in `cargo install`"
        elif not feats[f].strip():
            note = "  <- enables no dependency; a test probe, not a capability"
        else:
            note = "  <- in NEITHER delivered binary"
        print(f"    {f:24} = [{feats[f].strip()}]{note}")

    named = len(instr) + len(budget) + len(meas)
    print(f"\n  THE LIMIT OF THIS CENSUS, stated rather than left to be discovered:")
    print(f"  it derives POLARITY (is the capability reachable with the variable")
    print(f"  unset?) from the code. Whether a flag CHANGES EMITTED BYTES is a")
    print(f"  separate question it decides BY NAME for {named} of {len(rows)} flags, and")
    print(f"  `SYNTH_SHADOW_ALLOC` is the proof that rule misses things.")
    print(f"\nshipped-feature-census: axis 1 — {len(rows)} flags, {len(ships_off)} "
          f"capabilities ship off (+{len(modifiers)} modifiers), {len(unk)} "
          f"undetermined; axis 2 — {len(gated)} features off the default build, "
          f"{len([f for f in gated if f not in release_extra])} in NEITHER "
          f"delivered binary")
    # A capability shipping off is a DISCLOSURE, not a failure: each is an
    # evidence-gated flip with a recorded reason. An UNDETERMINED flag IS a
    # failure, because it means this census cannot describe the binary.
    return 1 if unk else 0


def self_test() -> int:
    fails, ran = [], []

    def ok(name, cond):
        ran.append(name)
        print(f"  {'ok  ' if cond else 'FAIL'} {name}")
        if not cond:
            fails.append(name)

    # ================================================ TRAP 1 — boolean polarity
    ok("RQ-78-FEATURESET: `!var(X).is_ok_and(|v| v == \"0\")` is ON by default "
       "(the substring match that produced a hand count of 15)",
       feature_polarity("SYNTH_X", 'if !std::env::var("SYNTH_X").is_ok_and(|v| v == "0") {') == ON)

    # THE TWO LIVE SITES, VERBATIM. Their booleans are OPPOSITE when unset and
    # both capabilities ship ON, so no classifier reading boolean polarity as
    # feature polarity can pass both, and none keyed on the `SYNTH_NO_` PREFIX
    # can pass the first.
    ok("RQ-78-FEATURESET: arm_backend.rs:857 — `is_err()` bound to a POSITIVE "
       "name (`promote`) ships ON",
       feature_polarity("SYNTH_NO_LOCAL_PROMOTE",
                        'let promote = std::env::var("SYNTH_NO_LOCAL_PROMOTE").is_err();') == ON)
    ok("RQ-78-FEATURESET: arm_backend.rs:1684 — `is_some()` bound to a NEGATIVE "
       "name (`islands_disabled`) ALSO ships ON, on the OPPOSITE boolean",
       feature_polarity("SYNTH_NO_LITPOOL_ISLANDS",
                        'let islands_disabled = std::env::var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some();') == ON)
    ok("RQ-78-FEATURESET: those two sites DISAGREE on the boolean — which is what "
       "makes the boolean unusable as the answer",
       boolean_when_unset("SYNTH_NO_LOCAL_PROMOTE",
                          'let promote = std::env::var("SYNTH_NO_LOCAL_PROMOTE").is_err();')
       is not
       boolean_when_unset("SYNTH_NO_LITPOOL_ISLANDS",
                          'let islands_disabled = std::env::var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some();'))
    ok("RQ-78-FEATURESET: a `SYNTH_NO_*` flag that must be SET to enable ships "
       "OFF — the prefix is not the evidence, the binding is",
       feature_polarity("SYNTH_NO_MISNAMED",
                        'let enable = std::env::var("SYNTH_NO_MISNAMED").is_ok();') == OFF)
    ok("`var(X).is_ok_and(|v| v != \"0\")` in an `fn enabled()` SHIPS OFF "
       "(the SYNTH_GRAPH_ALLOC shape)",
       feature_polarity("SYNTH_GRAPH_ALLOC",
                        'fn enabled() -> bool { std::env::var("SYNTH_GRAPH_ALLOC")'
                        '.is_ok_and(|v| v != "0") }') == OFF)
    ok("a bare `if var(X).is_ok()` with no binding SHIPS OFF",
       feature_polarity("SYNTH_W", 'if std::env::var("SYNTH_W").is_ok() {') == OFF)
    ok("`map_or(true, ...)` is ON by default",
       feature_polarity("SYNTH_U", 'let e = std::env::var("SYNTH_U").map_or(true, |v| v != "0");') == ON)

    # ============================== TRAP 2 — the binding is not on the same line
    # rustfmt wraps a long read onto its own line; a forward-only window then
    # sees no binding at all. MEASURED: 13 reads in this tree, including
    # SYNTH_GRAPH_ALLOC and SYNTH_SPILL_ON_EXHAUST.
    ok("RQ-78-FEATURESET: a binding on the PREVIOUS line is still found "
       "(rustfmt-wrapped read)",
       binding_of('let islands_disabled =\n'
                  '    std::env::var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some();')
       == "islands_disabled")
    ok("RQ-78-FEATURESET: and its verdict is ON, not OFF — a forward-only window "
       "reads this as a bare condition and gets the OPPOSITE answer",
       feature_polarity("SYNTH_NO_LITPOOL_ISLANDS",
                        'let islands_disabled =\n'
                        '    std::env::var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some();') == ON)
    # ...but widening the window NAIVELY is also wrong. Two lines above
    # SYNTH_FUSE_STATS sits an unrelated `let arm_instrs = ...`.
    ok("RQ-78-FEATURESET: an unrelated `let` in a PRECEDING statement is NOT "
       "adopted as the binding (the SYNTH_FUSE_STATS shape)",
       binding_of('let arm_instrs = fuse(arm_instrs);\n'
                  'if std::env::var("SYNTH_FUSE_STATS").is_ok() {') is None)
    ok("a `let` binding in the same statement is read",
       binding_of('let promote = std::env::var("X").is_err();') == "promote")
    ok("an enclosing `fn` is read as the binding when the body has none",
       binding_of('fn enabled() -> bool {\n    std::env::var("X").is_ok()') == "enabled")
    ok("`islands_disabled` is a negative name",
       bool(NEGATIVE_BINDING.search("islands_disabled")))
    ok("`promote` is NOT negative — a bare substring rule matching 'no' would "
       "break every positive binding",
       not NEGATIVE_BINDING.search("promote"))
    ok("`enabled` is NOT negative despite containing 'na'",
       not NEGATIVE_BINDING.search("enabled"))

    # ======================== TRAP 3 — the test cut, a DOCUMENTED v0.77 REPEAT
    # instruction_selector.rs carries `#[cfg(test)] fn aapcs_param_regs` at 1% of
    # a 29,616-line file. Truncating at the first `#[cfg(test)]` discarded 99% of
    # the shipped selector. Each cfg(test) ITEM must go, not everything after it.
    sel_shape = ('fn ship_a() { std::env::var("SYNTH_BEFORE"); }\n'
                 '#[cfg(test)]\n'
                 'fn helper() -> u32 { 0 }\n'
                 'fn ship_b() { std::env::var("SYNTH_AFTER"); }\n'
                 '#[cfg(test)]\n'
                 'mod tests { std::env::var("SYNTH_TESTONLY"); }\n')
    cut = non_test(sel_shape)
    ok("RQ-78-FEATURESET: a `#[cfg(test)] fn` helper does NOT truncate the file — "
       "shipped code AFTER it survives (the instruction_selector.rs shape)",
       "SYNTH_AFTER" in cut and "SYNTH_BEFORE" in cut)
    ok("RQ-78-FEATURESET: and the test-only read is still removed",
       "SYNTH_TESTONLY" not in cut and "helper" not in cut)
    ok("line numbers are PRESERVED, so reported locations stay true to the file",
       len(cut.splitlines()) == len(sel_shape.splitlines()))
    ok("a `#[cfg(test)] use ...;` item is removed at its semicolon",
       "test_only_import" not in non_test(
           '#[cfg(test)]\nuse foo::test_only_import;\nfn ship() { var("SYNTH_S"); }')
       and "SYNTH_S" in non_test(
           '#[cfg(test)]\nuse foo::test_only_import;\nfn ship() { var("SYNTH_S"); }'))
    # The brace counter must not be fooled by a brace inside a string literal —
    # this tree emits brace-heavy Rocq templates from Rust string constants.
    ok("RQ-78-FEATURESET: a `{` inside a STRING LITERAL does not unbalance the "
       "cfg(test) item scan",
       "SYNTH_SURVIVES" in non_test(
           '#[cfg(test)]\nmod t { let s = "{{{"; }\n'
           'fn ship() { std::env::var("SYNTH_SURVIVES"); }'))

    # ================================================== the modifier attribution
    live = {"SYNTH_GRAPH_ALLOC", "SYNTH_GRAPH_ALLOC_FORCE", "SYNTH_FACT_SPEC",
            "SYNTH_FACT_SPEC_FORCE_ADMIT", "SYNTH_SPILL_ON_EXHAUST"}
    ok("RQ-78-FEATURESET: `SYNTH_GRAPH_ALLOC_FORCE` MODIFIES `SYNTH_GRAPH_ALLOC` "
       "— so the count is 5 independent capabilities, not 7",
       modifier_of("SYNTH_GRAPH_ALLOC_FORCE", live) == "SYNTH_GRAPH_ALLOC")
    ok("`SYNTH_FACT_SPEC_FORCE_ADMIT` modifies `SYNTH_FACT_SPEC`",
       modifier_of("SYNTH_FACT_SPEC_FORCE_ADMIT", live) == "SYNTH_FACT_SPEC")
    ok("a capability with no parent in the set is NOT a modifier",
       modifier_of("SYNTH_GRAPH_ALLOC", live) is None
       and modifier_of("SYNTH_SPILL_ON_EXHAUST", live) is None)
    ok("RQ-78-FEATURESET: a `_FORCE` flag whose parent is read NOWHERE is NOT a "
       "modifier — the relation is the flag set, not the suffix",
       modifier_of("SYNTH_ORPHAN_FORCE", {"SYNTH_ORPHAN_FORCE", "SYNTH_OTHER"}) is None)
    ok("a two-level extension attributes to its NEAREST parent",
       modifier_of("SYNTH_A_B_C", {"SYNTH_A", "SYNTH_A_B", "SYNTH_A_B_C"}) == "SYNTH_A_B")

    # ==================================== the measure-only correction (over-report)
    ok("RQ-78-FEATURESET: `SYNTH_SHADOW_ALLOC` is MEASURE-ONLY, not a capability "
       "the binary lacks — its own source calls it side-effect-free, and the first "
       "census OVER-reported hidden capability by one",
       "SYNTH_SHADOW_ALLOC" in MEASURE_ONLY)
    ok("RQ-78-FEATURESET: and `DIAG` cannot catch it — the name carries no DEBUG/"
       "STATS/DUMP suffix, which is why the name rule needed an explicit list",
       not DIAG.search("SYNTH_SHADOW_ALLOC"))
    ok("the three name-decided buckets are DISJOINT, so no flag is counted twice",
       not (MEASURE_ONLY & SOLVER_BUDGET)
       and not any(DIAG.search(f) for f in MEASURE_ONLY | SOLVER_BUDGET))

    # ============================================== AXIS 2 — the Cargo features
    feats, reach, release_extra = cargo_feature_axis()
    ok("RQ-78-FEATURESET: `exports_only_275_probe` IS found — a feature name with "
       "UNDERSCORES, which `[a-z][a-z0-9-]*` silently dropped (the third instance "
       "of a too-narrow character class in this repo)",
       "exports_only_275_probe" in feats)
    ok("RQ-78-FEATURESET: `verify` is NOT reachable from synth-cli's `default`, "
       "so `cargo install synth-cli` yields a binary whose `synth verify` "
       "loud-declines",
       "verify" in feats and "verify" not in reach)
    ok("RQ-78-FEATURESET: ...but release.yml DOES build with it, so the two "
       "delivered binaries carry different feature sets",
       "verify" in release_extra)
    ok("`riscv` IS reachable from default", "riscv" in reach)

    # ============================================== refusals, each made to fire
    ok("an unrecognised expression is UNDETERMINED, never bucketed as on or off",
       feature_polarity("SYNTH_T", 'let x = weird_helper("SYNTH_T");') == UNKNOWN)
    ok("an empty source set REFUSES rather than reporting zero capabilities",
       _refuses(lambda: census(pathlib.Path("/nonexistent-root-for-census"))))
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        (root / "crates/c/src").mkdir(parents=True)
        (root / "crates/c/src/lib.rs").write_text(
            'let x = std::env::var("SYNTH_REAL").is_ok();')
        # POSITIVE CONTROL: without a build.rs the same tree must SUCCEED, or the
        # refusal below proves nothing about the build script.
        ok("the temp tree classifies WITHOUT a build.rs (positive control)",
           not _refuses(lambda: census(root)))
        (root / "crates/c/build.rs").write_text(
            'fn main() { if std::env::var("SYNTH_COMPILE_GATE").is_ok() {} }')
        ok("RQ-78-FEATURESET: a build.rs reading a SYNTH_* var REFUSES — a "
           "compile-time gate is invisible to a runtime census",
           _refuses(lambda: census(root)))
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        (root / "crates/a/src").mkdir(parents=True)
        (root / "crates/b/src").mkdir(parents=True)
        # BOTH bindings must be POSITIVE. A first draft used `let off = ...`,
        # and `off` is a NEGATIVE binding word, so both sites classified ON and
        # the fixture proved nothing about the refusal.
        (root / "crates/a/src/lib.rs").write_text(
            'let enable = std::env::var("SYNTH_SPLIT").is_err();')
        (root / "crates/b/src/lib.rs").write_text(
            'let enable = std::env::var("SYNTH_SPLIT").is_ok();')
        ok("RQ-78-FEATURESET: one flag classified DIFFERENTLY at two read sites "
           "REFUSES — first-match-wins is the #757 `.position()` shape",
           _refuses(lambda: census(root)))
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        (root / "crates/c/src").mkdir(parents=True)
        (root / "crates/c/src/lib.rs").write_text("fn ship() { let x = 1; }")
        ok("RQ-78-FEATURESET: a NON-EMPTY source set with zero SYNTH_* reads "
           "REFUSES — '0 capabilities hidden' from a broken pattern is a true "
           "statement about nothing",
           _refuses(lambda: census(root)))

    print(f"shipped-feature-census-self-test: {len(ran)} assertions, "
          f"{len(fails)} failure(s)")
    if len(ran) < MIN_ASSERTIONS:
        print(f"REFUSE: only {len(ran)} assertions ran, floor is "
              f"{MIN_ASSERTIONS}. Assertions were REMOVED or the body stopped "
              f"early — '0 failures' from a test that did not run is the "
              f"vacuous green this file exists to make impossible.")
        return 1
    return 1 if fails else 0


def _refuses(fn) -> bool:
    try:
        fn()
    except SystemExit as e:
        return str(e).startswith("REFUSE:")
    return False


if __name__ == "__main__":
    sys.exit(main())
