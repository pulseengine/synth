#!/usr/bin/env python3
# ci-status: wired — `--self-test` runs in the required `claim-check` job. The
# census itself prints a DERIVED list and asserts nothing about the compiler's
# output, so there is no expected value for CI to fail on beyond the self-test.
"""Which capabilities does the SHIPPED binary actually have? (#1436)

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

# Diagnostics change no emitted byte: they print, dump or bound a solver. Being
# off by default is correct for them, so they are reported separately rather
# than counted as hidden capability.
DIAG = re.compile(r"(DEBUG|STATS|VERBOSE|DUMP|REPORT|AUDIT|OBJDUMP|SOLVER_DIFF"
                  r"|DEADLINE_MS|MAX_CONFLICTS)$")

ON, OFF, UNKNOWN = "on-by-default", "SHIPS-OFF", "undetermined"

# An ARITHMETIC floor on the self-test's own work, checked in Python rather than
# by a CI grep. `grep -qE '[0-9]+ assertions'` is a DIGIT CLASS, not a floor — it
# accepts zero, so a self-test whose body stopped running passes it. That is the
# #1435 defect the v0.78 citation-floor lane fixed one layer up, and repeating it
# here would be the same mistake in a file whose subject is mechanical honesty.
# It is a FLOOR, not an equality: adding an assertion must never red CI, but
# losing one must.
MIN_ASSERTIONS = 25

# A binding whose NAME is negative inverts what its boolean means. These are the
# words this tree actually uses; an unmatched name is read as positive, which is
# the convention for `if <cond> { do_the_thing }`.
NEGATIVE_BINDING = re.compile(
    r"(?:^|_)(?:no|not|dis|disable[d]?|off|skip|suppress|reject|deny|forbid|"
    r"without|inhibit|block)(?:$|_)")


def non_test(text: str) -> str:
    """Everything before the test module. A flag read only under `#[cfg(test)]`
    is not shipped behaviour, and counting it would describe the test binary."""
    m = re.search(r"^#\[cfg\(test\)\]", text, re.M)
    return text[: m.start()] if m else text


def binding_of(expr: str) -> str | None:
    """The identifier this env read is bound to, or None for a bare condition.

    `let promote = ...`, `let x: bool = ...`, `fn enabled(...) -> bool { ... }`
    and `foo = ...` all name the boolean. A bare `if <expr> {` names nothing.
    """
    e = " ".join(expr.split())
    for pat in (r"\blet\s+(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]+)?=",
                r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(",
                r"^([A-Za-z_][A-Za-z0-9_]*)\s*="):
        m = re.search(pat, e)
        if m:
            return m.group(1)
    return None


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
    found: dict[str, tuple[str, str]] = {}
    for p in srcs:
        lines = non_test(p.read_text(errors="ignore")).splitlines()
        for i, ln in enumerate(lines):
            for m in re.finditer(r'env::var(?:_os)?\s*\(\s*"(SYNTH_[A-Z0-9_]+)"', ln):
                flag = m.group(1)
                if flag in found:
                    continue
                found[flag] = (str(p.relative_to(root)), " ".join(lines[i : i + 3]))
    if not found:
        sys.exit("REFUSE: zero SYNTH_* reads in non-test code across a non-empty "
                 "source set — the test-module cut or the pattern is broken, not "
                 "the tree")
    rows = []
    for flag, (path, expr) in sorted(found.items()):
        kind = "diagnostic" if DIAG.search(flag) else feature_polarity(flag, expr)
        rows.append((flag, path, kind, expr, modifier_of(flag, found)))
    return len(srcs), rows


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    nsrc, rows = census()
    off_all = [r for r in rows if r[2] == OFF]
    ships_off = [r for r in off_all if r[4] is None]
    modifiers = [r for r in off_all if r[4] is not None]
    on = [r for r in rows if r[2] == ON]
    diag = [r for r in rows if r[2] == "diagnostic"]
    unk = [r for r in rows if r[2] == UNKNOWN]
    print(f"shipped-feature census over {nsrc} source files, {len(rows)} SYNTH_* "
          f"flags read in non-test code")
    print(f"\nCAPABILITY NOT IN THE DELIVERED BINARY (unset => disabled): {len(ships_off)}")
    for flag, path, _k, _e, _m in ships_off:
        print(f"  {flag:32} {path}")
    print(f"\nalso ships off, but MODIFIES a flag above rather than gating its own")
    print(f"capability — derived from the flag set, not a suffix rule: {len(modifiers)}")
    for flag, path, _k, _e, parent in modifiers:
        print(f"  {flag:32} modifies {parent}")
    print(f"\non by default, the flag is an OPT-OUT: {len(on)}")
    for flag, path, _k, _e, _m in on:
        print(f"  {flag:32} {path}")
    print(f"\ndiagnostics (no emitted byte changes): {len(diag)}")
    print("  " + ", ".join(f for f, _p, _k, _e, _m in diag))
    print(f"\nUNDETERMINED — read by hand, never bucketed silently: {len(unk)}")
    for flag, path, _k, expr, _m in unk:
        print(f"  {flag:32} {path}\n       {expr[:110]}")
    print(f"\nshipped-feature-census: {len(rows)} flags, {len(ships_off)} capabilities "
          f"ship off (+{len(modifiers)} modifiers of them), {len(unk)} undetermined")
    # A capability shipping off is a DISCLOSURE, not a failure: each is an
    # evidence-gated flip with a recorded reason. An UNDETERMINED flag is a
    # failure, because it means this census cannot describe the binary.
    return 1 if unk else 0


def self_test() -> int:
    fails = []

    ran = []

    def ok(name, cond):
        ran.append(name)
        print(f"  {'ok  ' if cond else 'FAIL'} {name}")
        if not cond:
            fails.append(name)

    # ---------------------------------------------------------------- TRAP 1
    # The negated `== "0"` form is an OPT-OUT, not a hidden capability. Matching
    # `is_ok_and` as a SUBSTRING is what produced a count of 15.
    ok("RQ-78-FEATURESET: `!var(X).is_ok_and(|v| v == \"0\")` is ON by default "
       "(the substring match that produced a count of 15)",
       feature_polarity("SYNTH_X", 'if !std::env::var("SYNTH_X").is_ok_and(|v| v == "0") {') == ON)

    # ---------------------------------------------------------------- TRAP 2
    # THE TWO LIVE SITES, COPIED VERBATIM from arm_backend.rs. Their booleans are
    # OPPOSITE when unset and both capabilities ship ON. Any classifier that reads
    # boolean polarity as feature polarity fails one of these two, and any
    # classifier keyed on the `SYNTH_NO_` PREFIX fails the first one.
    ok("RQ-78-FEATURESET: live site arm_backend.rs:857 — `is_err()` bound to a "
       "POSITIVE name (`promote`) ships ON",
       feature_polarity("SYNTH_NO_LOCAL_PROMOTE",
                        'let promote = std::env::var("SYNTH_NO_LOCAL_PROMOTE").is_err();') == ON)
    ok("RQ-78-FEATURESET: live site arm_backend.rs:1684 — `is_some()` bound to a "
       "NEGATIVE name (`islands_disabled`) ALSO ships ON, on the OPPOSITE boolean",
       feature_polarity("SYNTH_NO_LITPOOL_ISLANDS",
                        'let islands_disabled = std::env::var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some();') == ON)
    ok("RQ-78-FEATURESET: those two sites disagree on the BOOLEAN — which is what "
       "makes the boolean unusable as the answer",
       boolean_when_unset("SYNTH_NO_LOCAL_PROMOTE",
                          'let promote = std::env::var("SYNTH_NO_LOCAL_PROMOTE").is_err();')
       is not
       boolean_when_unset("SYNTH_NO_LITPOOL_ISLANDS",
                          'let islands_disabled = std::env::var_os("SYNTH_NO_LITPOOL_ISLANDS").is_some();'))
    # NEGATIVE CONTROL for the prefix rule: a `NO_` flag CAN ship off, if its name
    # lies about its sense. A prefix-keyed classifier reports ON here and is wrong.
    ok("RQ-78-FEATURESET: a `SYNTH_NO_*` flag that must be SET to enable ships "
       "OFF — the prefix is not the evidence, the binding is",
       feature_polarity("SYNTH_NO_MISNAMED",
                        'let enable = std::env::var("SYNTH_NO_MISNAMED").is_ok();') == OFF)

    # --------------------------------------------------- the genuine OFF shapes
    ok("`var(X).is_ok_and(|v| v != \"0\")` with a positive binding SHIPS OFF "
       "(the SYNTH_GRAPH_ALLOC shape)",
       feature_polarity("SYNTH_GRAPH_ALLOC",
                        'fn enabled() -> bool { std::env::var("SYNTH_GRAPH_ALLOC")'
                        '.is_ok_and(|v| v != "0") }') == OFF)
    ok("a bare `if var(X).is_ok()` with no binding SHIPS OFF",
       feature_polarity("SYNTH_W", 'if std::env::var("SYNTH_W").is_ok() {') == OFF)
    ok("`map_or(true, ...)` is ON by default",
       feature_polarity("SYNTH_U", 'let e = std::env::var("SYNTH_U").map_or(true, |v| v != "0");') == ON)

    # ------------------------------------------------------- binding extraction
    ok("a `let` binding is read", binding_of('let promote = std::env::var("X").is_err();') == "promote")
    ok("an `fn` binding is read", binding_of('fn enabled() -> bool { x }') == "enabled")
    ok("a bare condition has NO binding, and is read as positive",
       binding_of('if std::env::var("X").is_ok() {') is None)
    ok("`islands_disabled` is a negative name",
       bool(NEGATIVE_BINDING.search("islands_disabled")))
    ok("`promote` is NOT a negative name — a substring rule matching 'no' inside "
       "an ordinary word would break every positive binding",
       not NEGATIVE_BINDING.search("promote"))
    ok("`enabled` is NOT a negative name despite containing 'na'",
       not NEGATIVE_BINDING.search("enabled"))

    # ------------------------------------------------- the modifier attribution
    live = {"SYNTH_GRAPH_ALLOC", "SYNTH_GRAPH_ALLOC_FORCE", "SYNTH_FACT_SPEC",
            "SYNTH_FACT_SPEC_FORCE_ADMIT", "SYNTH_SPILL_ON_EXHAUST"}
    ok("RQ-78-FEATURESET: `SYNTH_GRAPH_ALLOC_FORCE` MODIFIES `SYNTH_GRAPH_ALLOC` "
       "— so the ships-off count is 5 independent capabilities, not 7",
       modifier_of("SYNTH_GRAPH_ALLOC_FORCE", live) == "SYNTH_GRAPH_ALLOC")
    ok("`SYNTH_FACT_SPEC_FORCE_ADMIT` modifies `SYNTH_FACT_SPEC`",
       modifier_of("SYNTH_FACT_SPEC_FORCE_ADMIT", live) == "SYNTH_FACT_SPEC")
    ok("a capability with no parent in the set is NOT a modifier",
       modifier_of("SYNTH_GRAPH_ALLOC", live) is None
       and modifier_of("SYNTH_SPILL_ON_EXHAUST", live) is None)
    # NEGATIVE CONTROL: the relation is derived from the flag SET. A `_FORCE`
    # suffix with no parent read anywhere gates its own capability.
    ok("RQ-78-FEATURESET: a `_FORCE` flag whose parent is NOT read is NOT a "
       "modifier — the relation is the flag set, not the suffix",
       modifier_of("SYNTH_ORPHAN_FORCE", {"SYNTH_ORPHAN_FORCE", "SYNTH_OTHER"}) is None)
    ok("a two-level extension attributes to its NEAREST parent",
       modifier_of("SYNTH_A_B_C", {"SYNTH_A", "SYNTH_A_B", "SYNTH_A_B_C"}) == "SYNTH_A_B")

    # ---------------------------------------------------------- refusals & cuts
    ok("an unrecognised expression is UNDETERMINED, never bucketed as on or off",
       feature_polarity("SYNTH_T", 'let x = weird_helper("SYNTH_T");') == UNKNOWN)
    ok("a flag read ONLY under #[cfg(test)] is not shipped behaviour",
       'SYNTH_ONLY_IN_TESTS' not in non_test(
           'fn a(){}\n#[cfg(test)]\nmod t { std::env::var("SYNTH_ONLY_IN_TESTS"); }'))
    ok("the cut keeps non-test code rather than discarding everything",
       'SYNTH_SHIPPED' in non_test(
           'let a = std::env::var("SYNTH_SHIPPED");\n#[cfg(test)]\nmod t {}'))
    ok("an empty source set REFUSES rather than reporting zero capabilities",
       _refuses(lambda: census(pathlib.Path("/nonexistent-root-for-census"))))
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        root = pathlib.Path(d)
        (root / "crates/c/src").mkdir(parents=True)
        (root / "crates/c/src/lib.rs").write_text(
            'let x = std::env::var("SYNTH_REAL").is_ok();')
        # POSITIVE CONTROL first: the same tree with no build.rs must SUCCEED,
        # or the refusal below would prove nothing about the build script.
        ok("the temp tree classifies WITHOUT a build.rs (positive control)",
           not _refuses(lambda: census(root)))
        (root / "crates/c/build.rs").write_text(
            'fn main() { if std::env::var("SYNTH_COMPILE_GATE").is_ok() {} }')
        ok("RQ-78-FEATURESET: a build.rs reading a SYNTH_* var REFUSES — a "
           "compile-time gate is invisible to a runtime census",
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
