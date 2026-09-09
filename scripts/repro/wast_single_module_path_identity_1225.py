#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 600
"""#1225 / RQ-65-MVPCORE (#1017) — a single-module `.wast` compiles to the SAME
bytes as its module compiled alone.

# The defect this gates

`synth compile file.wast` has its own driver branch — the multi-module MERGE
written for synth's i32-only fixture suite — and it passes EMPTY data
segments, EMPTY globals declarations and initializers and a DEFAULT aarch64
substrate to the backends (`compile_all_exports`, the `.wast` arm of the
decode tuple). Measured on main at authoring: the same one-module input
compiled as `probe.wast` vs `probe.wat` produced 868 vs 944 bytes; the `.wast`
image carried no data bytes and a `Reset_Handler` that never wrote R9, while
`get_g` in both was `ldr.w r4, [r9]`. Exit 0 both times.

That branch is what the spec-suite census (`scripts/spec_compile_census.py`,
the number `docs/status/SPEC_FAMILY_CENSUS.md` plans from) compiles — and it
is a path NO execution oracle runs: the parity oracle
(`selector_parity_197_differential.py`) writes each `(module ...)` to a `.wat`
and compiles that. So the census's `ok` was a property of an unexecuted path.

# The property

For every `.wast` in the corpus with exactly ONE top-level `(module ...)`
directive, and for every backend the census measures:

    synth compile file.wast  <flags>   ==   synth compile module.wat  <flags>

byte-for-byte on the emitted object when both succeed; the same exit status
and the same normalized refusal line when either declines; and the same set
of per-function skip reasons. The `.wat` leg is the module's own text, cut
out of the `.wast` by this harness's own top-level-form scanner (never
synth's extractor — that would compare the extractor with itself).

Red-first (#911): on the pre-fix binary the two legs DIFFER on every
data-carrying or globals-carrying single-module file (measured: the probe
above; `int_literals.wast` and the like are identical on both because they
carry neither) — this script exits 1 on main before the routing fix.

# Corpus and floors

`tests/spec-testsuite/*.wast` (the pinned submodule; the census's 257-file
floor is re-asserted here so an empty checkout is red, #1095) plus
`tests/wast/*.wast` (synth's own fixtures — every one is single-module, so
this also proves the fixture suite's bytes are unchanged by the routing).
`binary`/`quote` modules are declined by name (the `.wat` leg cannot carry
them); everything else must compare. The `compiles` floor is the driver's
own count of `synth … compile …` invocations (two per compared file per
backend).

Run:  SYNTH=<target>/release/synth python3 scripts/repro/wast_single_module_path_identity_1225.py
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SUITE = ROOT / "tests" / "spec-testsuite"
FIXTURES = ROOT / "tests" / "wast"
EXPECTED_SUITE_FILES = 257  # same floor as scripts/spec_compile_census.py

BACKENDS = {
    "arm": ["--cortex-m"],
    "riscv": ["-b", "riscv"],
    "aarch64": ["-b", "aarch64"],
}

SKIP_RE = re.compile(r"warning: skipping function '([^']+)': (.+)")


def top_level_forms(text: str):
    """Yield (head, body_text) for each top-level s-expression.

    Handles `;;` line comments, nested `(; ;)` block comments and string
    literals with escapes — the three things that can hide a paren.
    """
    n = len(text)
    i = 0
    while i < n:
        c = text[i]
        if c == ";" and text.startswith(";;", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if c == "(" and text.startswith("(;", i):
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("(;", i):
                    depth += 1
                    i += 2
                elif text.startswith(";)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        if c == "(":
            start = i
            depth = 0
            in_str = False
            while i < n:
                ch = text[i]
                if in_str:
                    if ch == "\\":
                        i += 1
                    elif ch == '"':
                        in_str = False
                elif ch == '"':
                    in_str = True
                elif ch == "(" and text.startswith("(;", i):
                    # block comment inside a form
                    d = 1
                    i += 2
                    while i < n and d:
                        if text.startswith("(;", i):
                            d += 1
                            i += 2
                        elif text.startswith(";)", i):
                            d -= 1
                            i += 2
                        else:
                            i += 1
                    continue
                elif ch == ";" and text.startswith(";;", i):
                    j = text.find("\n", i)
                    i = n if j < 0 else j
                    continue
                elif ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
            body = text[start:i]
            m = re.match(r"\(\s*([A-Za-z_.]+)", body)
            yield (m.group(1) if m else "?"), body
            continue
        i += 1


def single_module(text: str):
    """The one `(module ...)` form of a single-module file, or None."""
    mods = [b for h, b in top_level_forms(text) if h == "module"]
    if len(mods) != 1:
        return None
    return mods[0]


def is_binary_or_quote(module_text: str) -> bool:
    return re.match(r"\(\s*module\s+(\$[^\s()]+\s+)?(binary|quote)\b", module_text) is not None


def compile_one(synth: str, src: Path, out: Path, flags):
    p = subprocess.run(
        [synth, "compile", str(src), "--all-exports", "-o", str(out), *flags],
        capture_output=True, text=True, timeout=300,
    )
    err = p.stdout + p.stderr
    if "panicked" in err:
        return "panic", err, None
    skips = sorted((m.group(1), m.group(2).strip()) for m in SKIP_RE.finditer(err))
    first = next((l for l in err.splitlines() if l.startswith("Error")), "")
    data = out.read_bytes() if p.returncode == 0 and out.exists() else None
    return p.returncode, (first, skips), data


def normalize(msg: str, *names) -> str:
    for nm in names:
        msg = msg.replace(nm, "<in>")
    return re.sub(r"/[^\s'\"]*/(?:[^/\s'\"]+)", "<path>", msg)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--synth", default=os.environ.get("SYNTH", str(ROOT / "target/debug/synth")))
    ap.add_argument("--backend", choices=sorted(BACKENDS), action="append")
    ap.add_argument("--only", help="substring filter on file name")
    ap.add_argument("--no-suite", action="store_true", help="fixtures only (local smoke)")
    args = ap.parse_args()

    synth = args.synth
    if not Path(synth).is_file():
        print(f"FAIL: synth not found at {synth}")
        return 1

    files = sorted(FIXTURES.glob("*.wast"))
    if not args.no_suite:
        suite = sorted(SUITE.glob("*.wast"))
        if len(suite) != EXPECTED_SUITE_FILES:
            print(f"FAIL: expected {EXPECTED_SUITE_FILES} top-level .wast files in {SUITE}, "
                  f"found {len(suite)} — empty/moved submodule (#1095); refusing a vacuous run")
            return 1
        files += suite
    if args.only:
        files = [f for f in files if args.only in f.name]

    backends = args.backend or sorted(BACKENDS)
    fails = []
    total_compared = 0
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for be in backends:
            flags = BACKENDS[be]
            compared = identical = 0
            declined: Counter = Counter()
            mismatches = []
            for f in files:
                text = f.read_text(errors="replace")
                mod = single_module(text)
                if mod is None:
                    declined["multi-or-zero-module"] += 1
                    continue
                if is_binary_or_quote(mod):
                    declined["binary-or-quote-module"] += 1
                    continue
                wat = tmp / f"{f.stem}.wat"
                wat.write_text(mod)
                out_a = tmp / f"{f.stem}.wast.{be}.o"
                out_b = tmp / f"{f.stem}.wat.{be}.o"
                for o in (out_a, out_b):
                    if o.exists():
                        o.unlink()
                rc_a, info_a, data_a = compile_one(synth, f, out_a, flags)
                rc_b, info_b, data_b = compile_one(synth, wat, out_b, flags)
                compared += 1
                if rc_a == "panic" or rc_b == "panic":
                    mismatches.append((f.name, "PANIC on one leg"))
                    continue
                if rc_a != rc_b:
                    mismatches.append((f.name, f"exit {rc_a} (.wast) != {rc_b} (.wat): "
                                       f"{normalize(info_a[0], f.name, wat.name)[:140]!r} vs "
                                       f"{normalize(info_b[0], f.name, wat.name)[:140]!r}"))
                    continue
                ea = normalize(info_a[0], f.name, wat.name)
                eb = normalize(info_b[0], f.name, wat.name)
                if rc_a != 0 and ea != eb:
                    mismatches.append((f.name, f"refusal differs: {ea[:140]!r} vs {eb[:140]!r}"))
                    continue
                sa = [(n, normalize(r, f.name, wat.name)) for n, r in info_a[1]]
                sb = [(n, normalize(r, f.name, wat.name)) for n, r in info_b[1]]
                if sa != sb:
                    only_a = sorted(set(sa) - set(sb))[:3]
                    only_b = sorted(set(sb) - set(sa))[:3]
                    mismatches.append((f.name, f"skip set differs: .wast-only={only_a} .wat-only={only_b}"))
                    continue
                if data_a is not None and data_b is not None and data_a != data_b:
                    off = next((k for k, (x, y) in enumerate(zip(data_a, data_b)) if x != y),
                               min(len(data_a), len(data_b)))
                    mismatches.append((f.name, f"object bytes differ: {len(data_a)} vs {len(data_b)} "
                                       f"bytes, first diff at 0x{off:x}"))
                    continue
                identical += 1
            total_compared += compared
            print(f"== {be}: {len(files)} files, compared {compared}, identical {identical}, "
                  f"mismatch {len(mismatches)}, declined "
                  + (", ".join(f"{k}={v}" for k, v in sorted(declined.items())) or "none"))
            for name, why in mismatches[:40]:
                print(f"    MISMATCH {name}: {why}")
            if len(mismatches) > 40:
                print(f"    ... and {len(mismatches) - 40} more")
            if mismatches:
                fails.append(f"{be}: {len(mismatches)} single-module .wast file(s) compile "
                             f"differently from their module alone")
            if compared == 0:
                fails.append(f"{be}: compared 0 files — vacuous")
    # Non-vacuity: the suite carries well over a hundred single-module files.
    floor = 20 if args.no_suite or args.only else 300
    if total_compared < floor:
        fails.append(f"NON-VACUITY: compared {total_compared} file-backend pairs < floor {floor}")
    print(f"#1225 CHECKS={total_compared} single-module .wast files compared across {len(backends)} backend(s)")
    if fails:
        for x in fails:
            print(f"FAIL: {x}")
        return 1
    print("RESULT: PASS — every single-module .wast compiles to exactly the bytes its module compiles to alone")
    return 0


if __name__ == "__main__":
    sys.exit(main())
