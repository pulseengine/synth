#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 18
"""RQ-79-PAGESIZE (#1441) — the oracle that must land BEFORE `(pagesize 1)` is honoured.

WHY THIS EXISTS, AND WHY IT LANDS FIRST. #1315 closed by REFUSING a declared
custom page size, which was right: before the refusal, `(memory $a 1 1
(pagesize 1))` compiled rc=0 and reported `__synth_mem_size_0 = 0x10000` for a
memory the module declares as ONE BYTE, and that symbol is what an embedder
programs one MPU region from (#1145). The refusal made a silent wrong answer
loud. It did not implement the capability, and nothing tracked it until #1441.

Honouring the declaration CHANGES EMITTED CODE — `memory.size` lowers through a
division by a literal 65536 — so it is a reach increment, and this repo's gating
rule is that the oracle for newly-accepted input lands first.

THE PERMITTED SET IS DERIVED FROM THE SHIPPED SPEC SUITE, NOT ASSUMED. The lane
was first scoped to "powers of two >= 32 B, since ARMv7-M PMSA cannot use finer
anyway". The hardware reasoning is sound and the proposal still forbids it:
`tests/spec-testsuite/proposals/custom-page-sizes/custom-page-sizes-invalid.wast`
asserts `(pagesize 32)` invalid BY NAME, under its own heading "Power-of-two page
sizes that are not 1 or 64KiB". So this oracle PARSES both suite files and
derives the legal and invalid sets from them, rather than hardcoding a list that
would silently rot if the proposal moved. That is the repo's first invariant:
derive what you check against from the artifact you ship.

WHAT IT ASSERTS TODAY, non-vacuously, with the capability ABSENT:
  * every spec-INVALID size is refused by synth (they are also malformed input,
    so this pins that synth does not accept something the spec rejects);
  * `(pagesize 65536)` — legal, and equal to the default — is ACCEPTED, and the
    multi-memory region table reports 0x10000 per memory;
  * a module with NO page-size declaration is ACCEPTED and reports the same;
  * `(pagesize 1)` is refused, and the refusal NAMES #1315 — so a refusal that
    silently stops explaining itself is a failure, not a pass.

WHAT IT ASSERTS ONCE THE CAPABILITY LANDS. The `(pagesize 1)` mode is DERIVED by
probing, not switched by hand, so this file does not need editing when the
capability arrives — it auto-strengthens to: ACCEPT, `__synth_mem_size_N` equal
to the DECLARED BYTE COUNT (not a page multiple), and `__synth_mem_region_N`
equal to that count rounded UP to a power of two >= 32, which is the ARMv7-M
PMSA region constraint. Two symbols because one number cannot be true about both
the declaration and the region: reporting only the rounded extent re-creates
#1315's over-grant in miniature, and reporting only the declared count moves an
unstated rounding obligation onto the embedder, which is the class #1145 exists
to prevent (maintainer's decision, 2026-10-01).

EXACTLY ONE of the two modes must hold, and which one is PRINTED. A probe that
matched neither would otherwise let the whole file pass having checked nothing.

THE REGION TABLE IS MULTI-MEMORY ONLY, measured: a single-memory module emits no
`__synth_mem_*` symbols at all, so every size assertion here compiles a
TWO-memory module. A single-memory fixture would have made these legs vacuous
while still printing PASS.

Run:  python3 scripts/repro/pagesize_oracle_1441.py
"""

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SUITE = ROOT / "tests/spec-testsuite/proposals/custom-page-sizes"
VALID_WAST = SUITE / "custom-page-sizes.wast"
INVALID_WAST = SUITE / "custom-page-sizes-invalid.wast"

# Floors. A derived population of zero is a REFUSAL, not a pass — and these
# guard the `(pagesize N)` scrape against a suite reorganisation that would
# otherwise leave every loop below iterating over nothing.
MIN_INVALID = 14
MIN_LEGAL = 2
MIN_ASSERTIONS = 29

PMSA_MIN_REGION = 32  # ARMv7-M PMSA: a region is a power of two >= 32 bytes.
DEFAULT_PAGE = 65536  # named once: a diagnostic that restates its own expected
                      # value as a literal can contradict the check beside it.

CHECKS = 0


def fail(msg: str) -> "None":
    print(f"REFUSE: {msg}", file=sys.stderr)
    sys.exit(1)


def _strip_negative_assertions(text: str) -> tuple[str, str]:
    """Split a .wast into (positive, negative) by removing whole
    `(assert_malformed ...)` / `(assert_invalid ...)` forms by PAREN BALANCE.

    Measured need: `custom-page-sizes.wast` — the POSITIVE suite — contains
    `(assert_malformed (module quote "(memory (pagesize 0) (data))") ...)` at
    line 113, so a flat regex over the file derives `0` as a LEGAL size. A
    line-level exclusion would happen to work on that one-liner and would
    silently fail on a multi-line block, which is the same truncation class as
    cutting a region at the first `#[cfg(test)]` marker. Balanced removal has
    no such blind spot.
    """
    neg_heads = ("(assert_malformed", "(assert_invalid")
    pos, neg, i = [], [], 0
    while i < len(text):
        head = next((h for h in neg_heads if text.startswith(h, i)), None)
        if head is None:
            pos.append(text[i])
            i += 1
            continue
        depth, j, in_str = 0, i, False
        while j < len(text):
            c = text[j]
            if in_str:
                if c == "\\":
                    j += 2
                    continue
                if c == '"':
                    in_str = False
            elif c == '"':
                in_str = True
            elif c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        neg.append(text[i:j])
        i = j
    return "".join(pos), "".join(neg)


def _sizes(path: Path, which: str) -> set[int]:
    """Page sizes declared in `path`, from its POSITIVE or NEGATIVE forms."""
    if not path.is_file():
        fail(f"{path} is absent — the spec suite is this oracle's source of truth "
             f"for which page sizes are legal; without it nothing below is derived")
    pos, neg = _strip_negative_assertions(path.read_text())
    chosen = pos if which == "positive" else neg
    return {int(m) for m in re.findall(r"\(pagesize\s+(\d+)\)", chosen)}


def spec_sets() -> tuple[set[int], set[int]]:
    """LEGAL and INVALID page sizes, derived from the shipped suite."""
    # Only sizes in POSITIVE forms are legal; the positive suite carries one
    # negative assertion of its own, and the invalid suite is entirely negative.
    legal = _sizes(VALID_WAST, "positive")
    invalid = (_sizes(INVALID_WAST, "negative")
               | _sizes(INVALID_WAST, "positive")
               | _sizes(VALID_WAST, "negative")) - legal
    if len(invalid) < MIN_INVALID:
        fail(f"derived only {len(invalid)} spec-invalid page sizes from "
             f"{INVALID_WAST.name}, want >= {MIN_INVALID} — the scrape broke, so "
             f"the refusal legs below would iterate over almost nothing")
    if len(legal) < MIN_LEGAL:
        fail(f"derived only {len(legal)} legal page sizes, want >= {MIN_LEGAL}")
    if legal != {1, DEFAULT_PAGE}:
        fail(f"the suite's legal set is {sorted(legal)}, not {sorted({1, DEFAULT_PAGE})} — the "
             f"proposal moved, so this oracle's whole premise needs re-reading "
             f"before its expectations are trusted")
    return legal, invalid


def synth_bin() -> Path:
    # `oracle_run.py` passes the binary as $SYNTH; honour it so CI and a local
    # run measure the SAME binary. Three ways a binary lies — stale, shared,
    # mutant — and a local fallback that silently diverges from CI is the first.
    env = os.environ.get("SYNTH")
    if env:
        q = Path(env)
        if not q.is_absolute():
            q = ROOT / q
        if not q.is_file():
            fail(f"$SYNTH={env} does not exist; refusing to fall back to a "
                 f"different binary than the one CI was told to measure")
        return q
    for rel in ("target/debug/synth", "target/release/synth"):
        p = ROOT / rel
        if p.is_file():
            return p
    fail("no synth binary at target/{debug,release}/synth — build it first; an "
         "oracle that silently skips because its subject is missing is the "
         "'checker reports success about work it never did' class")


def two_memory_wat(pagesize: int | None, pages: int) -> str:
    ps = "" if pagesize is None else f" (pagesize {pagesize})"
    return (
        "(module\n"
        f"  (memory $a {pages} {pages}{ps})\n"
        f"  (memory $b {pages} {pages}{ps})\n"
        '  (func (export "sa") (result i32) (memory.size $a))\n'
        '  (func (export "sb") (result i32) (memory.size $b)))\n'
    )


def assemble(tmp: Path, name: str, wat: str) -> Path | None:
    w = tmp / f"{name}.wat"
    w.write_text(wat)
    out = tmp / f"{name}.wasm"
    p = subprocess.run(["wasm-tools", "parse", str(w), "-o", str(out)],
                       capture_output=True, text=True)
    return out if p.returncode == 0 and out.is_file() else None


def compile_arm(binary: Path, wasm: Path, obj: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(binary), "compile", str(wasm), "-t", "cortex-m3",
         "--relocatable", "--all-exports", "-o", str(obj)],
        capture_output=True, text=True, cwd=ROOT)


def mem_symbols(obj: Path) -> dict[str, int]:
    from elftools.elf.elffile import ELFFile
    with obj.open("rb") as fh:
        e = ELFFile(fh)
        tabs = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"]
        if not tabs:
            fail(f"{obj.name} has no symtab — cannot read the #1145 region table")
        return {s.name: s["st_value"] for s in tabs[0].iter_symbols()
                if s.name.startswith("__synth_mem")}


def check(cond: bool, msg: str) -> None:
    global CHECKS
    CHECKS += 1
    if not cond:
        fail(msg)


def roundup_pow2_min32(n: int) -> int:
    r = PMSA_MIN_REGION
    while r < n:
        r *= 2
    return r


def main() -> int:
    legal, invalid = spec_sets()
    binary = synth_bin()
    print(f"spec suite: {len(legal)} legal {sorted(legal)}, "
          f"{len(invalid)} invalid (derived from {INVALID_WAST.name})")

    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)

        # ── spec-INVALID sizes: synth must refuse every one ──────────────────
        refused_invalid = 0
        for sz in sorted(invalid):
            w = assemble(tmp, f"inv{sz}", two_memory_wat(sz, 1))
            if w is None:
                # The assembler rejects some malformed forms outright; those
                # never reach synth and are not evidence about synth.
                continue
            p = compile_arm(binary, w, tmp / f"inv{sz}.o")
            check(p.returncode != 0,
                  f"synth ACCEPTED (pagesize {sz}), which the shipped spec suite "
                  f"asserts invalid — accepting input the spec rejects is worse "
                  f"than refusing input it permits")
            refused_invalid += 1
        check(refused_invalid >= MIN_INVALID,
              f"only {refused_invalid} spec-invalid sizes actually reached synth "
              f"(want >= {MIN_INVALID}); the rest were dropped by the assembler, "
              f"so this leg measured almost nothing")
        print(f"spec-invalid: {refused_invalid} sizes reached synth, all refused")

        # ── the default page size, declared and undeclared: accepted ─────────
        for name, ps in (("explicit65536", 65536), ("undeclared", None)):
            w = assemble(tmp, name, two_memory_wat(ps, 1))
            check(w is not None, f"{name} failed to assemble")
            obj = tmp / f"{name}.o"
            p = compile_arm(binary, w, obj)
            check(p.returncode == 0,
                  f"synth refused {name} (pagesize={ps}), which is the DEFAULT "
                  f"page size and must always compile: {p.stderr.strip()[:200]}")
            syms = mem_symbols(obj)
            # DEFENCE IN DEPTH, measured both ways rather than assumed. Weakening
            # this predicate alone leaves the oracle GREEN, because the size legs
            # below also fail when the table is missing; but with the table made
            # invisible this guard is the one that FIRES FIRST, so it is what turns
            # "size is None" into "the region table is absent". Neither is
            # redundant: one names the cause, the other catches a wrong value.
            check(syms.get("__synth_mem_count") == 2,
                  f"{name}: __synth_mem_count = {syms.get('__synth_mem_count')}, "
                  f"want 2 — without the region table the size legs are vacuous")
            for idx in (0, 1):
                k = f"__synth_mem_size_{idx}"
                check(syms.get(k) == DEFAULT_PAGE,
                      f"{name}: {k} = {syms.get(k)}, want {DEFAULT_PAGE}")
            print(f"{name}: accepted, region table reports 0x10000 per memory")

        # ── `(pagesize 1)`: the capability. Mode is DERIVED, not switched ────
        PAGES = 20000
        w = assemble(tmp, "ps1", two_memory_wat(1, PAGES))
        check(w is not None, "(pagesize 1) failed to assemble — it is SPEC-LEGAL, "
                             "so a wasm-tools that rejects it is the finding")
        obj = tmp / "ps1.o"
        p = compile_arm(binary, w, obj)

        if p.returncode != 0:
            # CAPABILITY ABSENT. Pin the refusal AND that it still explains
            # itself: a refusal that stops naming its analysis issue sends the
            # next reader to nothing.
            err = (p.stderr + p.stdout).lower()
            check("page size" in err,
                  "(pagesize 1) was refused but the diagnostic does not mention "
                  "the page size — the refusal has drifted off its subject")
            check("#1315" in err or "1315" in err,
                  "(pagesize 1)'s refusal no longer cites #1315, where the "
                  "analysis and the over-grant measurement live")
            print("(pagesize 1): REFUSED, diagnostic still cites #1315 "
                  "— capability ABSENT (#1441 open)")
        else:
            # CAPABILITY PRESENT. Now the real assertions bite.
            syms = mem_symbols(obj)
            want_region = roundup_pow2_min32(PAGES)
            for idx in (0, 1):
                sk, rk = f"__synth_mem_size_{idx}", f"__synth_mem_region_{idx}"
                check(syms.get(sk) == PAGES,
                      f"{sk} = {syms.get(sk)}, want {PAGES} — with (pagesize 1) "
                      f"the declared size is a BYTE count; a page multiple here "
                      f"is #1315's over-grant returning in miniature")
                check(rk in syms,
                      f"{rk} absent — the embedder needs the MPU-legal extent as "
                      f"its own symbol, because {sk} is now the declaration")
                check(syms.get(rk) == want_region,
                      f"{rk} = {syms.get(rk)}, want {want_region} "
                      f"(power of two >= {PMSA_MIN_REGION}, PMSA)")
            print(f"(pagesize 1): ACCEPTED, size={PAGES} region={want_region} "
                  f"— capability PRESENT")

    if CHECKS < MIN_ASSERTIONS:
        fail(f"ran only {CHECKS} assertions, want >= {MIN_ASSERTIONS} — a thinned "
             f"oracle that still prints PASS is the failure this floor exists for")
    print(f"PASS: pagesize oracle, {CHECKS} assertions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
