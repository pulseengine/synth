#!/usr/bin/env python3
"""Byte triage — compare two synth builds over the corpus, byte for byte.

LIVES IN `scripts/`, NOT `scripts/repro/`, and that is a deliberate call rather
than a way around the ORACLE_WIRING ceiling. `scripts/repro/` is the population
of per-defect reproductions and differentials, each of which CI either runs or
must declare it does not. This is release/measurement INFRASTRUCTURE in the
shape of `determinism_check.py` and `mutation_survey.py`, which live here for
the same reason: it takes TWO binaries, and a CI run has exactly one. There is
no second build for CI to compare against, so declaring it `manual` in the
oracle population would be recording a debt that cannot ever be paid.

Byte triage: compile the corpus with two synth binaries and compare outputs.

RQ-69-SUBTRACT (#242) gate — a deletion that moves emitted bytes without an
oracle proving the new bytes correct is REFUSED. This proves the deletion moves
no byte at all.

    python3 byte_triage.py <synth-A> <synth-B> [--corpus DIR]

Classifies each (module, config) pair as:
    identical          both succeeded, byte-identical output
    identical-failure  both failed, same return code AND same stderr needle
    CHANGED            anything else — the thing this gate exists to catch
"""
import argparse
import hashlib
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

CONFIGS = [
    ("arm", "cortex-m4", []),
    ("arm", "cortex-m4f", []),
    ("arm", "cortex-m3", []),
    ("arm", "cortex-m55", []),                  # the Helium target specifically
    ("arm", "cortex-m4", ["--relocatable"]),
]


def compile_one(binary, wat, backend, target, extra, outdir, tag=""):
    # Unique per (module, config, binary) so parallel workers never share an
    # output path — the #1309 lesson, applied to the tool that checks #242.
    out = Path(outdir) / f"{Path(wat).stem}-{tag}.elf"
    if out.exists():
        out.unlink()
    cmd = [binary, "compile", str(wat), "-o", str(out),
           "-b", backend, "--target", target, *extra]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
    if p.returncode == 0 and out.exists() and out.stat().st_size > 0:
        return ("ok", hashlib.sha256(out.read_bytes()).hexdigest())
    # a failure is identified by rc plus the first line of stderr, so a
    # DIFFERENT refusal reason counts as a change rather than as "both failed"
    first = (p.stderr.strip().splitlines() or [""])[0][:160]
    return (f"rc{p.returncode}", first)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("binary_a")
    ap.add_argument("binary_b")
    ap.add_argument("--corpus", default="scripts/repro")
    ap.add_argument("--jobs", type=int, default=max(2, (os.cpu_count() or 4) // 2))
    args = ap.parse_args()

    wats = sorted(Path(args.corpus).glob("*.wat"))
    if not wats:
        sys.exit(f"no .wat files under {args.corpus}")

    identical = 0
    identical_failure = 0
    changed = []

    work = [(wat, b, t, e, i)
            for wat in wats
            for i, (b, t, e) in enumerate(CONFIGS)]

    def one(item):
        wat, backend, target, extra, ci = item
        with tempfile.TemporaryDirectory() as d:
            ra = compile_one(args.binary_a, wat, backend, target, extra, d, f"a{ci}")
            rb = compile_one(args.binary_b, wat, backend, target, extra, d, f"b{ci}")
        label = f"{wat.name}:{target}{'+reloc' if extra else ''}"
        return label, ra, rb

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for label, ra, rb in pool.map(one, work):
            if ra == rb:
                if ra[0] == "ok":
                    identical += 1
                else:
                    identical_failure += 1
            else:
                changed.append((label, ra, rb))

    total = identical + identical_failure + len(changed)
    print(f"byte triage: {len(wats)} modules x {len(CONFIGS)} configs = {total} compiles")
    print(f"  identical          {identical}")
    print(f"  identical-failure  {identical_failure}")
    print(f"  CHANGED            {len(changed)}")
    for tag, ra, rb in changed[:25]:
        print(f"    {tag}\n      A={ra}\n      B={rb}")
    return 1 if changed else 0


if __name__ == "__main__":
    sys.exit(main())
