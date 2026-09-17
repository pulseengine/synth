#!/usr/bin/env python3
"""RQ-68-REPRO (#1291) — the determinism gate synth never had.

relay built drone software to wasm and through synth twice and got two
different files. Measured before this gate existed: the ELF was byte-identical
and the SBOM differed only in a wall-clock timestamp — codegen WAS
deterministic, by accident of implementation, with nothing to notice if that
stopped being true.

This compiles every scripts/repro/*.wat fixture with two synth binaries built
in INDEPENDENT target directories (so a build-time non-determinism in the
compiler itself is visible, not just a run-time one), into separate output
directories, under a pinned SOURCE_DATE_EPOCH and an environment scrubbed of
every ambient SYNTH_* lever, and fails on ANY difference in exit code, object
bytes, or SBOM bytes. The comparison is raw: nothing is normalised. That is
sound because both builds write the same file NAME into different
directories, and the SBOM records only the base name.

Potency is not assumed: `--plant VAR=VAL` applies one lever to the SECOND
build only, and scripts/test_determinism_check.py requires that to go red.

usage: determinism_check.py <synth-a> <synth-b> [--plant VAR=VAL] [--min-pairs N]
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
EPOCH = "1700000000"
CONFIGS = {
    "self": ["--target", "cortex-m4", "--all-exports"],
    "reloc": ["--target", "cortex-m4", "--relocatable", "--all-exports"],
}


def clean_env(extra: dict[str, str]) -> dict[str, str]:
    env = {k: v for k, v in os.environ.items()
           if not k.startswith("SYNTH_") and k != "SOURCE_DATE_EPOCH"}
    env["SOURCE_DATE_EPOCH"] = EPOCH
    env.update(extra)
    return env


def compile_one(binp: str, mod: pathlib.Path, cfg: str, outdir: pathlib.Path,
                extra: dict[str, str]):
    elf = outdir / f"{mod.stem}.{cfg}.elf"
    sbom = outdir / f"{mod.stem}.{cfg}.cdx.json"
    r = subprocess.run([binp, "compile", str(mod), "-o", str(elf), *CONFIGS[cfg],
                        "--sbom", str(sbom)],
                       capture_output=True, text=True, env=clean_env(extra), timeout=300)
    elf_b = elf.read_bytes() if (r.returncode == 0 and elf.exists()) else None
    sbom_t = sbom.read_text() if (r.returncode == 0 and sbom.exists()) else None
    return r.returncode, elf_b, sbom_t


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("synth_a")
    ap.add_argument("synth_b")
    ap.add_argument("--plant", default=None, help="VAR=VAL applied to the SECOND build only")
    ap.add_argument("--min-pairs", type=int, default=100)
    a = ap.parse_args()
    plant = {}
    if a.plant:
        k, _, v = a.plant.partition("=")
        plant = {k: v}
    mods = sorted((ROOT / "scripts/repro").glob("*.wat"))
    with tempfile.TemporaryDirectory() as ta, tempfile.TemporaryDirectory() as tb:
        da, db = pathlib.Path(ta), pathlib.Path(tb)
        jobs = [(m, c) for m in mods for c in CONFIGS]

        def pair(job):
            m, c = job
            return (m.name, c,
                    compile_one(a.synth_a, m, c, da, {}),
                    compile_one(a.synth_b, m, c, db, plant))

        compared = both_failed = 0
        diffs = []
        with cf.ThreadPoolExecutor(8) as ex:
            for name, cfg, (rca, ea, sa), (rcb, eb, sb) in ex.map(pair, jobs):
                if rca != rcb:
                    diffs.append(f"{name} [{cfg}]: exit code {rca} vs {rcb}")
                    continue
                if rca != 0:
                    both_failed += 1
                    continue
                compared += 1
                if ea != eb:
                    diffs.append(f"{name} [{cfg}]: OBJECT bytes differ")
                if sa != sb:
                    diffs.append(f"{name} [{cfg}]: SBOM differs")
    print(f"determinism: {len(jobs)} compiles per binary over {len(mods)} fixtures x "
          f"{len(CONFIGS)} configs — {compared} compared, {both_failed} failed "
          f"identically on both, {len(diffs)} difference(s)"
          + (f" [planted {a.plant} on the second build]" if a.plant else ""))
    for d in diffs[:25]:
        print("  DIFF", d)
    if compared < a.min_pairs:
        print(f"FAIL: only {compared} successful pairs compared (< {a.min_pairs}) — "
              f"a gate that compares nothing is not a gate")
        return 1
    if diffs:
        print("FAIL: same source, same flags, different output (#1291)")
        return 1
    print("PASS: every output byte-identical across two independently built compilers")
    return 0


if __name__ == "__main__":
    sys.exit(main())
