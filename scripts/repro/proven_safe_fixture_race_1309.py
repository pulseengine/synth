#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^proven_safe fixture race: processes=(\d+) FAILED=0$/ >= 16
"""RQ-69-TESTISO (#1309) — the #901 fixtures must not be shared between processes.

RED-FIRST, measured 2026-09-18 on the pre-fix tree (cf35150a):

    ROUNDS=6 CONCURRENCY=8 processes=48 FAILED=16
      proven_safe::tests::sites_are_keyed_per_function_901 ... FAILED
      proven_safe::tests::valid_sites_become_marks_901 ... FAILED
      proven_safe::tests::width_disagreement_is_dropped_901 ... FAILED

Cause: every process built its fixtures under a FIXED
`temp_dir()/proven_safe_901_unit`. `File::create` truncates, so one process read
a fixture another was rewriting and `ingest` refused a document that is valid on
disk a millisecond later. #1309 was filed from READING the code; this is the
script that turned it into an observation.

WHY IT SPAWNS A PREBUILT BINARY RATHER THAN N CARGOS: concurrent `cargo test`
invocations block on the target-directory lock, so they would serialize and the
probe would pass while never overlapping — a vacuous oracle of exactly the kind
this project keeps finding. The binary is built ONCE, then executed N times in
parallel.

The `ci-checks` floor above binds the PRINTED process count, not the exit code:
a run that spawned nothing would exit 0 while checking nothing.

    python3 scripts/repro/proven_safe_fixture_race_1309.py [--procs N] [--rounds R]
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def build_and_locate() -> Path:
    """Build the synth-core test binary once and ask cargo where it landed.

    Never guess the hashed filename — it changes with every toolchain and
    feature-set change, and a stale guess is the `#stale-binary` trap this repo
    has already paid for.
    """
    proc = subprocess.run(
        ["cargo", "test", "-p", "synth-core", "--no-run", "--message-format=json"],
        cwd=ROOT, capture_output=True, text=True,
    )
    exe = None
    for line in proc.stdout.splitlines():
        try:
            msg = json.loads(line)
        except ValueError:
            continue
        target = msg.get("target") or {}
        # Select on the target's KIND, not its name: cargo reports the LIB
        # target name (`synth_core`, underscores), not the package name
        # (`synth-core`, hyphens), and matching the package spelling silently
        # finds nothing. `test: true` + kind `lib` is the unit-test binary —
        # the integration tests in the same package are kind `test`.
        if msg.get("executable") and target.get("test") and target.get("kind") == ["lib"]:
            exe = msg["executable"]
    if not exe:
        sys.exit(f"could not locate the synth-core test binary\n{proc.stderr[-2000:]}")
    return Path(exe)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--procs", type=int, default=8)
    ap.add_argument("--rounds", type=int, default=2)
    args = ap.parse_args()

    binary = build_and_locate()
    print(f"binary: {binary}")

    total = 0
    failed = 0
    failing_tests: set[str] = set()
    for _round in range(args.rounds):
        running = [
            subprocess.Popen(
                [str(binary), "proven_safe", "--test-threads=4"],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            for _ in range(args.procs)
        ]
        for p in running:
            out, _ = p.communicate()
            total += 1
            if p.returncode != 0:
                failed += 1
                for line in out.splitlines():
                    if line.startswith("test ") and line.endswith(" FAILED"):
                        failing_tests.add(line)

    # The verdict line the CI floor binds.
    print(f"proven_safe fixture race: processes={total} FAILED={failed}")
    if failed:
        print("--- distinct failing tests ---")
        for t in sorted(failing_tests):
            print(f"  {t}")
        print("fixtures are being shared between processes (#1309)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
