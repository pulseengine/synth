#!/usr/bin/env python3
"""VCR-VER-004 — INSTRUMENT INDEPENDENCE, proven by re-running v0.53's mutation.

**The finding this responds to.** v0.53's VCR-DEC-001 lane proved BY MUTATION
that emptying `liveness::cfg_exit_observable` — the exit contract the join-aware
graph allocator and its own CFG validator SHARE — makes the compiler emit code
that leaves the function's return value in the WRONG REGISTER, and that BOTH
per-compilation validators accept it:

  * `validate_cfg_rewrite`     (the pass's acceptance oracle)  -> Ok
  * `validate_final_allocation`(VCR-RA-003, whole-function)    -> Consistent

Only EXECUTION caught it. Two independent-*looking* instruments, one shared
blind spot — and a direct counterexample to the claim that per-compilation
validation is an independent check on the code generator.

**What this script proves.** It re-applies v0.53's EXACT mutation (the committed
patch `mutations/v053_shared_exit_contract.patch` — not a reconstruction, not an
artificially constructed input), rebuilds, and asserts on the SAME compilation of
the SAME fixture:

  (1) `validate_cfg_rewrite` ACCEPTS the rewrite            [the blind spot]
  (2) VCR-RA-003 reports Consistent                          [the blind spot]
  (3) VCR-VER-004 `validate_abi_contract` REJECTS it with a CONCRETE violation
      naming the ABI result register                         [the new instrument]
  (4) the miscompile is therefore NOT EMITTED: the function declines to the
      shipping allocator.

(1) is the load-bearing assertion. It is what makes (3) non-vacuous: because the
dataflow gate returned Ok, the pre-VCR-VER-004 compiler would have emitted this
rewrite. No opt-out flag is needed to show that, and deliberately none exists —
an env var that disables the instrument would be a footgun, not evidence.

**Why the new check fails differently** (the point of the lane, in one line):
`validate_cfg_rewrite` is a BACKWARD must-analysis whose obligation set is a
VARIABLE seeded from the shared table, and the empty set is a fixpoint — so
emptying the seed makes it vacuously green. `validate_abi_contract` is a FORWARD
value analysis whose obligation is the AAPCS result registers, hard-named in its
own source; a forward evaluation always produces exactly one value for R0 at each
return, so there is always exactly one obligation per sink and there is no seed
to shrink.

Run (needs cargo; no emulator, no solver):
    python3 scripts/repro/vcr_ver_004_instrument_independence.py
Exits nonzero if any of (1)-(4) does not hold. ALWAYS restores the tree.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
PATCH = REPO / "scripts/repro/mutations/v053_shared_exit_contract.patch"
FIXTURE = REPO / "scripts/repro/brif_outer_740.wat"
TOUCHED = [
    "crates/synth-synthesis/src/liveness.rs",
    "crates/synth-synthesis/src/graph_alloc.rs",
]

# The exact three verdict lines, as emitted by the compiler under
# SYNTH_GRAPH_ALLOC_STATS / SYNTH_RA003_VERBOSE.
ACCEPT_DATAFLOW = "[graph-alloc] join colouring ACCEPTED by validate_cfg_rewrite (dataflow)"
RA003_CONSISTENT = "VCR-RA-003: Consistent"
ABI_REJECT = re.compile(
    r"\[graph-alloc\] REJECTED by the ABI observable contract \(VCR-VER-004\): "
    r"Violated \{ sink: (\d+), reg: (R0|R1) \}"
)
DECLINED = "[graph-alloc] DECLINED → shipping reallocate_function"


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=REPO, capture_output=True, text=True, **kw)


def build():
    r = run(["cargo", "build", "--bin", "synth"])
    if r.returncode != 0:
        print(r.stderr[-4000:], file=sys.stderr)
        raise SystemExit("FATAL: cargo build failed")
    # Resolve the binary the way cargo did (CARGO_TARGET_DIR may be redirected —
    # the stale-./target/debug/synth trap).
    meta = run(["cargo", "metadata", "--format-version", "1", "--no-deps"])
    import json

    target_dir = json.loads(meta.stdout)["target_directory"]
    return str(Path(target_dir) / "debug" / "synth")


def compile_fixture(synth):
    env = dict(os.environ)
    env.update(
        SYNTH_GRAPH_ALLOC="1",
        SYNTH_GRAPH_ALLOC_STATS="1",
        SYNTH_RA003_VERBOSE="1",
    )
    r = subprocess.run(
        [synth, "compile", str(FIXTURE), "--relocatable", "-o", os.devnull],
        cwd=REPO,
        capture_output=True,
        text=True,
        env=env,
    )
    return r.stdout + r.stderr


def main():
    if not PATCH.is_file():
        raise SystemExit(f"FATAL: missing mutation patch {PATCH}")
    dirty = run(["git", "diff", "--name-only", "--"] + TOUCHED).stdout.split()
    if dirty:
        raise SystemExit(
            "FATAL: the files the mutation touches are already modified: "
            + ", ".join(dirty)
        )

    problems = []

    # ---- BASELINE: the unmutated compiler applies to this fixture ----------
    synth = build()
    base = compile_fixture(synth)
    if ACCEPT_DATAFLOW not in base:
        problems.append(
            "BASELINE: the join allocator does not reach the fixture — this "
            "script would gate nothing. Re-pick the fixture."
        )
    if ABI_REJECT.search(base):
        problems.append(
            "BASELINE: VCR-VER-004 rejects the UNMUTATED compiler — a FALSE "
            "REJECTION. The instrument is broken, not the compiler."
        )
    if problems:
        for p in problems:
            print("FAIL " + p)
        return 1
    print("OK   baseline: join colouring applies AND the ABI contract holds")

    # ---- MUTATED: v0.53's exact mutation, re-applied -----------------------
    r = run(["git", "apply", str(PATCH)])
    if r.returncode != 0:
        print(r.stderr, file=sys.stderr)
        raise SystemExit("FATAL: could not apply the mutation patch")
    try:
        synth = build()
        out = compile_fixture(synth)
    finally:
        rev = run(["git", "apply", "-R", str(PATCH)])
        if rev.returncode != 0:
            print(rev.stderr, file=sys.stderr)
            raise SystemExit("FATAL: could not REVERT the mutation — tree dirty!")

    # (1) the pass's own dataflow oracle is GREEN on this rewrite
    if ACCEPT_DATAFLOW in out:
        print("OK   (1) validate_cfg_rewrite ACCEPTS the mutated rewrite")
    else:
        problems.append(
            "(1) validate_cfg_rewrite did NOT accept — the mutation no longer "
            "reproduces the v0.53 blind spot, so (3) proves nothing"
        )

    # (2) VCR-RA-003 is GREEN on the same compilation
    if RA003_CONSISTENT in out:
        print("OK   (2) VCR-RA-003 validate_final_allocation reports Consistent")
    else:
        problems.append("(2) VCR-RA-003 did not report Consistent")

    # (3) VCR-VER-004 REJECTS, concretely
    m = ABI_REJECT.search(out)
    if m:
        print(
            f"OK   (3) VCR-VER-004 REJECTS: result register {m.group(2)} holds a "
            f"different value at the return terminator (instr {m.group(1)})"
        )
    else:
        problems.append(
            "(3) VCR-VER-004 did NOT reject the mutated rewrite — the static "
            "check does not catch the class it exists for"
        )

    # (4) and therefore the miscompile is not emitted
    if DECLINED in out:
        print("OK   (4) the function DECLINES to the shipping allocator — not emitted")
    else:
        problems.append("(4) the function did not decline; the rewrite was emitted")

    print()
    print(f"VCR-VER-004-INDEPENDENCE ASSERTIONS={4 - len(problems)}/4")
    if problems:
        for p in problems:
            print("FAIL " + p)
        print("RESULT: FAIL")
        return 1
    print("RESULT: PASS — the v0.53 mutation is now caught STATICALLY, by an")
    print("        instrument that shares neither the exit contract nor the CFG")
    print("        with the pass, while both dataflow validators stay green.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
