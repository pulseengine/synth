#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^VCR-VER-004-INDEPENDENCE ASSERTIONS=(\d+)/4$/ >= 4
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

**What this script proves.** It re-plants v0.53's mutation — SEMANTICS
preserved exactly: empty the shared `cfg_exit_observable` contract, and strip
the colourer's select to a bare lowest-free pick so the emptied contract
manifests as a wrong-return-register rewrite — then rebuilds and asserts on the
SAME compilation of the SAME fixture:

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

**How the mutation is planted — structurally, not by line-context patch.** The
original committed `git apply` patch hardcoded diff context into
`graph_alloc.rs`, source this oracle does not own; RQ-60-RACOST increment 2's
select rewrite broke the context, the mutation stopped planting, and only the
non-vacuity floor (`ASSERTIONS >= 4`) turned that red instead of vacuously
green. The class is retired, not re-anchored: the exit-contract half replaces
the BRACE-MATCHED BODY of `cfg_exit_observable` (keyed on its signature — the
name both the pass and the validator consume, so a rename breaks far more than
this script), and the select half replaces the span between the
`v053-mutation-site:select-pick` BEGIN/END markers in `graph_alloc.rs`, which
travel with the decision when it is refactored. A missing signature or marker
is a LOUD failure here, never a silent skip, and no mutation source ever lives
in the tree — the mutated files are restored from git in a `finally`.

**Why the new check fails differently** (the point of the lane, in one line):
`validate_cfg_rewrite` is a BACKWARD must-analysis whose obligation set is a
VARIABLE seeded from the shared table, and the empty set is a fixpoint — so
emptying the seed makes it vacuously green. `validate_abi_contract` is a FORWARD
value analysis whose obligation is the AAPCS result registers, hard-named in its
own source; a forward evaluation always produces exactly one value for R0 at each
return, so there is always exactly one obligation per sink and there is no seed
to shrink.

**Proven RED-FIRST, and the evidence is reproducible.** Change `abi_gate` in
`graph_alloc.rs` to treat `AbiContractVerdict::Violated` as an accept, rebuild,
and re-run with the mutation applied: the compiler prints
`whole-function colouring APPLIED (validated)` and EMITS the miscompile, so
assertions (3) and (4) both fail. With the gate intact it prints
`DECLINED → shipping reallocate_function`. The gate is load-bearing, not
decorative.

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


LIVENESS = REPO / "crates/synth-synthesis/src/liveness.rs"
GRAPH_ALLOC = REPO / "crates/synth-synthesis/src/graph_alloc.rs"
MARK_BEGIN = "v053-mutation-site:select-pick BEGIN"
MARK_END = "v053-mutation-site:select-pick END"


def plant_exit_contract_mutation():
    """Empty `cfg_exit_observable` — the v0.53 mutation's liveness half.

    Anchored on the function SIGNATURE and brace matching, never on line
    context: the body is replaced wholesale with the empty contract."""
    src = LIVENESS.read_text()
    sig = "pub fn cfg_exit_observable(terminator: &ArmOp) -> BTreeSet<Reg> {"
    at = src.find(sig)
    if at < 0:
        raise SystemExit(
            "FATAL: cfg_exit_observable signature not found — the shared exit "
            "contract moved; re-anchor this oracle"
        )
    body_start = at + len(sig)
    depth, i = 1, body_start
    while depth and i < len(src):
        depth += {"{": 1, "}": -1}.get(src[i], 0)
        i += 1
    if depth:
        raise SystemExit("FATAL: unbalanced braces after cfg_exit_observable")
    mutated = (
        src[:body_start]
        + "\n    // ***L6 MUTATION (v0.53 reproduction): empty the shared exit"
        + "\n    // contract.***\n    let _ = terminator;\n    BTreeSet::new()\n}"
        + src[i:]
    )
    LIVENESS.write_text(mutated)


def plant_select_mutation():
    """Strip the colourer's select to lowest-free — the half that makes the
    emptied contract MANIFEST as a wrong-register rewrite (v0.53 dropped the
    churn bias; the cost-model select's equivalent is dropping the measured
    ranking + preference order). Anchored on the BEGIN/END markers that travel
    with the select decision."""
    src = GRAPH_ALLOC.read_text()
    b = src.find(MARK_BEGIN)
    e = src.find(MARK_END)
    if b < 0 or e < 0 or e <= b:
        raise SystemExit(
            "FATAL: v053-mutation-site markers not found in graph_alloc.rs — "
            "the select moved without its markers; restore them at the new site"
        )
    span_start = src.rfind("\n", 0, b) + 1
    span_end = src.find("\n", e) + 1
    mutated = (
        src[:span_start]
        + "        // ***L6 MUTATION (v0.53 reproduction): drop the"
        + "\n        // measured-cost ranking and the preference order.***"
        + "\n        let _ = (&orig_colour, caller_saved, &mut *occ_cost);"
        + "\n        let pick = (0..k).find(|&c| !used[c]);\n"
        + src[span_end:]
    )
    GRAPH_ALLOC.write_text(mutated)


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

    # ---- MUTATED: v0.53's mutation, re-planted structurally ----------------
    plant_exit_contract_mutation()
    plant_select_mutation()
    try:
        synth = build()
        out = compile_fixture(synth)
    finally:
        rev = run(["git", "checkout", "--"] + TOUCHED)
        if rev.returncode != 0:
            print(rev.stderr, file=sys.stderr)
            raise SystemExit("FATAL: could not RESTORE the mutated files — tree dirty!")

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
