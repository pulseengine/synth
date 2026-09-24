#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 3
"""RQ-73-FALCONFIXTURE (#1318): a value-carrying branch at FLOAT type is a loud
decline on ARM and RISC-V, and it is 6 of the 7 declines in the reporter's
`opt.wasm`.

WHY THIS EXISTS. #1318 has been open since 2026-09-17 with its residual living
in an issue attachment, which v0.70's RQ-70-FALCONCORPUS already named as the
defect one level up: the CLASS had fixtures, the REPORTER'S MODULE did not, so
the number could not be re-derived from this repository. It can now.

PROVENANCE, and it refutes the scoping this lane opened with. The planning
artifact said the module "is an ISSUE ATTACHMENT and not in this repository"
and made step (a) "ask the reporter to re-test". `errors.zip` on #1318 contains
`opt.wasm` and `fused.wasm` THEMSELVES, so it was measured here instead.
At v0.72.0, with the reporter's own command line:

    fused.wasm   rc=0, 0 of 26 skipped          (still clean, as at v0.70.0)
    opt.wasm     rc=1, 7 of 17 skipped
                 -> 1x #1069  (the `controller@0.10.0#step` export)
                 -> 6x GI-FPU-002 (func_4, func_5, func_8, func_10,
                                   func_11, func_12)

Unchanged from the v0.70.0 status, which is consistent with both emit sites
being untouched between v0.70.0 and v0.72.0 (`git log -L` over the exact line
ranges; positive control on the v0.72 island code correctly reported 2 commits).

HOW THE SIX WERE REDUCED. Each was extracted from `opt.wasm` into its own
module — stubbing callees, adding the one mutable global where needed — and
each still declined with `GI-FPU-002`. All six contain a `block` with an f32
result. The minimal module carrying only that shape declines identically, which
is what `falcon_opt_1318.wat` commits. The LIMIT of that claim is stated
plainly: containing the shape is not proof it is the trigger in each of the six
(a function can decline for more than one reason); the minimal case shows the
shape is SUFFICIENT on its own, which is what this oracle pins.

A DISCARDED HYPOTHESIS, recorded so it is not re-tried: `i32.reinterpret_f32` /
`f32.reinterpret_i32` are all over `func_5`, but a module containing only those
compiles cleanly everywhere. Not the trigger.

WHY THESE ARE `EXPECTED_DECLINES` AND NOT `KNOWN`. The pin-debt population's
stated criterion (CLAUDE.md) excludes decline pins by design — "a loud refusal
is reach, not silent wrongness". Every cell here is a loud refusal on input
wasmtime accepts and executes, so these pins are REACH debt, not wrongness
debt, and they correctly do not enter `known_open_pins`. Filing them as `KNOWN`
would have made this lane pay a ratchet waiver for evidence of a decline, and
would have overstated the silent-miscompile count the v0.73 headline rests on.

THE DIAGNOSTIC IS THE SECOND FINDING. ARM compiles the i32 form, and declines
the i64 form with a message that says exactly what is unsupported. The f32/f64
form yields "an integer operation peeked an f32 (VFP) stack value — invalid
wasm or an unlowered float op reached the integer path", which names the wrong
subsystem and reads as though the input might be malformed. It is not: every
export in the fixture is validated and executed by wasmtime. That mismatch is
why six declines in a real flight-control module were never connected to a
known limitation. AArch64 compiles all four, so the capability exists here.

Stated as measured and no further: the SAME shape declines at i64 with the
`#509` message and at f32 with an integer-path message. Whether both raise
sites reduce to one underlying limitation is NOT shown, and no such claim is
made.

A pin that moves in EITHER direction is red. A fix that makes `vbr_f32`
compile must move this table in the same PR that lands it.
"""

from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
FIXTURE = ROOT / "scripts/repro/falcon_opt_1318.wat"
SYNTH = ROOT / "target/debug/synth"

BACKENDS = {
    "arm": ["--target", "cortex-m7dp", "--relocatable"],
    "riscv": ["-b", "riscv"],
    "aarch64": ["-b", "aarch64"],
}
EXPORTS = ["vbr_i32", "vbr_i64", "vbr_f32", "vbr_f64"]

# (export, backend) -> None for "must compile", else a NEEDLE that must appear
# in that function's decline. Exact in both directions: an unexpected decline
# AND an unexpected success are both red.
EXPECTED_DECLINES: dict[tuple[str, str], str | None] = {
    # The CONTROL. i32 compiles everywhere. If any of these ever declines, this
    # oracle has stopped discriminating and `main` refuses rather than passing.
    ("vbr_i32", "arm"): None,
    ("vbr_i32", "riscv"): None,
    ("vbr_i32", "aarch64"): None,
    # AArch64 carries a branch value at every type — the capability exists in
    # this codebase, which is what makes the ARM/RISC-V cells a GAP and not a
    # design boundary.
    ("vbr_i64", "aarch64"): None,
    ("vbr_f32", "aarch64"): None,
    ("vbr_f64", "aarch64"): None,
    # ARM: named and accurate at i64; integer-path message at float.
    ("vbr_i64", "arm"): "#509",
    ("vbr_f32", "arm"): "GI-FPU-002",
    ("vbr_f64", "arm"): "GI-FPU-002",
    # RISC-V: the sibling gap, different wording.
    ("vbr_i64", "riscv"): "RISC-V selector",
    ("vbr_f32", "riscv"): "RISC-V selector",
    ("vbr_f64", "riscv"): "RISC-V selector",
}


def compile_for(backend: str, obj: str) -> dict[str, str]:
    """export -> decline text ('' when it compiled).

    v0.73 cold review, gate finding F2: this used to infer "compiles" from the
    ABSENCE of a `warning: skipping` line, never read the return code, and
    wrote the object to /dev/null so there was nothing to inspect. A 14-line
    shell stub that printed the six expected warnings and exited 3 passed the
    whole CI step — floor included, because the `compiles >= 3` floor counts
    INVOCATIONS, not successful compilations.

    Both halves are now checked against the compiler's own behaviour: the exit
    status must agree with whether anything was skipped, and when nothing was
    skipped an object must actually exist.
    """
    out = subprocess.run(
        [str(SYNTH), "compile", str(FIXTURE), *BACKENDS[backend],
         "--all-exports", "-o", obj],
        capture_output=True, text=True,
    )
    blob = out.stdout + out.stderr
    declines = {}
    for line in blob.splitlines():
        if not line.startswith("warning: skipping function"):
            continue
        name = line.split("'")[1] if "'" in line else "?"
        declines[name.rsplit("#", 1)[-1]] = line

    # The compiler's OWN verdict must agree with what we read off its output.
    if declines and out.returncode == 0:
        raise SystemExit(
            f"REFUSE {backend}: {len(declines)} function(s) were skipped but "
            f"synth exited 0. The decline text and the exit status disagree, "
            f"so one of them is not the compiler's real behaviour."
        )
    if not declines:
        if out.returncode != 0:
            raise SystemExit(
                f"REFUSE {backend}: synth exited {out.returncode} while "
                f"reporting NO skipped function. 'Compiles' inferred from an "
                f"absent warning line is exactly the reading a broken or "
                f"stubbed compiler satisfies."
            )
        if not os.path.isfile(obj) or os.path.getsize(obj) == 0:
            raise SystemExit(
                f"REFUSE {backend}: synth exited 0 and skipped nothing, but "
                f"produced no object at {obj}. Nothing was compiled."
            )
    return declines


def main() -> int:
    if not SYNTH.is_file():
        print(f"FAIL: {SYNTH} not built — run `cargo build -p synth-cli`")
        return 1
    if not FIXTURE.is_file():
        print(f"FAIL: {FIXTURE} missing")
        return 1

    checked = 0
    bad: list[str] = []
    print(f"{'export':<10}{'backend':<10}{'observed':<12}pin")
    td = tempfile.mkdtemp(prefix="falcon1318-")
    for backend in BACKENDS:
        declines = compile_for(backend, os.path.join(td, f"{backend}.o"))
        for export in EXPORTS:
            pin = EXPECTED_DECLINES[(export, backend)]
            got = declines.get(export)
            checked += 1
            obs = "decline" if got else "compiles"
            print(f"{export:<10}{backend:<10}{obs:<12}{pin or 'compiles'}")
            if pin is None and got:
                bad.append(f"{export}/{backend}: pinned to COMPILE but declined: {got}")
            elif pin is not None and not got:
                bad.append(
                    f"{export}/{backend}: pinned to decline with {pin!r} but it "
                    f"COMPILED — if this is a fix, move the pin in this PR"
                )
            elif pin is not None and pin not in got:
                bad.append(f"{export}/{backend}: expected {pin!r} in: {got}")

    # ANTI-VACUITY. Two independent ways this oracle could pass while measuring
    # nothing, both refused rather than reported.
    if checked == 0:
        print("FAIL: classified 0 cells — nothing was measured")
        return 1
    n_declines = sum(1 for v in EXPECTED_DECLINES.values() if v is not None)
    if n_declines == 0:
        print("FAIL: no cell is pinned to decline — this oracle cannot discriminate")
        return 1

    print(f"\n#1318 CHECKS={checked}/12 (export,backend) cells; "
          f"{n_declines} pinned declines, {checked - n_declines} pinned compiles")
    if bad:
        for b in bad:
            print(f"REFUSE: {b}")
        print("RESULT: FAIL — a pin moved in one direction or the other")
        return 1
    print("RESULT: PASS — the value-carrying-branch matrix is exactly as pinned")
    return 0


if __name__ == "__main__":
    sys.exit(main())
