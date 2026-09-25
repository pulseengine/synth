#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^replay-control-1318: ([0-9]+) adversaries REFUSED$/ >= 3
"""RQ-75-REPLAY (#1318) NEGATIVE CONTROL: build the replay adversaries and
require that `falcon_opt_1318_differential.py` REFUSES each of them.

WHY THIS IS A SCRIPT AND NOT A PARAGRAPH. v0.73's gate review defeated the
#1318 step with a 16-line stub; v0.74 repaired that and DISCLOSED, in prose,
that a stub replaying pre-recorded ELFs would still pass. Prose does not go red.
This rebuilds the adversaries from the real compiler on every run, so the claim
"a replay is refused" is re-earned rather than remembered — and so a future
change that weakens the differential turns THIS step red instead of going
unnoticed until someone re-reads a docstring.

Nothing recorded is committed. The objects are produced by the binary under test
at run time and thrown away, which is also why this cannot rot: there is no
fixture to go stale.

TWO ADVERSARIES, because one would leave two of the three mechanisms unproven:

  1. PURE REPLAY — copies the recorded objects with `.text` overwritten by 0xDE
     filler and echoes the recorded warning lines. Compiles nothing at all.
     Caught by the FRESHNESS PROBE: it cannot produce a symbol named with a
     nonce generated after the recording.

  2. DELEGATING REPLAY — forwards anything that is not the #1318 fixture to the
     real compiler, so it PASSES the freshness probe, and replays only the
     fixture. Caught by the DECODE CHECK.

     This one exists because adversary 1 alone proves only the probe. Measured:
     adversary 2 is refused on the `riscv` leg at 0% decode — and NOT on `arm`,
     because `0xDEDE` is a valid Thumb halfword. That asymmetry is disclosed in
     `freshness_probe`'s docstring and is the reason freshness, not decoding, is
     the primary mechanism.

The third mechanism — `declined INTERSECT symbols = {}` — is not reachable from
a replay of self-consistent recordings, so it is driven directly in
`_check_cross_leg` below rather than left unexercised.
"""

from __future__ import annotations

import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
SYNTH = ROOT / "target/debug/synth"
DIFF = ROOT / "scripts/repro/falcon_opt_1318_differential.py"
FIXTURE = ROOT / "scripts/repro/falcon_opt_1318.wat"
BACKENDS = {
    "arm": ["--target", "cortex-m7dp", "--relocatable"],
    "riscv": ["-b", "riscv"],
    "aarch64": ["-b", "aarch64"],
}

PURE = '''#!/usr/bin/env python3
import json, shutil, sys, pathlib
# the VERBATIM recording: real `.text`, so the decode check passes and only the
# freshness probe can catch this.
REC = pathlib.Path(__file__).resolve().parent / "verbatim"
T = json.loads((REC / "table.json").read_text())
if "--version" in sys.argv:
    print("synth 0.0.0-stub"); sys.exit(0)
out = sys.argv[sys.argv.index("-o") + 1] if "-o" in sys.argv else None
for e in T:
    if all(f in sys.argv for f in e["flags"]) and (
            "--allow-skipped-exports" in sys.argv) == (
            "--allow-skipped-exports" in e["flags"]):
        sys.stdout.write(e["stdout"]); sys.stderr.write(e["stderr"])
        if e["obj"] and out:
            shutil.copyfile(REC / e["obj"], out)
        sys.exit(e["rc"])
sys.exit(97)
'''

DELEGATING = '''#!/usr/bin/env python3
import json, shutil, subprocess, sys, pathlib
REC = pathlib.Path(__file__).resolve().parent
REAL = (REC / "real_path.txt").read_text().strip()
T = json.loads((REC / "table.json").read_text())
if "--version" in sys.argv:
    print("synth 0.0.0-stub"); sys.exit(0)
if not any("falcon_opt_1318.wat" in a for a in sys.argv):
    sys.exit(subprocess.run([REAL, *sys.argv[1:]]).returncode)
out = sys.argv[sys.argv.index("-o") + 1] if "-o" in sys.argv else None
for e in T:
    if all(f in sys.argv for f in e["flags"]) and (
            "--allow-skipped-exports" in sys.argv) == (
            "--allow-skipped-exports" in e["flags"]):
        sys.stdout.write(e["stdout"]); sys.stderr.write(e["stderr"])
        if e["obj"] and out:
            shutil.copyfile(REC / e["obj"], out)
        sys.exit(e["rc"])
sys.exit(97)
'''


# Adversary 3: the cold review's A3. Reads the export names out of the .wat it is
# asked to compile and PATCHES them into a recorded object's string table, in
# place, at fixed offsets. Against v0.75's first probe — one export, always
# exactly 26 bytes — this passed the whole CI step. It is kept as the regression
# test for the variable-length fix: with names of differing lengths an in-place
# patch cannot place them all, so the probe must refuse.
PATCHER = '''#!/usr/bin/env python3
import json, re, shutil, sys, pathlib
REC = pathlib.Path(__file__).resolve().parent
T = json.loads((REC / "table.json").read_text())
if "--version" in sys.argv:
    print("synth 0.0.0-stub"); sys.exit(0)
out = sys.argv[sys.argv.index("-o") + 1] if "-o" in sys.argv else None
wat = next((a for a in sys.argv if a.endswith(".wat")), None)
if wat and "falcon_opt_1318" not in wat:
    # the freshness probe. Replay a recorded object, patching the requested
    # names in at FIXED offsets — the attack that worked on the 26-byte nonce.
    want = re.findall(r\'\\(export "([^"]+)"\\)\', pathlib.Path(wat).read_text())
    src = next((e for e in T if e["obj"]), None)
    if not (src and out):
        sys.exit(90)
    raw = bytearray((REC / src["obj"]).read_bytes())
    donor = re.findall(rb"fresh[0-9a-f]{4,16}", bytes(raw)) or re.findall(rb"vbr_[a-z0-9]+", bytes(raw))
    ok = True
    for i, name in enumerate(want):
        nb = name.encode()
        if i < len(donor) and len(donor[i]) == len(nb):
            raw[:] = bytes(raw).replace(donor[i], nb, 1)
        else:
            ok = False           # lengths differ: no in-place patch exists
    pathlib.Path(out).write_bytes(bytes(raw))
    sys.exit(0 if ok else 0)     # exits 0 either way: the GATE must catch it
for e in T:
    if all(f in sys.argv for f in e["flags"]) and (
            "--allow-skipped-exports" in sys.argv) == (
            "--allow-skipped-exports" in e["flags"]):
        sys.stdout.write(e["stdout"]); sys.stderr.write(e["stderr"])
        if e["obj"] and out:
            shutil.copyfile(REC / e["obj"], out)
        sys.exit(e["rc"])
sys.exit(97)
'''

def record(rec: pathlib.Path) -> None:
    """Capture the real compiler's output, then blank every .text with 0xDE."""
    from elftools.elf.elffile import ELFFile

    table = []
    for name, flags in BACKENDS.items():
        for allow in (False, True):
            obj = rec / f"{name}{'-allow' if allow else ''}.o"
            args = [str(SYNTH), "compile", str(FIXTURE), *flags, "--all-exports"]
            if allow:
                args.append("--allow-skipped-exports")
            args += ["-o", str(obj)]
            r = subprocess.run(args, capture_output=True, text=True)
            table.append({"flags": flags + (["--allow-skipped-exports"] if allow else []),
                          "stdout": r.stdout, "stderr": r.stderr,
                          "rc": r.returncode,
                          "obj": obj.name if obj.is_file() else None})
    (rec / "table.json").write_text(json.dumps(table))
    # Keep an UNFILLED copy: adversary 1 replays real `.text`, so the decode
    # check passes and FRESHNESS is the only mechanism that can catch it. Without
    # this, both adversaries were decode-caught and adversary 1 supplied ZERO
    # evidence about the probe — the cold review's M12.
    verbatim = rec / "verbatim"
    verbatim.mkdir(exist_ok=True)
    for p in sorted(rec.glob("*.o")):
        shutil.copy2(p, verbatim / p.name)
    shutil.copy2(rec / "table.json", verbatim / "table.json")
    for p in sorted(rec.glob("*.o")):
        with open(p, "rb") as fh:
            sec = next((s for s in ELFFile(fh).iter_sections()
                        if s.name == ".text"), None)
            if sec is None:
                continue
            off, size = sec.header["sh_offset"], sec.header["sh_size"]
        raw = bytearray(p.read_bytes())
        raw[off:off + size] = b"\xde" * size
        p.write_bytes(bytes(raw))


def run_diff_against(stub: pathlib.Path) -> tuple[int, str]:
    """Run the differential with SYNTH pointed at `stub`, restoring after.

    THE REAL BINARY IS COPIED ASIDE BY `stash_real`, not referenced through
    `target/debug/synth`. An earlier version had the delegating stub read
    `SYNTH.resolve()`, which worked locally ONLY because that path was a SYMLINK
    to a build outside the tree, so `resolve()` escaped the rename below. In CI
    it is the real file: it gets renamed, and the stub ends up invoking ITSELF.
    The step failed there and passed locally — the same "a local oracle run is
    not a CI run" shape this release keeps meeting, this time in the control
    built to catch such things.
    """
    backup = SYNTH.with_suffix(".control-backup")
    SYNTH.rename(backup)
    try:
        SYNTH.symlink_to(stub)
        r = subprocess.run([sys.executable, str(DIFF)], cwd=ROOT,
                           capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr
    finally:
        if SYNTH.is_symlink() or SYNTH.exists():
            SYNTH.unlink()
        backup.rename(SYNTH)


def stash_real(rec: pathlib.Path) -> pathlib.Path:
    """A copy of the compiler under test, at a path the swap cannot disturb."""
    dst = rec / "real_synth"
    shutil.copy2(SYNTH.resolve(), dst)
    dst.chmod(0o755)
    return dst


def _check_cross_leg(fails: list[str]) -> None:
    """Drive `declined INTERSECT symbols = {}` directly.

    A replay of SELF-CONSISTENT recordings never contradicts itself, so this
    mechanism is unreachable from either adversary. Driving it here is what
    stops it being dead code — the v0.57 lesson, and the reason v0.74's own
    INV2 sat documented-but-unimplemented for a release.
    """
    sys.path.insert(0, str(ROOT / "scripts/repro"))
    import falcon_opt_1318_differential as D

    with tempfile.TemporaryDirectory() as td:
        obj = os.path.join(td, "arm.o")
        r = subprocess.run(
            [str(SYNTH), "compile", str(FIXTURE), *BACKENDS["arm"],
             "--all-exports", "--allow-skipped-exports", "-o", obj],
            capture_output=True, text=True)
        if r.returncode != 0:
            fails.append("cross-leg: could not build a real arm object to drive it")
            return
        try:
            D.inspect_object("arm", obj, ["vbr_i32"],
                             declined=["vbr_i64", "vbr_f32", "vbr_f64"])
            print("  ok   cross-leg: the honest arrangement passes")
        except SystemExit as e:
            fails.append(f"cross-leg: honest arrangement REFUSED — {str(e)[:120]}")
        try:
            D.inspect_object("arm", obj, [], declined=["vbr_i32"])
            fails.append("cross-leg: a declined export present in the symtab was "
                         "NOT caught")
        except SystemExit:
            print("  ok   cross-leg: declined-yet-present is CAUGHT")


def main() -> int:
    if not SYNTH.is_file():
        print(f"FAIL: {SYNTH} not built")
        return 1
    fails: list[str] = []
    refused = 0
    with tempfile.TemporaryDirectory(prefix="replay1318-") as td:
        rec = pathlib.Path(td)
        record(rec)
        (rec / "real_path.txt").write_text(str(stash_real(rec)))
        # RQ-75-REPLAY round 1 (the cold review's M12): each adversary names the
        # MECHANISM that must catch it, and the refusal is matched against that
        # mechanism. The first version asserted only THAT a refusal happened, so
        # commenting out `freshness_probe()` entirely left this green — both
        # adversaries were decode-caught on the riscv leg, and adversary 1
        # supplied ZERO evidence about the probe it existed to prove.
        MECHANISM_NEEDLE = {
            # the probe's own refusal text, per its two failure modes
            "freshness": ("does not name", "could not compile a"),
            "decode": ("decodes as",),
        }
        for label, src, expect in (
                ("pure replay, real .text (freshness is the only catcher)",
                 PURE, "freshness"),
                ("delegating replay, 0xDE .text (decode is the only catcher)",
                 DELEGATING, "decode"),
                ("fixed-offset strtab patcher (the A3 attack)",
                 PATCHER, "freshness"),
        ):
            stub = rec / f"stub_{expect}_{abs(hash(label)) % 9973}.py"
            stub.write_text(src)
            stub.chmod(0o755)
            rc, out = run_diff_against(stub)
            refusal = next((l.strip() for l in out.splitlines()
                            if "REFUSE" in l), "")
            if rc == 0:
                fails.append(f"{label}: the differential PASSED a replay "
                             f"(rc=0) — the gate is inert again")
                continue
            needles = MECHANISM_NEEDLE[expect]
            if not any(n in refusal for n in needles):
                fails.append(
                    f"{label}: refused, but by the WRONG MECHANISM. Expected "
                    f"{expect} (one of {needles}); got {refusal[:140]!r}. A "
                    f"refusal from another check is not evidence about the one "
                    f"this adversary exists to prove")
                continue
            refused += 1
            print(f"  ok   {label} REFUSED by {expect}")
            print(f"       {refusal[:110]}")
        _check_cross_leg(fails)

    for f in fails:
        print(f"  FAIL {f}")
    # The machine-readable floor. `oracle_run.py` reads this count, so a run
    # that quietly stopped building adversaries is VACUOUS rather than green —
    # the same anti-vacuity shape the rest of this family uses, and the reason
    # this script does NOT declare `# ci-checks: none`.
    print(f"replay-control-1318: {refused} adversaries REFUSED")
    print(f"replay-control-1318: {len(fails)} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
