#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 6
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

    fused.wasm   rc=0, 0 of 21 skipped          (still clean, as at v0.70.0)
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

from elftools.elf.elffile import ELFFile

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


# (v0.74, RQ-74-STUBPROOF) What each leg must actually EMIT. A stub can print
# any text and exit any code; it cannot emit an ELF of the right machine whose
# symbol table names the exports that did not decline.
EXPECTED_MACHINE = {"arm": "EM_ARM", "riscv": "EM_RISCV", "aarch64": "EM_AARCH64"}

# Capstone modes per leg, for the decode check below.
DECODE_MODE = {
    "arm": ("CS_ARCH_ARM", "CS_MODE_THUMB"),
    "riscv": ("CS_ARCH_RISCV", "CS_MODE_RISCV32"),
    "aarch64": ("CS_ARCH_ARM64", "CS_MODE_ARM"),
}


def freshness_probe(backend: str, tmpdir: str) -> None:
    """REFUSE unless the binary under test compiles a module it has NEVER SEEN.

    RQ-75-REPLAY (#1318), v0.75 — THE DEFEAT THIS CLOSES. v0.74 repaired the
    null-stub hole by asking what the emitted file IS: ELF magic, the right
    `e_machine` per leg, a non-empty `.text`, a symbol per non-declined export.
    It disclosed that this still never asks what the file CONTAINS, and that a
    stub replaying PRE-RECORDED ELFs therefore passes forever.

    That was not a hypothesis. Built and measured at this lane's cut: a short
    script that compiles NOTHING, replays the recorded objects
    with `.text` entirely overwritten by 0xDE filler, and echoes the recorded
    warning lines, produced rc=0, `CHECKS=12/12` and
    `RESULT: PASS — the value-carrying-branch matrix is exactly as pinned`.

    A DECODE ALONE DOES NOT CLOSE IT, and the measurement is why this probe
    exists instead. Disassembling `.text` and requiring it to decode catches the
    filler on two legs and NOT on the third:

        leg        real code   0xDE filler
        arm         1.00        1.00        <- blind
        riscv       1.00        0.00
        aarch64     1.00        0.00

    `0xDEDE` decodes as `UDF #0xde` — a PERMANENTLY UNDEFINED Thumb encoding
    that capstone nevertheless decodes and counts, which is exactly why a
    decode-COVERAGE metric is blind to it. "Valid" was the wrong word: the point
    is that an undefined encoding still decodes. So the ARM leg — the one this
    issue was reported against — scores filler at 1.00. A decode check shipped as "the
    fix" would have closed two legs and left the reported one open while reading
    as complete.

    So the primary mechanism is FRESHNESS, which is arch- and
    encoding-independent: compile a module generated NOW, exporting a symbol
    whose name carries a random nonce, and require that symbol in the emitted
    object. A recording made before the nonce existed cannot contain it, so no
    replay passes however faithful its bytes. Verified present on all three legs
    with the real compiler.
    """
    import secrets
    from elftools.elf.elffile import ELFFile

    # RQ-75-REPLAY round 1 (v0.75) — THE FIRST VERSION OF THIS PROBE WAS
    # DEFEATED, and the sentence it shipped was FALSE. It exported ONE symbol
    # named `freshness_` + `token_hex(8)`, and asserted "a nonce chosen for THIS
    # run cannot appear in a recording". It can: that name is ALWAYS EXACTLY 26
    # bytes, so the nonce is a FIXED-LENGTH byte patch into a recorded
    # `.strtab` — no offsets move, no ELF library needed, no compiler needed.
    # The cold review built it: a VERBATIM replay (real `.text`, so the decode
    # check reads 1.00 on every leg) plus a 16-hex byte patch passed the entire
    # CI step, `CHECKS=12/12`, `RESULT: PASS`.
    #
    # So freshness now varies in ways a byte patch cannot follow:
    #   * the symbol names are VARIABLE LENGTH (4..16 hex chars), so patching
    #     one in place would move every following offset in the string table;
    #   * the NUMBER of exports varies (2..5), so a recording of one module
    #     cannot supply the symbol set another run demands;
    #   * every name must be present, so a patch must land all of them.
    #
    # This does not claim to be unforgeable — an adversary that correctly
    # REBUILDS a string table and its offsets defeats it, and that is stated
    # rather than left implied. It claims that satisfying it requires
    # constructing an ELF rather than patching bytes at fixed positions.
    n_syms = 2 + secrets.randbelow(4)
    syms = []
    for _ in range(n_syms):
        width = 4 + secrets.randbelow(13)          # 4..16 hex chars
        syms.append(f"fresh{secrets.token_hex(8)[:width]}")
    syms = sorted(set(syms))
    tag = secrets.token_hex(4)
    body = "".join(
        f'  (func (export "{sy}") (result i32) (i32.const {i + 1}))\n'
        for i, sy in enumerate(syms))
    wat = os.path.join(tmpdir, f"{backend}-{tag}.wat")
    with open(wat, "w", encoding="utf-8") as fh:
        fh.write(f"(module\n{body})\n")
    obj = os.path.join(tmpdir, f"{backend}-{tag}.o")
    r = subprocess.run(
        [str(SYNTH), "compile", wat, *BACKENDS[backend], "--all-exports",
         "-o", obj],
        capture_output=True, text=True,
    )
    if r.returncode != 0 or not os.path.isfile(obj):
        raise SystemExit(
            f"REFUSE {backend}: the binary under test could not compile a "
            f"{len(syms)}-function module generated for this run "
            f"(rc={r.returncode}). It is not a working compiler for this leg, "
            f"whatever it printed about the fixture. "
            f"{(r.stderr or r.stdout)[:200]}"
        )
    with open(obj, "rb") as fh:
        elf = ELFFile(fh)
        names = set()
        for sec in elf.iter_sections():
            if sec.header["sh_type"] == "SHT_SYMTAB":
                names |= {s.name for s in sec.iter_symbols() if s.name}
    absent = [sy for sy in syms if sy not in names]
    if absent:
        raise SystemExit(
            f"REFUSE {backend}: compiled a module exporting {syms} and the "
            f"emitted object does not name {absent}. Observed: "
            f"{sorted(names)}. The names and their COUNT are chosen for this "
            f"run, at lengths a fixed-offset byte patch cannot follow, so this "
            f"is what a replay fails (RQ-75-REPLAY)."
        )


def decode_text(backend: str, data: bytes) -> float:
    """Fraction of `.text` capstone can decode. See freshness_probe for why
    this is a SECONDARY check: the ARM leg decodes 0xDE filler at 1.00.

    A MISSING capstone is LOUD, not a skip. Swallowing the ImportError and
    returning 1.0 would make this check disappear in exactly the environment
    where nobody notices — and it already bit once: the `rq66-unwatched-oracle`
    job runs this oracle and its `pip install` did not list capstone, so the
    first push red there and NOT in the jobs that do. A dependency a gate needs
    belongs in the job that runs it, not behind a try/except."""
    try:
        import capstone
    except ImportError as ex:  # pragma: no cover - environment, not logic
        raise SystemExit(
            f"REFUSE {backend}: capstone is not importable ({ex}), so the "
            f".text decode check cannot run. Add capstone to this job's "
            f"`pip install` rather than letting the check vanish silently."
        ) from ex

    arch, mode = DECODE_MODE[backend]
    md = capstone.Cs(getattr(capstone, arch), getattr(capstone, mode))
    md.detail = False
    covered = sum(i.size for i in md.disasm(data, 0x1000))
    return covered / len(data) if data else 0.0


def inspect_object(backend: str, obj: str, compiled: list[str],
                   declined: list[str] | None = None) -> None:
    """REFUSE unless `obj` is a real ELF for this leg naming every compiled export.

    (v0.74, RQ-74-STUBPROOF) v0.73's round-2 gate review replaced
    `target/debug/synth` with a 16-line python script that printed the six
    expected `warning: skipping` lines and exited 3, and wrote a ONE-BYTE file
    and exited 0 for the aarch64 leg. The oracle returned rc=0, "CHECKS=12/12",
    "RESULT: PASS", and `measured=3` — verdict-identical to the real compiler,
    and the full CI step passed too. Reproduced again at the v0.74 cut before
    this was written.

    v0.73 round 1 had already added an exit-status cross-check and an
    object-exists/non-empty check; the stub satisfied BOTH. The gap was that
    nothing ever asked what the file IS.

    WHAT THIS STILL CANNOT SEE (v0.74 cold review round 1, disclosed here
    rather than left to be rediscovered):

      * IT ASKS WHAT THE FILE IS, NEVER WHAT IT CONTAINS OR WHO PRODUCED IT.
        A 30-line script that copies three PRE-RECORDED ELFs — right machine,
        right symbols, `.text` entirely overwritten with 0xDE filler — and
        prints the canned warning lines passes the whole step: rc=0,
        CHECKS=12/12, RESULT: PASS, and both CI greps. A recorded artifact
        replays forever. Closing it needs the emitted CODE checked (a decode,
        or an execution differential), not another header field.
      * THE TWO INVOCATIONS ARE NEVER CROSS-CHECKED. `inspect_object` asserts
        `compiled SUBSET-OF symbols`; it never asserts
        `declined INTERSECT symbols = {}`. An object whose symtab contains the
        three exports leg 1 just reported as DECLINED passes.
      * THE FLOOR MOVE 3 -> 6 BOUGHT NOTHING. `oracle_run`'s `mode=compiles`
        counts subprocess INVOCATIONS, so doubling the invocations doubled the
        floor and a stub satisfies both. The floor proves the step ran, not
        that anything compiled.
    """
    if not os.path.isfile(obj) or os.path.getsize(obj) == 0:
        raise SystemExit(
            f"REFUSE {backend}: no object at {obj} to inspect. With "
            f"--allow-skipped-exports every leg emits one, so an absent object "
            f"is the compiler failing, not a decline."
        )
    with open(obj, "rb") as fh:
        head = fh.read(4)
        if head != b"\x7fELF":
            raise SystemExit(
                f"REFUSE {backend}: {obj} is not an ELF (magic {head!r}). "
                f"'It compiled' was inferred from text on stdout; the artifact "
                f"says otherwise."
            )
        fh.seek(0)
        elf = ELFFile(fh)
        machine = elf.header.e_machine
        want = EXPECTED_MACHINE[backend]
        if machine != want:
            raise SystemExit(
                f"REFUSE {backend}: object reports e_machine={machine}, "
                f"expected {want}. The leg compiled for the wrong target, or "
                f"the object is not this leg's."
            )
        text = next((s for s in elf.iter_sections() if s.name == ".text"), None)
        # RQ-75-REPLAY: capture the bytes while the file is still OPEN.
        # pyelftools reads section data lazily, so `.data()` after the `with`
        # block raises KeyError from its own lazy container — which is how the
        # decode check first appeared to break the real compiler.
        text_bytes = text.data() if text is not None else b""
        if text is None or text.data_size == 0:
            raise SystemExit(
                f"REFUSE {backend}: object has no non-empty .text. An ELF with "
                f"no code is not a compile."
            )
        names = set()
        for sec in elf.iter_sections():
            if sec.header["sh_type"] == "SHT_SYMTAB":
                names |= {sym.name for sym in sec.iter_symbols() if sym.name}
    # RQ-75-REPLAY (#1318): CROSS-CHECK THE TWO INVOCATIONS. v0.74 asserted
    # `compiled SUBSET-OF symbols` and never `declined INTERSECT symbols = {}`,
    # so an object whose symtab carried the very exports leg 1 had just reported
    # as DECLINED passed. The two legs were never compared with each other.
    if declined:
        contradiction = sorted(set(declined) & names)
        if contradiction:
            raise SystemExit(
                f"REFUSE {backend}: {contradiction} were reported DECLINED on "
                f"the plain run, and the --allow-skipped-exports object names "
                f"them anyway. The two invocations contradict each other, so "
                f"one of them is not this compiler's behaviour "
                f"(RQ-75-REPLAY)."
            )
    # And the code itself must decode. SECONDARY, deliberately: measured at this
    # lane's cut, 0xDE filler decodes at 1.00 on the ARM leg (0xDEDE is a valid
    # Thumb halfword) and 0.00 on riscv/aarch64. So this closes two legs and the
    # freshness probe is what closes the class.
    ratio = decode_text(backend, text_bytes)
    if ratio < 0.90:
        raise SystemExit(
            f"REFUSE {backend}: only {ratio:.0%} of .text decodes as "
            f"{backend} instructions. An ELF whose code section is not code is "
            f"not a compile (RQ-75-REPLAY)."
        )
    missing = [e for e in compiled if e not in names]
    if missing:
        raise SystemExit(
            f"REFUSE {backend}: {missing} did not decline, so each must appear "
            f"in the object's symbol table, and does not. Observed symbols: "
            f"{sorted(names)}. This is the CONTROL half — on arm and riscv "
            f"something always declines, so before v0.74 the compiled cells "
            f"were inferred purely from the ABSENCE of a warning line and no "
            f"artifact was inspected at all."
        )


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

    # (v0.74, RQ-74-STUBPROOF) The object check above is REACHABLE ONLY when
    # nothing declined — and on arm and riscv something ALWAYS declines (three
    # pinned cells each), so for those legs it was dead code and the i32
    # CONTROL cells rested on an absent warning line. #952 makes the plain run
    # emit no object at all when an export is skipped, which is why the check
    # was written that way rather than carelessly.
    #
    # So compile a SECOND time with --allow-skipped-exports, which #952's own
    # message advertises: it returns 0 and emits the object for the subset that
    # DID compile. Measured on this fixture: arm goes rc=1/no object ->
    # rc=0/447-byte object carrying `.text` and the symbol `vbr_i32`.
    insp = os.path.join(os.path.dirname(obj), f"{backend}-inspect.o")
    out2 = subprocess.run(
        [str(SYNTH), "compile", str(FIXTURE), *BACKENDS[backend],
         "--all-exports", "--allow-skipped-exports", "-o", insp],
        capture_output=True, text=True,
    )
    if out2.returncode != 0:
        raise SystemExit(
            f"REFUSE {backend}: --allow-skipped-exports exited "
            f"{out2.returncode}. That flag exists precisely so a partial "
            f"object IS produced, so a non-zero exit here is the compiler "
            f"failing rather than declining."
        )
    inspect_object(backend, insp, [e for e in EXPORTS if e not in declines],
                   declined=list(declines))
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
        # RQ-75-REPLAY: prove the binary under test compiles something it has
        # never seen BEFORE trusting anything it says about the fixture.
        freshness_probe(backend, td)
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
