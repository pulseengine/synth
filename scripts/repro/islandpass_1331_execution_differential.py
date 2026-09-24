#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 15
"""RQ-73-ISLANDPASS (#1331): the EXECUTION gate a literal-island fixed point owes.

WHY THIS FILE EXISTS, AND WHY IT IS WRITTEN TO ACTIVATE ITSELF.

v0.72 made 4 KB+ functions compile by placing literal pools inline. Branch
offsets are byte-resolved BEFORE the encode loop, so an island inserted between
a branch and its target moves the target and not the branch. v0.72 therefore
REFUSES such placements, which is correct and is why the fixture here still
declines. Making it compile needs a real fixed point — islands change sizes,
which change positions, which change which branches need 32-bit encodings,
which change sizes again (LLVM's ARMConstantIslandPass shape).

The gating rule is that the oracle lands FIRST. But the shape this oracle must
police CANNOT BE EXECUTED TODAY: it does not compile. An oracle that only
asserts "this still refuses" would go green forever and would be silent on the
day the refusal is replaced by wrong bytes — which is precisely the transition
that produced v0.72's two silent miscompiles.

So this oracle has TWO STATES and switches on the compiler's own behaviour:

  REFUSED (today)  assert the decline is the PINNED #345 message. Nothing else
                   is asserted, because nothing else can be.
  COMPILES (after  assert, and REQUIRE: (1) the emitted object satisfies the
  the pass)        island invariants, and (2) every exported call is BIT-EXACT
                   against wasmtime. Compiling is what ARMS the strong half.

That is the property that makes it non-vacuous across the change: the pass
cannot land and leave this file trivially green, because the very act of
compiling is what turns the execution requirement on.

WHAT v0.72's EXISTING DIFFERENTIAL COULD NOT SEE, and why this fixture differs.
Its one islanded module "had no calls and one literal". Both omissions were
load-bearing — the two miscompiles were:

    R_ARM_THM_CALL@0x1014 -> hw1=0xe002   the island's own `b.n +8`, not a BL
    LDR.W lit@0x1010 imm12=0              the patch landed INSIDE the island

A module with no `call` carries no `R_ARM_THM_CALL` to get wrong, and a module
with one literal cannot show a patch landing in the wrong pool. The fixture
here has a direct call INSIDE the spanned region and THREE distinct literals,
one before the span, one inside it, one after.

NOT A SUBSTITUTE FOR `island_offset_invariant_345.py`. That reads invariants off
every emitted object in the corpus and is the broad net. This one is deep rather
than broad: one module, executed. Its own docstring records the gap this closes
— an invariant check cannot see a branch that is mis-targeted but still lands on
an instruction boundary, because such a target IS in the instruction-start set.
Only running it can.
"""

import os
import subprocess
import sys
import tempfile

SYNTH = os.environ.get("SYNTH_BIN", "./target/debug/synth")
REPRO = os.path.dirname(os.path.abspath(__file__))
# (v0.74, RQ-74-ISLANDREACH) v0.73 ran ONE fixture, and v0.73's round-2 gate
# review showed why that matters: mutating every local branch target forward by
# one WHOLE instruction — so each target stays a legal instruction start — was
# MISSED by `island_offset_invariant_345.py`, by `sc5_postisland_345.py` and by
# `litpool_islands_345_differential.py`, and CAUGHT only here. Re-measured at the
# v0.74 cut: 3 MISSED, this one CAUGHT (1/5 args bit-exact).
#
# So the whole class rests on this file, and it rested on a single span shape:
# a forward `br_if` out of one block. These two are NEW and vary the shape —
# a BACKWARD branch (loop latch), where the island lands between the target and
# the branch rather than after it, and a branch out of a NESTED block, where the
# island is placed at a different block depth. Both are generated, with
# provenance, by scripts/repro/gen_islandpass_1331.py.
FIXTURES = (
    os.path.join(REPRO, "islandpass_1331_spanning.wat"),
    os.path.join(REPRO, "islandpass_1331_backspan.wat"),
    os.path.join(REPRO, "islandpass_1331_nested.wat"),
)
# compile_once() and execute() read this module global; main() rebinds it per
# fixture rather than threading it through, so the two helpers stay unchanged.
FIXTURE = FIXTURES[0]
ARGS = ["--target", "cortex-m7", "--relocatable", "--all-exports",
        "--native-pointer-abi"]

# The pinned decline. Exact in both directions: if the message CHANGES without
# the module compiling, that is a different refusal and this gate must say so.
PINNED_REFUSAL = "LdrSym literal pool out of range (#345)"

# Arguments the fixture is exercised with. 0 does NOT take the spanning branch
# (so the call and the second literal execute); non-zero DOES take it.
ARGVALS = (0, 1, 2, 9, 0x7FFFFFFF)


def compile_once(obj):
    return subprocess.run([SYNTH, "compile", FIXTURE, *ARGS, "-o", obj],
                          capture_output=True, text=True)


def island_invariants(obj):
    """INV1: every R_ARM_THM_CALL offset lands on a BL (hw1 & 0xF800 == 0xF000).

    INV2 IS NOT IMPLEMENTED HERE, and this docstring used to claim it was.
    (v0.74 cold review round 1.) `reloc_offsets` is built at the top of this
    function and never read — `grep -n reloc_offsets` returns exactly two lines,
    the assignment and the `.add`, and no use. A gate's docstring asserting a
    check it does not perform is this release's own subject pointed inward, so
    it is corrected rather than quietly deleted.

    What DOES cover the intent, partially: `execute()` refuses unless at least
    three pool relocations resolved (`nrel < 3`), which is why the gap went
    unnoticed. A real per-literal INV2 is a v0.75 candidate; it is not claimed
    here."""
    import struct

    from elftools.elf.elffile import ELFFile

    problems = []
    e = ELFFile(open(obj, "rb"))
    text = e.get_section_by_name(".text").data()
    rel = e.get_section_by_name(".rel.text")
    THM_CALL, ABS32 = 10, 2
    reloc_offsets = set()
    ncall = 0
    if rel is not None:
        for r in rel.iter_relocations():
            t, off = r["r_info_type"], r["r_offset"]
            if t == ABS32:
                reloc_offsets.add(off)
            if t == THM_CALL:
                ncall += 1
                (hw1,) = struct.unpack_from("<H", text, off)
                if hw1 & 0xF800 != 0xF000:
                    problems.append(
                        f"INV1 R_ARM_THM_CALL@0x{off:x} -> hw1=0x{hw1:04x}, not a BL "
                        f"— the reloc was recorded at a pre-island offset")
    if ncall == 0:
        problems.append("INV1 VACUOUS: the object carries no R_ARM_THM_CALL, so the "
                        "call-inside-the-span case was not exercised at all")
    return problems, ncall


def execute(obj):
    """Bit-exact against wasmtime. Harness shared with the other
    --native-pointer-abi differentials in this directory."""
    import struct

    import wasmtime
    from elftools.elf.elffile import ELFFile
    from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
    from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_R0,
                                   UC_ARM_REG_R11, UC_ARM_REG_SP)

    ABS32 = 2
    BASES = {".text": 0x10000, ".data": 0x60000, ".bss": 0x40000}
    MAPSZ, RETPAD = 0x20000, 0x90000
    problems = []

    e = ELFFile(open(obj, "rb"))
    secname = {i: s.name for i, s in enumerate(e.iter_sections())}
    text = bytearray(e.get_section_by_name(".text").data())
    dsec, bsec = e.get_section_by_name(".data"), e.get_section_by_name(".bss")
    data = bytearray(dsec.data()) if dsec is not None else bytearray()
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: (s["st_shndx"], s["st_value"]) for s in symtab.iter_symbols()}

    rel, nrel = e.get_section_by_name(".rel.text"), 0
    if rel is not None:
        for rr in rel.iter_relocations():
            if rr["r_info_type"] != ABS32:
                continue
            sym = symtab.get_symbol(rr["r_info_sym"])
            shndx, val = syms[sym.name]
            sec = secname.get(shndx, ".data")
            (add,) = struct.unpack_from("<I", text, rr["r_offset"])
            struct.pack_into("<I", text, rr["r_offset"],
                             (BASES.get(sec, BASES[".data"]) + val + add) & 0xFFFFFFFF)
            nrel += 1
    # R_ARM_THM_CALL: patch the BL in place. The fixture has a direct call
    # INSIDE the spanned region — that is the whole point of it — and a harness
    # that resolves only ABS32 leaves `bl #0` branching to the next instruction.
    # The first version of this file did exactly that and reported a CORRECT
    # compiler as a miscompile (`big(0)` wrong, the other four args bit-exact,
    # because only the fall-through path reaches the call). A differential is
    # only as good as its own link step.
    THM_CALL = 10
    ncall = 0
    if rel is not None:
        for rr in rel.iter_relocations():
            if rr["r_info_type"] != THM_CALL:
                continue
            sym = symtab.get_symbol(rr["r_info_sym"])
            shndx, val = syms[sym.name]
            off = rr["r_offset"]
            target = BASES[secname.get(shndx, ".text")] + (val & ~1)
            delta = target - (BASES[".text"] + off + 4)
            S = (delta >> 24) & 1
            i1, i2 = (delta >> 23) & 1, (delta >> 22) & 1
            j1, j2 = (~i1 ^ S) & 1, (~i2 ^ S) & 1
            hw1 = 0xF000 | (S << 10) | ((delta >> 12) & 0x3FF)
            hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | ((delta >> 1) & 0x7FF)
            struct.pack_into("<HH", text, off, hw1, hw2)
            ncall += 1
    if ncall == 0:
        problems.append(
            "VACUITY: no R_ARM_THM_CALL was relocated, so the call-inside-the-"
            "span case did not actually execute a call")

    if nrel < 3:
        problems.append(
            f"VACUITY: only {nrel} R_ARM_ABS32 pool relocation(s) resolved; the "
            f"fixture declares THREE literals, so a wrong-pool patch would be "
            f"invisible here")

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    for b in set(BASES.values()) | {RETPAD}:
        mu.mem_map(b, MAPSZ)
    mu.mem_write(BASES[".text"], bytes(text))
    if data:
        mu.mem_write(BASES[".data"], bytes(data))
    mu.mem_write(RETPAD, b"\x00\xbf" * 8)

    engine = wasmtime.Engine()
    mod = wasmtime.Module(engine, open(FIXTURE).read())

    def truth(arg):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, mod, [])
        return inst.exports(store)["big"](store, arg) & 0xFFFFFFFF

    def run(arg):
        if bsec is not None:
            mu.mem_write(BASES[".bss"], b"\x00" * min(bsec["sh_size"], MAPSZ))
        mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R11, 0)
        mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + MAPSZ - 0x400)
        mu.reg_write(UC_ARM_REG_LR, RETPAD | 1)
        entry = BASES[".text"] + (syms["big"][1] & ~1)
        mu.emu_start(entry | 1, RETPAD, timeout=30_000_000)
        return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

    ran = 0
    for arg in ARGVALS:
        exp = truth(arg)
        try:
            got = run(arg)
        except UcError as ex:
            problems.append(f"big({arg}): UNICORN FAULT {ex} (wasmtime says {exp}) "
                            f"— the island branch, the BL, or a pooled word is wrong")
            continue
        ran += 1
        if got != exp:
            problems.append(f"big({arg}) = {got}, wasmtime says {exp} "
                            f"— the islanded code MISCOMPILES")
    if ran == 0:
        problems.append("VACUITY: zero executions completed")
    else:
        print(f"  executed: {ran}/{len(ARGVALS)} args bit-exact vs wasmtime, "
              f"{nrel} pool reloc(s) resolved")
    return problems


def main() -> int:
    if not os.path.isfile(SYNTH):
        print(f"FAIL: {SYNTH} not built")
        return 1
    if not os.path.isfile(FIXTURE):
        print(f"FAIL: {FIXTURE} missing")
        return 1

    with tempfile.TemporaryDirectory() as td:
        # ---- CONTROL, and the reason the declared floor is 2 rather than 1.
        # The NON-spanning module must keep compiling. Without this, a change
        # that disabled inline islands entirely would turn the spanning fixture
        # from "refused for the pinned reason" to "refused for the pinned
        # reason" — identical output, total regression, and this gate would
        # have reported PASS. The control is what distinguishes "islands work
        # but decline to span" from "islands do not work".
        ctl_src = os.path.join(REPRO, "litpool_islands_345.wat")
        if not os.path.isfile(ctl_src):
            print(f"FAIL: control fixture {ctl_src} missing")
            return 1
        ctl = subprocess.run(
            [SYNTH, "compile", ctl_src, *ARGS, "-o", os.path.join(td, "ctl.o")],
            capture_output=True, text=True)
        if ctl.returncode != 0:
            print("REFUSE: the NON-spanning island fixture no longer compiles — "
                  "inline islands themselves have regressed, which this gate's "
                  "pinned-decline state would otherwise have hidden")
            print(f"  {(ctl.stdout + ctl.stderr).strip().splitlines()[-1][:150]}")
            return 1
        print("  control: non-spanning island module still compiles")

        rc = 0
        for _fx in FIXTURES:
            rc |= run_one(td, _fx)
        return rc


def run_one(td: str, fx: str) -> int:
    """One spanning fixture, through both states. (v0.74, RQ-74-ISLANDREACH)"""
    global FIXTURE
    FIXTURE = fx
    label = os.path.basename(fx)
    if not os.path.isfile(fx):
        print(f"FAIL: fixture {fx} missing")
        return 1
    obj = os.path.join(td, os.path.basename(fx) + ".o")
    r = compile_once(obj)
    blob = r.stdout + r.stderr

    if r.returncode != 0 or not os.path.isfile(obj):
        # ---- STATE 1: still refused. Pin the refusal, assert nothing else.
        #
        # (v0.74 cold review round 1) THIS BRANCH USED TO BE A SILENT PASS. It
        # returns 0 and prints no `RESULT:` line, so a fixture REVERTING from
        # "compiles and executes bit-exact" to "refused" scored green, and the
        # declared floor could not see it either: `compiles >= 4` counts
        # subprocess INVOCATIONS, which a refusing compiler still makes.
        # Demonstrated with a SYNTH_BIN wrapper that disabled islands for
        # `islandpass_1331_nested.wat` only — rc=0, two PASS lines, and the CI
        # grep `grep -q '^RESULT: PASS'` satisfied.
        #
        # The floor is now `emulations >= 15` (3 fixtures x 5 ARGVALS). A
        # reverted fixture stops emulating, the count falls to 10, and the run
        # is VACUOUS rather than green. That is why the floor counts the work
        # done rather than the calls made.
        if PINNED_REFUSAL not in blob:
            print(f"REFUSE {label}: it declines, but NOT with the pinned #345 "
                  f"message. A different refusal is a different defect.")
            print(f"  got: {blob.strip().splitlines()[-1][:160]}")
            return 1
        print(f"  {label}: REFUSED with the pinned message ({PINNED_REFUSAL})")
        print(f"#1331 ISLANDPASS {label}: pinned-decline; the fixed point has "
              f"NOT landed")
        return 0

    # ---- STATE 2: it compiles. The strong half is now MANDATORY.
    problems, ncall = island_invariants(obj)
    problems += execute(obj)
    print(f"#1331 ISLANDPASS {label}: compiled; {ncall} R_ARM_THM_CALL checked, "
          f"{len(ARGVALS)} args executed")
    if problems:
        for p in problems:
            print(f"REFUSE {label}: {p}")
        print(f"RESULT: FAIL — {label} compiles but the bytes are not correct")
        return 1
    print(f"RESULT: PASS — {label} compiles AND executes bit-exact")
    return 0


if __name__ == "__main__":
    sys.exit(main())
