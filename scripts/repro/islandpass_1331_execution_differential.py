#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 15
# RQ-75-FLOORBIND (#1331), v0.75 — PROVEN POTENT by four mutations, each verified
# present on disk before measuring, and each checked to red FOR ITS OWN REASON
# rather than merely to red:
#
#   a FOURTH fixture added, floor left at 15   -> REFUSE (declared floor 15 != 20)
#   compare the compiler WITH ITSELF           -> VACUITY (wasmtime consulted 0x)
#   ARGVALS set to all zeros                   -> VACUITY (duplicate arguments)
#   spanning padding deleted, module VALID     -> REACH (.text 364 < 4096)
#
# 4 CAUGHT for the right reason, 0 for the wrong one, 0 survived, 0 inert. The
# distinction is load-bearing: the shrink mutation's FIRST form cut a line range,
# broke the WAT, and red on the pinned-refusal check instead — proving nothing
# about reach. A red-first that fires for the wrong reason is a hypothesis about
# the plant, not evidence about the gate.
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

# RQ-75-FLOORBIND (#1331), v0.75 — THE DECLARED FLOOR IS CHECKED AGAINST THE
# DERIVATION. v0.74 moved this oracle's floor from `compiles >= 4` to
# `emulations >= 15`, closing a real silent skip. But 15 was `3 fixtures x 5
# ARGVALS` WRITTEN OUT, so a fourth fixture would leave a floor of 15
# satisfiable by three — restoring the very skip v0.74 closed, quietly, in the
# commit that grows the corpus.
#
# The `# ci-checks:` header must STAY a literal: `oracle_wiring_check.py` reads
# it statically, without importing this module, which is what lets it audit
# every oracle without running any of them. So the literal stays and this module
# REFUSES TO RUN when it disagrees with the derivation. The number is still
# declared once; it can no longer be declared WRONG.
EXPECTED_EMULATIONS = len(FIXTURES) * len(ARGVALS)


def _declared_floor():
    """The `emulations >= N` this file's own header declares, read off source."""
    import re
    src = open(__file__, encoding="utf-8").read()
    m = re.search(r"^# ci-checks:\s*emulations\s*>=\s*(\d+)\s*$", src, re.M)
    return int(m.group(1)) if m else None


# RQ-75-FLOORBIND round 1 (v0.75): the shapes the corpus must actually contain.
# `len(FIXTURES) * len(ARGVALS)` checks CONSISTENCY, not ADEQUACY — the cold
# review replaced FIXTURES with three copies of the SAME fixture and every
# number stayed identical: the oracle, `check_floor_binding`, the CI
# emulation-floor equality, `claim_check` at 75/75, and the generator's own
# `--check` all ran green while two thirds of the corpus stopped being tested.
# And the two lost shapes were exactly v0.74's additions.
#
# So the POPULATION is declared, not merely counted. Each entry names a distinct
# island-placement shape; adding a fourth is a visible edit here, which is the
# same "declared list, never a glob" rule FIELD_KEY_CONSUMERS uses one file over.
REQUIRED_SHAPES = ("spanning", "backspan", "nested")
# The structural needle that makes each shape THAT shape, so a file merely NAMED
# for a shape cannot stand in for it. Round 2 defeated the basename-only check
# with three renamed copies of one fixture.
SHAPE_NEEDLE = {
    "backspan": "loop",      # the backward branch is a loop latch
    "nested":   "br_if 1",   # a branch out of a NESTED block
}


def check_corpus_adequacy():
    """REFUSE a corpus that counts right and covers wrong.

    ROUND 2 DEFEATED THE FIRST VERSION OF THIS CHECK, which compared BASENAMES:
    three byte-identical copies of `spanning.wat`, named `*_spanning_r2`,
    `*_backspan_r2` and `*_nested_r2`, satisfied both the duplicate test and the
    REQUIRED_SHAPES test while the corpus covered ONE shape. All five gates ran
    green. A check on filenames is a check on filenames.

    So CONTENT is what is compared now. The three shapes are distinguishable in
    the WAT itself — a forward `br_if` that spans the island point, a backward
    branch (loop latch), and a branch out of a nested block — so distinct content
    hashes are necessary, and each shape's own structural needle is required to
    appear in the file that claims it.
    """
    import hashlib

    base = [os.path.basename(f) for f in FIXTURES]
    digests = {}
    for f in FIXTURES:
        if not os.path.isfile(f):
            raise SystemExit(f"REFUSE: fixture {f} is missing")
        digests[os.path.basename(f)] = hashlib.sha256(
            open(f, "rb").read()).hexdigest()[:12]
    if len(set(digests.values())) != len(FIXTURES):
        dupes = {}
        for n, d in digests.items():
            dupes.setdefault(d, []).append(n)
        same = {d: ns for d, ns in dupes.items() if len(ns) > 1}
        raise SystemExit(
            f"REFUSE: fixtures with IDENTICAL CONTENT under different names: "
            f"{same}. Renaming a copy satisfies a basename check while the "
            f"corpus covers one shape — measured in v0.75's round 2 "
            f"(RQ-75-FLOORBIND).")
    # Each shape must be claimed by EXACTLY ONE fixture. Substring matching over
    # basenames is unsound on its own: round 2 pointed out that a single file
    # named `spanning_backspan_nested.wat` satisfies a "does some name contain
    # each shape" test with a corpus of one.
    for kind in REQUIRED_SHAPES:
        owners = [n for n in base if kind in n]
        if len(owners) != 1:
            raise SystemExit(
                f"REFUSE: the {kind!r} shape is claimed by {len(owners)} "
                f"fixture(s) {owners} — exactly one must claim it, or one file "
                f"named for several shapes satisfies the corpus "
                f"(RQ-75-FLOORBIND).")
    # And each claimed shape must carry its own structural needle.
    for kind, needle in SHAPE_NEEDLE.items():
        owner = [n for n in base if kind in n]
        if not owner:
            continue
        for n in owner:
            path = next(f for f in FIXTURES if os.path.basename(f) == n)
            if needle not in open(path, encoding="utf-8").read():
                raise SystemExit(
                    f"REFUSE: {n} is NAMED for the {kind!r} shape but its content "
                    f"does not contain {needle!r}. The name is not the shape "
                    f"(RQ-75-FLOORBIND).")
    if len(set(base)) != len(base):
        raise SystemExit(
            f"REFUSE: FIXTURES carries duplicates {sorted(base)} — the floor "
            f"`len(FIXTURES) * len(ARGVALS)` is satisfied by repeating one "
            f"shape, which is how two thirds of this corpus can stop being "
            f"tested with every number unchanged (RQ-75-FLOORBIND).")
    missing = [k for k in REQUIRED_SHAPES
               if not any(k in b for b in base)]
    if missing:
        raise SystemExit(
            f"REFUSE: the corpus no longer covers {missing}. These are distinct "
            f"island-placement shapes — a forward span, a backward branch (loop "
            f"latch) and a branch out of a nested block — and a count cannot "
            f"tell that one has been swapped for a copy of another "
            f"(RQ-75-FLOORBIND).")


def check_floor_binding():
    check_corpus_adequacy()
    got = _declared_floor()
    if got is None:
        raise SystemExit(
            "REFUSE: no `# ci-checks: emulations >= N` header in this file. "
            "The floor is what stops a reverted fixture scoring green (#1331).")
    if got != EXPECTED_EMULATIONS:
        raise SystemExit(
            f"REFUSE: the declared floor is `emulations >= {got}` but "
            f"{len(FIXTURES)} fixture(s) x {len(ARGVALS)} arg(s) = "
            f"{EXPECTED_EMULATIONS}. A floor BELOW the derivation is satisfiable "
            f"while a fixture silently stops emulating (#1331); a floor above it "
            f"can never be met. Update the header.")


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
    unnoticed. A real per-literal INV2 is a v0.76 candidate (it said v0.75, and v0.75 did NOT
    deliver it); it is not claimed
    here."""
    import struct

    from elftools.elf.elffile import ELFFile

    problems = []
    e = ELFFile(open(obj, "rb"))
    text = e.get_section_by_name(".text").data()
    # RQ-75-FLOORBIND (#1331): THE FIXTURE MUST STILL NEED AN ISLAND.
    # A Thumb-2 `LDR(literal)` reaches 4,095 bytes forward (12-bit unsigned
    # offset), so a module whose `.text` fits inside that range needs no literal
    # island at all — and islands are this oracle's entire subject. v0.74's
    # round 1 demonstrated the defeat: deleting 900 lines of padding from the
    # spanning fixture dropped `.text` to 2,988 bytes and this differential
    # still reported "compiles AND executes bit-exact", rc=0, with the
    # generator's own `--check` green. The gate passed on a module with no
    # island in it.
    #
    # Measured at this lane's cut so the threshold is not vacuous:
    # spanning 11,544 / backspan 6,656 / nested 6,636 bytes. The mutation that
    # proves it must keep the module VALID — deleting whole 4-line padding units
    # gives `.text` 364 bytes and still compiles; a crude line-range truncation
    # breaks the WAT and reds for the WRONG reason, which is how this assertion
    # was first measured as passing when it had never run.
    if len(text) < 4096:
        problems.append(
            f"REACH: .text is {len(text)} bytes, below the 4,095-byte "
            f"LDR(literal) span — this fixture needs no literal island, so it "
            f"cannot be evidence about islands (RQ-75-FLOORBIND)")
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

    # RQ-75-FLOORBIND: THE COUNTER LIVES HERE, not at the call site. Round 2
    # defeated this oracle by making it compare the compiler WITH ITSELF —
    # replace `truth(arg)` with `run(arg)` and every argument agrees, the
    # emulation count RISES, and it prints "5/5 args bit-exact vs wasmtime".
    # An earlier draft of this lane incremented the counter beside
    # `exp = truth(arg)`, where that exact mutation still incremented it: an
    # instrument placed where the mutation cannot move it measures nothing.
    wasmtime_calls = 0

    def truth(arg):
        nonlocal wasmtime_calls
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, mod, [])
        wasmtime_calls += 1
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

    expected_vals = []
    ran = 0
    for arg in ARGVALS:
        exp = truth(arg)
        expected_vals.append(exp)
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
    # An oracle that never asked the reference is not a differential, whatever
    # it prints.
    if wasmtime_calls != len(ARGVALS):
        problems.append(
            f"VACUITY: wasmtime was consulted {wasmtime_calls} time(s) for "
            f"{len(ARGVALS)} argument(s) — without the reference this compares "
            f"the compiler with itself (RQ-75-FLOORBIND)")
    # And an argument set that cannot distinguish two outcomes cannot see an
    # argument-dropping miscompile, however many times it runs: ARGVALS can be
    # set to all zeros with byte-identical output. The threshold is 2, not
    # len(ARGVALS), because v0.74 measured PER FIXTURE that `spanning`
    # legitimately distinguishes exactly 2 and `backspan` 4 — demanding 5 would
    # red on correct fixtures.
    if len(set(ARGVALS)) != len(ARGVALS):
        problems.append(
            f"VACUITY: ARGVALS carries duplicates {ARGVALS!r} — the repeated "
            f"arguments add executions without adding discrimination")
    if len(set(expected_vals)) < 2:
        problems.append(
            f"VACUITY: all {len(ARGVALS)} arguments have the SAME expected "
            f"result {expected_vals[:1]!r}, so a miscompile that ignores its "
            f"argument is invisible here (RQ-75-FLOORBIND)")
    if ran == 0:
        problems.append("VACUITY: zero executions completed")
    else:
        print(f"  executed: {ran}/{len(ARGVALS)} args bit-exact vs wasmtime, "
              f"{nrel} pool reloc(s) resolved")
    return problems


def main() -> int:
    # RQ-75-FLOORBIND: the declared floor must agree with the derivation BEFORE
    # anything is measured. A wrong floor is not a wrong number; it is a gate
    # that cannot see a fixture stop emulating.
    check_floor_binding()
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
