#!/usr/bin/env python3
# ci-status: wired
# ci-checks: stdout /^  corpus: (\d+) byte-identical/ >= 160
"""RQ-72-ISLANDS (#345, cpetig via #1331): constant islands for the literal pool.


WHY THIS IS A DIFFERENTIAL AND NOT A PINNED-HASH BASELINE
---------------------------------------------------------
This lane MOVES EMITTED BYTES for any module that needs an island, so the
obligation is to prove it moves NO bytes for modules that do not. The obvious
way — freeze a sha256 per module and compare — creates a 165-entry table that
must be regenerated on every legitimate codegen change, and a table nobody can
regenerate honestly is how a "frozen replay" stops being frozen (the defect
RQ-72-ISSUEGATE records about the v0.70 replay).

So the control is SELF-CONTAINED: compile each module TWICE with the SAME
binary, once with islands enabled and once with `SYNTH_NO_LITPOOL_ISLANDS=1`,
and assert the two `.text` sections are byte-identical. Nothing to maintain,
and it cannot go stale — if codegen legitimately changes, BOTH legs change
together and the comparison still means what it says.

THE GATES
---------
1. POTENCY OF THE OFF-SWITCH. The fixture `litpool_islands_345.wat` must
   REFUSE with islands off (`LdrSym literal pool out of range`) and COMPILE
   with them on. If both legs agree, the switch is not wired and every other
   assertion here is vacuous.
2. BYTE IDENTITY. Every corpus module that compiles must produce a
   byte-identical `.text` on both legs. This is the negative control: it
   proves the change is confined to the shapes it targets.
3. EXECUTION. The previously-refused fixture must not merely compile — the
   refused code had never run, so "it compiles now" is a fact about the
   compiler, not about the code (the v0.71 VFPALIAS lesson). Its exports are
   executed and compared against wasmtime.
4. THE REFUSAL IS STILL LIVE. `emit_literal_pool` keeps the #345 error: an
   island widens WHERE a pool may sit, never the Thumb-2 LDR-literal encoding,
   which is a 12-bit unsigned field and always will be.

   HONEST LIMIT, stated rather than dressed as a gate. No input is known that
   refuses WITH islands enabled, and none was constructed: the trigger re-runs
   at every instruction boundary, so it flushes before the window can close,
   and with many literals in flight the growing word block makes it flush
   EARLIER, not later. The refusal path is therefore exercised here by the
   ISLANDS-OFF leg of gate 1, which reaches the identical `return Err` in the
   identical function — not by a separate ON-leg fixture, because that fixture
   does not exist. If a future change makes an ON-leg refusal reachable, this
   is the note that says the coverage was never there.
"""
import glob, hashlib, os, subprocess, sys, tempfile

SYNTH = os.environ.get("SYNTH_BIN", "./target/release/synth")
REPRO = os.path.dirname(os.path.abspath(__file__))
FIXTURE = os.path.join(REPRO, "litpool_islands_345.wat")
ARGS = ["--target", "cortex-m7", "--relocatable", "--all-exports", "--native-pointer-abi"]
OFF = "SYNTH_NO_LITPOOL_ISLANDS"
REFUSAL = "LdrSym literal pool out of range"

# RQ-73-ISLANDPASS (#1331): modules that DECLINE with inline islands off and
# COMPILE with them on, by design. Before the fixed point there were none — a
# spanning placement was refused rather than resolved — so this set existing at
# all is the deliverable. Each entry is asserted in BOTH directions below.
INTENDED_ACCEPTANCES = {
    # The v0.72 red-first fixture: a forward `br_if` spanning the placement.
    "litpool_islands_345_branchspan.wat",
    # The #1331 fixture: spanning branch PLUS a direct call inside the span and
    # three distinct literals — the two things v0.72's execution leg could not
    # see. Its own execution gate is falcon-style bit-exactness against
    # wasmtime in islandpass_1331_execution_differential.py.
    "islandpass_1331_spanning.wat",
}


def compile_once(wat, obj, islands):
    env = dict(os.environ)
    env.pop(OFF, None)
    if not islands:
        env[OFF] = "1"
    return subprocess.run([SYNTH, "compile", wat, "-o", obj, *ARGS],
                          capture_output=True, text=True, timeout=300, env=env)


def text_sha(obj):
    from elftools.elf.elffile import ELFFile
    with open(obj, "rb") as f:
        s = ELFFile(f).get_section_by_name(".text")
        return hashlib.sha256(s.data()).hexdigest() if s is not None else None


def execute_fixture():
    """GATE 3: the previously-refused code had NEVER RUN, so 'it compiles now'
    is a fact about the compiler. Execute it against wasmtime.

    The harness is the one every other --native-pointer-abi differential in
    this directory uses: map .text/.data/.bss at known bases, resolve every
    R_ARM_ABS32 literal-pool word in place (REL: base + symbol + in-place
    addend), set the embedder register contract, run under unicorn.
    """
    import struct
    import wasmtime
    from elftools.elf.elffile import ELFFile
    from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UcError
    from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R11,
                                   UC_ARM_REG_SP, UC_ARM_REG_LR)

    ABS32 = 2
    BASES = {".text": 0x10000, ".data": 0x60000, ".bss": 0x40000}
    MAPSZ = 0x20000
    RETPAD = 0x90000

    problems = []
    with tempfile.TemporaryDirectory() as td:
        obj = os.path.join(td, "isl.o")
        r = compile_once(FIXTURE, obj, islands=True)
        if r.returncode != 0:
            return ["GATE3: the fixture did not compile with islands on; "
                    "execution could not be attempted"]

        e = ELFFile(open(obj, "rb"))
        secname = {i: s.name for i, s in enumerate(e.iter_sections())}
        text = bytearray(e.get_section_by_name(".text").data())
        dsec = e.get_section_by_name(".data")
        bsec = e.get_section_by_name(".bss")
        data = bytearray(dsec.data()) if dsec is not None else bytearray()
        symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: (s["st_shndx"], s["st_value"]) for s in symtab.iter_symbols()}

        rel = e.get_section_by_name(".rel.text")
        nrel = 0
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
        if nrel == 0:
            problems.append(
                "GATE3 vacuity: no R_ARM_ABS32 pool relocation was resolved, so "
                "the island word this lane exists to place was never exercised")

        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for b in set(BASES.values()) | {RETPAD}:
            mu.mem_map(b, MAPSZ)
        mu.mem_write(BASES[".text"], bytes(text))
        if data:
            mu.mem_write(BASES[".data"], bytes(data))
        mu.mem_write(RETPAD, b"\x00\xbf" * 8)

        engine = wasmtime.Engine()
        mod = wasmtime.Module(engine, open(FIXTURE).read())

        def truth(fn, arg):
            store = wasmtime.Store(engine)
            inst = wasmtime.Instance(store, mod, [])
            return inst.exports(store)[fn](store, arg) & 0xFFFFFFFF

        def run(fn, arg):
            if bsec is not None:
                mu.mem_write(BASES[".bss"], b"\x00" * min(bsec["sh_size"], MAPSZ))
            mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
            mu.reg_write(UC_ARM_REG_R11, 0)
            mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + MAPSZ - 0x400)
            mu.reg_write(UC_ARM_REG_LR, RETPAD | 1)
            entry = BASES[".text"] + (syms["big"][1] & ~1)
            mu.emu_start(entry | 1, RETPAD, timeout=20_000_000)
            return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

        ran = 0
        for arg in (0, 1, 2, 7, 13, 0x7FFFFFFF):
            exp = truth("big", arg)
            try:
                got = run("big", arg)
            except UcError as ex:
                problems.append(f"GATE3 big({arg}): UNICORN FAULT {ex} (expect {exp}) "
                                f"— the island branch or the pooled word is wrong")
                continue
            ran += 1
            if got != exp:
                problems.append(f"GATE3 big({arg}) = {got}, wasmtime says {exp} "
                                f"— the islanded code MISCOMPILES")
        if ran == 0:
            problems.append("GATE3 vacuity: zero executions completed")
        else:
            print(f"  executed: {ran}/6 args bit-exact vs wasmtime, "
                  f"{nrel} pool reloc(s) resolved")
    return problems


def main():
    failures = []

    # ---- GATE 1: the off-switch must actually switch something -------------
    with tempfile.TemporaryDirectory() as td:
        on = compile_once(FIXTURE, os.path.join(td, "on.o"), islands=True)
        off = compile_once(FIXTURE, os.path.join(td, "off.o"), islands=False)
    off_blob = off.stdout + off.stderr
    on_blob = on.stdout + on.stderr
    if REFUSAL not in off_blob:
        failures.append(
            "GATE1 potency: with islands OFF the fixture did NOT hit the pool "
            "range. Either the off-switch is unwired or the fixture no longer "
            "reaches past 4095 — in both cases every assertion below is "
            f"vacuous. Output:\n{off_blob[:600]}")
    if REFUSAL in on_blob:
        failures.append(
            "GATE1 accept: with islands ON the fixture STILL refuses — the "
            f"pass did not place a reachable island. Output:\n{on_blob[:600]}")

    # ---- GATE 2: byte identity on everything that did not need an island ---
    same = diff = skipped = accepted = 0
    with tempfile.TemporaryDirectory() as td:
        for wat in sorted(glob.glob(os.path.join(REPRO, "*.wat"))):
            if os.path.abspath(wat) == os.path.abspath(FIXTURE):
                continue
            a = os.path.join(td, "a.o")
            b = os.path.join(td, "b.o")
            ra = compile_once(wat, a, islands=True)
            rb = compile_once(wat, b, islands=False)
            base = os.path.basename(wat)
            if base in INTENDED_ACCEPTANCES:
                # RQ-73-ISLANDPASS (#1331). The message below has always said
                # "or be a named, intended acceptance"; until now nothing was
                # named, so the branch did not exist. These two modules are the
                # whole point of the fixed point, and the assertion is
                # DIRECTIONAL: islands ON must ACCEPT and islands OFF must
                # DECLINE. A pin that merely tolerated "the two legs differ"
                # would stay green if the pass regressed to refusing again.
                if ra.returncode != 0:
                    failures.append(
                        f"GATE2 {base}: pinned as an intended acceptance, but it "
                        f"DECLINED with islands on (rc={ra.returncode}) — the "
                        f"#1331 fixed point has regressed")
                elif rb.returncode == 0:
                    failures.append(
                        f"GATE2 {base}: accepted with islands OFF too, so it no "
                        f"longer demonstrates that inline placement is what "
                        f"serves this shape — the fixture has gone vacuous")
                else:
                    accepted += 1
                continue
            if ra.returncode != rb.returncode:
                failures.append(
                    f"GATE2 {base}: islands changed the "
                    f"ACCEPT/DECLINE outcome (on rc={ra.returncode}, "
                    f"off rc={rb.returncode}) — a module that declined before "
                    f"must still decline, or be a named, intended acceptance")
                continue
            if ra.returncode != 0:
                skipped += 1
                continue
            sa, sb = text_sha(a), text_sha(b)
            if sa == sb:
                same += 1
            else:
                diff += 1
                failures.append(
                    f"GATE2 {os.path.basename(wat)}: .text MOVED with islands "
                    f"enabled ({sa[:12]} vs {sb[:12]}) although the module "
                    f"never needed one — the change is not confined")

    if accepted != len(INTENDED_ACCEPTANCES):
        failures.append(
            f"GATE2 vacuity: {accepted} of {len(INTENDED_ACCEPTANCES)} pinned "
            f"intended acceptances were exercised — a named acceptance that the "
            f"corpus never reaches is a pin nothing checks")

    if same < 160:
        failures.append(
            f"GATE2 vacuity: only {same} modules were compared byte-for-byte; "
            f"the corpus should yield >= 160. A control that compares almost "
            f"nothing passes for the wrong reason")

    print(f"  corpus: {same} byte-identical, {diff} MOVED, {skipped} decline on both legs")

    # ---- GATE 3: EXECUTION -------------------------------------------------
    failures.extend(execute_fixture())
    for f in failures:
        print(f"FAIL {f}")
    print(f"litpool-islands-345: {len(failures)} failure(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
