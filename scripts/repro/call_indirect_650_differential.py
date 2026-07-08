#!/usr/bin/env python3
"""#650 — multi-table call_indirect oracle: the contiguous R11 region.

Layout contract (#650): the runtime/harness links every funcref table as ONE
contiguous region of raw 4-byte code pointers based at R11, in declaration
order — table 0 at R11+0, table N at R11 + sum(size(0..N))*4. The dispatch
expansion for table N adds the compile-time base offset
(`add ip, r11, ip; ldr ip, [ip, #off]`), and the #642 bounds guard compares
against THAT table's own size. Offset 0 (table 0 / any single-table module)
keeps the pre-#650 bytes identical by construction.

The fixture carries TWO tables with OVERLAPPING indices and DISTINCT
functions — the aliasing canary: table0[1] (x+200) != table1[1] (1000-x). A
backend that drops the table index and always dispatches table 0 returns
table 0's results for `f1`.

For each case both engines run:
  - wasmtime (oracle): f0/f1 over in-bounds indices; OOB indices trap.
  - unicorn (synth's code, region linked at r11 per the contract): in-bounds
    results must match wasmtime; OOB on EITHER table must stop at a `udf`
    (the §4.4.8 trap). Words past the 6-entry region are seeded with a valid
    decoy so a missing/short bounds guard "succeeds" (returns 0x5A) instead
    of faulting — a loud, non-vacuous red.

On origin/main (≤ v0.33.1) this harness is RED at the compile step: every
`call_indirect` through table 1 loud-declines ("table index 1 is not
supported (only table 0 is linked at R11)"). That red documents the
capability gap this oracle upgrades — green = correct multi-table dispatch.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/call_indirect_650_differential.py
Exits nonzero on any compile decline, mismatch, missed trap, or aliasing.
"""

import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("call_indirect_650_multitable.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, TABLE, STK = 0x1000000, 0x3000000, 0x6000000
RET = CODE + 0xFFF0  # return pad (inside the CODE map)
DECOY = CODE + 0xFF00  # decoy "function" an unguarded/short-guarded build calls
X = 5
IN_BOUNDS = [0, 1, 2]
OOB = [3, 5, 99]
T0 = ["func_0", "func_1", "func_2"]  # $a0 $a1 $a2 — table 0 image
T1 = ["func_3", "func_4", "func_5"]  # $b0 $b1 $b2 — table 1 image


def compile_direct(out: str, target: str) -> None:
    """Compile via the direct-selector path (the one that lowers call_indirect)."""
    r = subprocess.run(
        [
            SYNTH,
            "compile",
            str(WAT),
            "-o",
            out,
            "--target",
            target,
            "--all-exports",
            "--relocatable",
            "--no-optimize",
        ],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        print(f"COMPILE FAILED:\n{r.stdout}\n{r.stderr}")
        sys.exit(1)


def wasmtime_oracle():
    """Ground truth: (export, idx) -> result or 'trap'."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    results = {}
    for name in ("f0", "f1"):
        for idx in IN_BOUNDS + OOB:
            store = wasmtime.Store(engine)  # fresh instance per call (stateful)
            f = wasmtime.Instance(store, module, []).exports(store)[name]
            try:
                results[(name, idx)] = f(store, X, idx) & 0xFFFFFFFF
            except wasmtime.Trap:
                results[(name, idx)] = "trap"
    return results


def run_unicorn(text: bytes, syms: dict, entry: str, idx: int, a32: bool):
    """Execute entry(X, idx); returns ('ok', r0) or ('trap-udf', pc) or a failure."""
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM if a32 else UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(TABLE, 0x10000)
    mu.mem_map(STK, 0x100000)
    mu.mem_write(CODE, text)
    if a32:
        mu.mem_write(RET, struct.pack("<II", 0xE320F000, 0xE320F000))
        mu.mem_write(DECOY, struct.pack("<II", 0xE3A0005A, 0xE12FFF1E))
        thumb_bit = 0
    else:
        mu.mem_write(RET, struct.pack("<HH", 0xBF00, 0xBF00))
        mu.mem_write(DECOY, struct.pack("<HH", 0x205A, 0x4770))
        thumb_bit = 1
    # #650 layout contract: ONE contiguous region at R11 — table 0's three
    # entries at words 0..2, table 1's at words 3..5. Words PAST the region
    # are decoy-seeded (a short bounds guard or a missing base offset that
    # runs off the end "succeeds" loudly with 0x5A instead of faulting).
    entries = [syms[s] for s in T0 + T1]
    for i, off in enumerate(entries):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", (CODE + off) | thumb_bit))
    for i in range(len(entries), 128):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", DECOY | thumb_bit))

    mu.reg_write(UC_ARM_REG_R0, X)
    mu.reg_write(UC_ARM_REG_R1, idx)
    mu.reg_write(UC_ARM_REG_R11, TABLE)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | thumb_bit)
    try:
        mu.emu_start((CODE + syms[entry]) | thumb_bit, RET, count=2000)
    except UcError as e:
        pc = mu.reg_read(UC_ARM_REG_PC)
        # A deterministic §4.4.8 trap = execution stopped ON a udf
        # (Thumb 0xDExx / A32 0xE7F000F0).
        if CODE <= pc < CODE + len(text):
            if a32:
                w = struct.unpack("<I", text[pc - CODE : pc - CODE + 4])[0]
                if w == 0xE7F000F0:
                    return ("trap-udf", pc)
            else:
                hw = struct.unpack("<H", text[pc - CODE : pc - CODE + 2])[0]
                if hw & 0xFF00 == 0xDE00:
                    return ("trap-udf", pc)
        return ("fault", f"{e} at pc={pc:#x} (NOT a udf trap)")
    return ("ok", mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF)


def run_isa(oracle: dict, target: str, a32: bool) -> int:
    elf_path = f"/tmp/ci650_{'a32' if a32 else 'thumb'}.o"
    compile_direct(elf_path, target)

    with open(elf_path, "rb") as fh:
        e = ELFFile(fh)
        text = bytes(e.get_section_by_name(".text").data())
        # Symbols from the symtab, never from disasm text (host-dependent).
        st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
    for need in ["f0", "f1"] + T0 + T1:
        if need not in syms:
            print(f"SYMBOL MISSING: {need} (a decline drops the function — #650 red)")
            return 1

    isa = "A32" if a32 else "Thumb-2"
    fails = 0
    for name in ("f0", "f1"):
        for idx in IN_BOUNDS:
            want = oracle[(name, idx)]
            kind, got = run_unicorn(text, syms, name, idx, a32)
            ok = kind == "ok" and got == want
            fails += 0 if ok else 1
            got_s = f"{got:#x}" if isinstance(got, int) else got
            print(
                f"[{isa}] {name}({X},{idx}) = {kind}:{got_s} (wasmtime: {want:#x}) "
                f"{'OK' if ok else 'MISMATCH'}"
            )
        for idx in OOB:
            assert oracle[(name, idx)] == "trap", f"oracle must trap {name} idx {idx}"
            kind, got = run_unicorn(text, syms, name, idx, a32)
            ok = kind == "trap-udf"
            fails += 0 if ok else 1
            if ok:
                print(f"[{isa}] {name}({X},{idx}) = udf trap at {got:#x} (wasmtime: trap) OK")
            elif kind == "ok" and got == 0x5A:
                print(
                    f"[{isa}] {name}({X},{idx}) = {got:#x} — the DECOY past the region "
                    "was CALLED: bounds guard missing or against the wrong size MISMATCH"
                )
            else:
                print(f"[{isa}] {name}({X},{idx}) = {kind}:{got} (wasmtime: trap) MISMATCH")

    # The aliasing canary, asserted explicitly: overlapping index, different
    # table, DIFFERENT result (a table-index-dropping backend fails here).
    _, r0 = run_unicorn(text, syms, "f0", 1, a32)
    _, r1 = run_unicorn(text, syms, "f1", 1, a32)
    if r0 == r1:
        print(f"[{isa}] ALIASING: f0({X},1) == f1({X},1) == {r0:#x} — table index dropped")
        fails += 1
    else:
        print(f"[{isa}] aliasing canary: f0({X},1)={r0:#x} != f1({X},1)={r1:#x} OK")
    return fails


def main() -> int:
    oracle = wasmtime_oracle()
    print(f"wasmtime oracle: {oracle}")

    # Both ISAs share the expansion: Thumb-2 (cortex-m3) and A32 (cortex-r5).
    fails = run_isa(oracle, "cortex-m3", a32=False)
    fails += run_isa(oracle, "cortex-r5", a32=True)

    if fails == 0:
        print("ORACLE: PASS")
        return 0
    print(f"ORACLE: FAIL — {fails} case(s) diverged from wasmtime (#650)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
