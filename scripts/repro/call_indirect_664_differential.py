#!/usr/bin/env python3
"""#664 — null-funcref-slot call_indirect oracle: sparse tables trap, not decline.

The fixture's 4-slot table has only slots 1 and 3 initialized; 0 and 2 are
null funcrefs. Pre-#664 the closed-world verifier POISONED such a table
(every type rejected) and the whole function loud-declined — on origin/main
this harness is RED at the compile step (SYMBOL MISSING). #664 relaxes the
verdict to "every INITIALIZED slot type-equal" and discharges the null-slot
trap at RUNTIME: the layout contract requires the runtime/harness to link
every uninitialized slot as a ZERO word, and the dispatch null-checks the
loaded pointer (`cmp ip, #0; bne ok; udf`) between the #642 bounds guard
and the BLX.

For each case both engines run:
  - wasmtime (oracle): via(x, 1/3) return values; via(x, 0/2) trap with
    "uninitialized element"; via(x, 4/99) trap OOB.
  - unicorn (synth's code, table linked at r11 per the contract — null
    slots as ZERO words, words past the region decoy-seeded): initialized
    slots must match wasmtime; null AND OOB indices must stop AT A UDF.

Non-vacuity: a build without the null check BLXes address 0 — an unmapped
fetch fault, which the harness distinguishes from the deterministic UDF
trap (red, not vacuously green). The OOB decoy is inherited from #642/#650.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/call_indirect_664_differential.py
Exits nonzero on any compile decline, mismatch, or missed trap.
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

WAT = Path(__file__).with_name("call_indirect_664_nullslot.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, TABLE, STK = 0x1000000, 0x3000000, 0x6000000
RET = CODE + 0xFFF0  # return pad (inside the CODE map)
DECOY = CODE + 0xFF00  # decoy "function" an unguarded/short-guarded build calls
X = 5
INIT = [1, 3]  # initialized slots -> $f1 (x+100), $f3 (1000-x)
NULL = [0, 2]  # uninitialized slots -> must trap (§4.4.8)
OOB = [4, 99]  # past the table -> must trap (#642 bounds guard)
SLOT_FUNCS = {1: "func_0", 3: "func_1"}  # table image: slot -> symbol


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
    """Ground truth: idx -> result or 'trap'."""
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    results = {}
    for idx in INIT + NULL + OOB:
        store = wasmtime.Store(engine)  # fresh instance per call (stateful)
        f = wasmtime.Instance(store, module, []).exports(store)["via"]
        try:
            results[idx] = f(store, X, idx) & 0xFFFFFFFF
        except wasmtime.Trap:
            results[idx] = "trap"
    return results


def run_unicorn(text: bytes, syms: dict, idx: int, a32: bool):
    """Execute via(X, idx); returns ('ok', r0) or ('trap-udf', pc) or a failure."""
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
    # #664 layout contract: null slots are ZERO words. Initialized slots get
    # their function's address; words PAST the 4-entry table are decoy-seeded
    # (a short/missing bounds guard "succeeds" loudly with 0x5A, #642/#650).
    for slot in range(4):
        if slot in SLOT_FUNCS:
            ptr = (CODE + syms[SLOT_FUNCS[slot]]) | thumb_bit
        else:
            ptr = 0  # null funcref — the contract's zero word
        mu.mem_write(TABLE + 4 * slot, struct.pack("<I", ptr))
    for i in range(4, 128):
        mu.mem_write(TABLE + 4 * i, struct.pack("<I", DECOY | thumb_bit))

    mu.reg_write(UC_ARM_REG_R0, X)
    mu.reg_write(UC_ARM_REG_R1, idx)
    mu.reg_write(UC_ARM_REG_R11, TABLE)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | thumb_bit)
    try:
        mu.emu_start((CODE + syms["via"]) | thumb_bit, RET, count=2000)
    except UcError as e:
        pc = mu.reg_read(UC_ARM_REG_PC)
        # A deterministic §4.4.8 trap = execution stopped ON a udf
        # (Thumb 0xDExx / A32 0xE7F000F0). A BLX to address 0 (missing null
        # check) faults OUTSIDE .text and is reported as 'fault' — red.
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
    elf_path = f"/tmp/ci664_{'a32' if a32 else 'thumb'}.o"
    compile_direct(elf_path, target)

    with open(elf_path, "rb") as fh:
        e = ELFFile(fh)
        text = bytes(e.get_section_by_name(".text").data())
        # Symbols from the symtab, never from disasm text (host-dependent).
        st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
    for need in ["via"] + sorted(SLOT_FUNCS.values()):
        if need not in syms:
            print(f"SYMBOL MISSING: {need} (a decline drops the function — #664 red)")
            return 1

    isa = "A32" if a32 else "Thumb-2"
    fails = 0
    for idx in INIT:
        want = oracle[idx]
        kind, got = run_unicorn(text, syms, idx, a32)
        ok = kind == "ok" and got == want
        fails += 0 if ok else 1
        got_s = f"{got:#x}" if isinstance(got, int) else got
        print(
            f"[{isa}] via({X},{idx}) = {kind}:{got_s} (wasmtime: {want:#x}) "
            f"{'OK' if ok else 'MISMATCH'}"
        )
    for idx in NULL + OOB:
        assert oracle[idx] == "trap", f"oracle must trap idx {idx}"
        why = "null slot" if idx in NULL else "OOB"
        kind, got = run_unicorn(text, syms, idx, a32)
        ok = kind == "trap-udf"
        fails += 0 if ok else 1
        if ok:
            print(f"[{isa}] via({X},{idx}) = udf trap at {got:#x} ({why}, wasmtime: trap) OK")
        elif kind == "ok" and got == 0x5A:
            print(
                f"[{isa}] via({X},{idx}) = {got:#x} — the DECOY past the table was "
                f"CALLED ({why}): bounds guard missing or short MISMATCH"
            )
        else:
            print(
                f"[{isa}] via({X},{idx}) = {kind}:{got} ({why}, wasmtime: trap) "
                "MISMATCH — a missing null check BLXes address 0 and faults here"
            )
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
    print(f"ORACLE: FAIL — {fails} case(s) diverged from wasmtime (#664)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
