#!/usr/bin/env python3
"""#757 RED-FIRST differential — the low-const-below-string chunked static copy.

The six 0.43.0 reconstructions all found the wide-head source addend CORRECT,
but every one of them placed the copied string AT the `__synth_wasm_data` base
(or with only zeros below it), so a "reads base+0 instead of base+0x20"
miscomputation was MASKED — reading zeros looks the same as reading nothing.

gale's real gust:os module has small consts at data offsets 0x00..0x1f AND the
string "gust:os up\\n" at 0x20 in the SAME region. This harness reproduces that
layout: the head i64 chunk sources from `data_base + 0x20` through the #746 wide
arm, reached THROUGH a RawVec-grow `call`, and the destination is the low-const
region. copy_peek(i) copies then reads dest byte i back.

If the wide arm folds the wrong per-chunk source addend, copy_peek(0..6) returns
the LOW consts [2,0,0,0,1,0,0] instead of the string bytes "gust:os".

Resolves BOTH R_ARM_ABS32 (type 2) and R_ARM_THM_CALL (type 10) — the copy is
reached through a `bl` (RawVec-grow), and an unresolved bl self-corrupts (the
memory-note vacuous-gate lesson). Separate section bases so a baked absolute
linmem offset cannot accidentally resolve.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/mem757_low_const_copy_differential.py
Exits nonzero on any mismatch.
"""

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("mem757_low_const_copy.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
BUDGET = 2048
ABS32 = 2
THM_CALL = 10
BASES = {".text": 0x100000, ".bss": 0x200000, ".data": 0x300000, ".rodata": 0x400000}
MAPSZ = 0x10000


def wasmtime_truth(fn, arg):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg) & 0xFFFFFFFF


def main():
    obj = Path(tempfile.mkdtemp(prefix="mem757lc_")) / "mem757lc.o"
    proc = subprocess.run(
        [
            SYNTH,
            "compile",
            str(WAT),
            "-o",
            str(obj),
            "--target",
            "cortex-m3",
            "--native-pointer-abi",
            "--all-exports",
            "--relocatable",
            "--shadow-stack-size",
            str(BUDGET),
        ],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        print(proc.stderr.strip())
        print("FAIL: compile declined")
        return 1

    e = ELFFile(open(obj, "rb"))
    secname = {i: s.name for i, s in enumerate(e.iter_sections())}
    text = bytearray(e.get_section_by_name(".text").data())
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: (s["st_shndx"], s["st_value"]) for s in symtab.iter_symbols()}

    def sym_addr(sym):
        shndx, val = syms[sym.name]
        sn = secname.get(shndx, ".text")
        return BASES.get(sn, BASES[".text"]) + val

    for r in e.get_section_by_name(".rel.text").iter_relocations():
        t = r["r_info_type"]
        sym = symtab.get_symbol(r["r_info_sym"])
        off = r["r_offset"]
        if t == ABS32:
            shndx, val = syms[sym.name]
            sn = secname[shndx]
            (add,) = struct.unpack_from("<I", text, off)
            struct.pack_into("<I", text, off, (BASES[sn] + val + add) & 0xFFFFFFFF)
        elif t == THM_CALL:
            P = BASES[".text"] + off + 4
            S = sym_addr(sym) & ~1
            disp = S - P
            imm = (disp >> 1) & 0x3FFFFF
            s = (imm >> 21) & 1
            i1 = (imm >> 20) & 1
            i2 = (imm >> 19) & 1
            j1 = (~i1 & 1) ^ s
            j2 = (~i2 & 1) ^ s
            imm10 = (imm >> 11) & 0x3FF
            imm11 = imm & 0x7FF
            hi = 0xF000 | (s << 10) | imm10
            lo = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
            struct.pack_into("<HH", text, off, hi, lo)
        else:
            print(f"FAIL: unhandled relocation type {t} at {off:#x} — vacuous-gate risk")
            return 1

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    for _, base in BASES.items():
        mu.mem_map(base, MAPSZ)
    mu.mem_write(BASES[".text"], bytes(text))
    for nm in (".data", ".rodata"):
        s = e.get_section_by_name(nm)
        if s is not None:
            mu.mem_write(BASES[nm], bytes(s.data()))
    bss = e.get_section_by_name(".bss")
    bss_size = bss["sh_size"] if bss is not None else 0
    RET = BASES[".text"] + 0xFF0
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")

    def run_arm(fn, arg):
        for nm in (".data", ".rodata"):
            s = e.get_section_by_name(nm)
            if s is not None:
                mu.mem_write(BASES[nm], bytes(s.data()))
        if bss_size:
            mu.mem_write(BASES[".bss"], b"\x00" * bss_size)
        mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R11, 0)
        mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + MAPSZ - 0x100)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        entry = BASES[".text"] + (syms[fn][1] & ~1)
        mu.emu_start(entry | 1, RET, timeout=5_000_000)
        return mu.reg_read(UC_ARM_REG_R0)

    ok = True
    for i in range(11):
        exp = wasmtime_truth("copy_peek", i)
        try:
            got = run_arm("copy_peek", i)
        except UcError as ex:
            print(f"copy_peek({i}) = UNICORN FAULT {ex} (expect {exp:#x})")
            ok = False
            continue
        match = "" if got == exp else "  <-- MISMATCH"
        print(f"copy_peek({i}) = {got:#x} (expect {exp:#x} {chr(exp) if 32<=exp<127 else '.'!r}){match}")
        ok &= got == exp

    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
