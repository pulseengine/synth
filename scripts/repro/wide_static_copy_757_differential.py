#!/usr/bin/env python3
"""#757 investigation harness — the multi-chunk static-copy differential.

#757 reported a SILENT MISCOMPILE regression from the #746 fix: a chunked copy
of a static string (>= 9 bytes, above `wasm_data_base`, under
`--native-pointer-abi --shadow-stack-size`) was claimed to copy the HEAD chunk
wrong (source address offset past the string) while the TAIL read correctly —
i.e. the per-chunk source-address RELOCATION addend was wrong for the first
chunk.

This harness runs the compiled object under unicorn (Thumb-2, R11 = 0 native
deref, `.bss`/`.data`/`.rodata` at SEPARATE bases so a baked absolute linmem
offset cannot accidentally resolve) against wasmtime ground truth, for a
`copy_peek(i)` export that copies a static string into a dynamic `.bss` dest and
reads byte `i` back.

CRITICAL — it resolves R_ARM_THM_CALL (type 10) relocations, not just
R_ARM_ABS32 (type 2). The gale shape reaches its copy loop THROUGH a `call`
(RawVec-grow), so an object with an unresolved `bl` self-calls and corrupts
state — an emulation artifact that MASQUERADES as a miscompile. An oracle that
skips the call relocation is a vacuous gate (the memory-note lesson). Resolving
it is what turned the apparent RED back to GREEN and disproved the triage
mechanism.

FINDING (0.43.0): every faithful reconstruction of the gale shape — symmetric
i64 head+tail, asymmetric wide-head/narrow-tail, const-index, const-source,
`memory.copy`, high-pressure loop, and the value-live-across-call control below
— compiles CORRECTLY: the relocation addend AND the runtime base register are
both right, execution matches wasmtime byte-for-byte. The triage's "head-chunk
addend is wrong" hypothesis does not hold for any reproducible shape.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/wide_static_copy_757_differential.py
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

WAT = Path(__file__).with_name("mem757_static_copy_controls.wat")
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
    obj = Path(tempfile.mkdtemp(prefix="mem757_")) / "mem757.o"
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
            # R_ARM_THM_CALL: encode a full Thumb BL to (S - P) — overwrite the
            # f7ff fffe placeholder outright (do NOT re-add its -4 addend).
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
        print(f"copy_peek({i}) = {got:#x} (expect {exp:#x}){match}")
        ok &= got == exp

    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
