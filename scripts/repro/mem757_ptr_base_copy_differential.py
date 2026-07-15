#!/usr/bin/env python3
"""#757 RED-FIRST differential — memmove (`memory.copy`) from a STATIC pointer.

gale's real mechanism: a RawVec-grow `call` followed by a `memory.copy` whose
SOURCE operand is a static pointer const `data_base + 0x20` (a `&STATIC_STR`),
relocated by the native-pointer ABI to `__synth_wasm_data + 0x20`. With low
consts filling `[data_base, data_base+0x20)`, a wrong source addend reads the
LOW consts [2,0,0,0,...] instead of "gust:os".

This differs from the six 0.43.0 controls: those used i64.load/i64.store chunks
with the offset folded into the MEMARG. gale's memmove passes the source as a
relocated CONST POINTER through `memory.copy`.

Unlike the separated-section harness, this maps linear memory as ONE contiguous
region (R11 = 0 native deref, so wasm addr == absolute addr) and pins the
`__synth_wasm_data` symbol at its wasm base 0x100000, so a runtime dst pointer
(0x101000) and a relocated src pointer stay in the same address space — this is
faithful to the deployed native-pointer image, where linear memory IS one block.
Resolves R_ARM_ABS32 (2) and R_ARM_THM_CALL (10); an unresolved bl self-corrupts.

Run:
  SYNTH=./target/debug/synth python scripts/repro/mem757_memcopy_static_src_differential.py
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

WAT = Path(__file__).with_name("mem757_ptr_base_copy.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
BUDGET = 2048
ABS32 = 2
THM_CALL = 10

# One contiguous 8 MiB linear-memory image at LINBASE; .text placed just below
# it. `__synth_wasm_data` symbol is pinned at DATABASE (= wasm data base 0x100000
# offset into the image) so relocated static pointers and runtime dst pointers
# share the address space, exactly as in the deployed native image.
TEXT = 0x00080000
LINBASE = 0x00100000  # wasm addr 0 -> here? No: native ABI uses R11=0, wasm addr == absolute.
MAPSZ = 0x00400000


def wasmtime_truth(fn, arg):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, WAT.read_text())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    return inst.exports(store)[fn](store, arg) & 0xFFFFFFFF


def main():
    obj = Path(tempfile.mkdtemp(prefix="mem757pb_")) / "mem757pb.o"
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

    # Native-pointer image: wasm address A resolves to absolute A (R11 = 0).
    # `__synth_wasm_data` and any `__synth_wasm_seg_*` region symbols are the
    # wasm data base (0x100000) plus the symbol's st_value, so a relocated
    # static pointer equals its wasm address.
    WDB = 0x100000  # wasm data base

    def sym_abs(name):
        shndx, val = syms[name]
        sn = secname.get(shndx, ".text")
        if sn == ".text":
            return TEXT + val
        # data/rodata/bss region symbols: st_value is the wasm OFFSET into the
        # linear image; absolute = wasm_data_base + offset (R11 = 0 native ABI).
        return WDB + val

    for r in e.get_section_by_name(".rel.text").iter_relocations():
        t = r["r_info_type"]
        sym = symtab.get_symbol(r["r_info_sym"])
        off = r["r_offset"]
        if t == ABS32:
            (add,) = struct.unpack_from("<I", text, off)
            struct.pack_into("<I", text, off, (sym_abs(sym.name) + add) & 0xFFFFFFFF)
        elif t == THM_CALL:
            P = TEXT + off + 4
            S = sym_abs(sym.name) & ~1
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
            print(f"FAIL: unhandled relocation type {t} at {off:#x}")
            return 1

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(TEXT, 0x80000)  # code below linear memory
    mu.mem_map(LINBASE, MAPSZ)  # one contiguous linear-memory image
    mu.mem_write(TEXT, bytes(text))
    RET = TEXT + 0x70000
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")

    # Initialize the static data at its wasm addresses inside the linear image.
    def init_lin():
        mu.mem_write(LINBASE, b"\x00" * MAPSZ)
        for nm in (".data", ".rodata"):
            s = e.get_section_by_name(nm)
            if s is None:
                continue
            # region symbol wasm offset for this section (0 default)
            off = 0
            for sname, (shndx, val) in syms.items():
                if sname.startswith("__synth_wasm_seg") and secname.get(shndx) == nm:
                    off = val
                    break
            mu.mem_write(WDB + off, bytes(s.data()))

    def run_arm(fn, arg):
        init_lin()
        mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R11, 0)
        mu.reg_write(UC_ARM_REG_SP, LINBASE + MAPSZ - 0x100)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        entry = TEXT + (syms[fn][1] & ~1)
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
        ec = chr(exp) if 32 <= exp < 127 else "."
        print(f"copy_peek({i}) = {got:#x} (expect {exp:#x} {ec!r}){match}")
        ok &= got == exp

    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
