#!/usr/bin/env python3
"""#707 multi-provider shared-memory fused node: N `__stack_pointer` globals all
init == sp_init, co-rebased by `--shadow-stack-size`.

A `meld fuse --memory shared` node keeps each fused component's own
`__stack_pointer` global, so the module carries N mutable i32 globals ALL
initialized to the same stack top. `--shadow-stack-size B` used to REFUSE (could
not pick a unique SP global); #707 re-bases the whole equivalence class to B
(they alias the one shared reservation).

This differential validates the co-rebase is runtime-correct: each of the three
exports f0/f1/f2 does an independent shadow-stack roundtrip through its OWN SP
global (sp0/sp1/sp2). After the shrink every SP slot inits to B, each roundtrip
must (a) return its input v (the store landed at the re-based frame and read
back) and (b) restore its own SP slot to B on return. Run each export on a fresh
instance — exactly wasmtime's per-call semantics — so the three aliasing stacks
never overlap in time.

Compile (co-rebased):
  synth compile scripts/repro/mem707_multi_sp.wat -o /tmp/mem707.o \
        --target cortex-m3 --native-pointer-abi --all-exports --relocatable \
        --shadow-stack-size 512
Run:
  <venv>/bin/python scripts/repro/multi_sp_707_differential.py /tmp/mem707.o [expected_sp_init]
"""
import struct
import sys

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_LR,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/mem707.o"
# The re-based SP init the slots must hold after each roundtrip (budget B, or the
# original 4096 with no flag). Defaults to the shrunk budget the doc-comment uses.
EXP_SP = int(sys.argv[2]) if len(sys.argv) > 2 else 512
ABS32 = 2

# Native-pointer derefs are absolute (R11 = 0). Map a LOW page at 0 to cover the
# shadow-stack reservation [0, B) the frames live in, plus the usual code/data.
LOW, CODE, DATA = 0x0, 0x10000, 0x40000
MAPSZ = 0x10000

e = ELFFile(open(ELF, "rb"))
text = bytearray(e.get_section_by_name(".text").data())
data = bytearray(e.get_section_by_name(".data").data())

symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}

# Relocate every R_ARM_ABS32 literal-pool word in place (REL: final = base + sym
# + in-place addend). `__synth_globals` lives in .data; text/code stay in .text.
secname_by_idx = {i: s.name for i, s in enumerate(e.iter_sections())}
for r in e.get_section_by_name(".rel.text").iter_relocations():
    if r["r_info_type"] != ABS32:
        continue
    sym = symtab.get_symbol(r["r_info_sym"])
    shndx = sym["st_shndx"]
    base = DATA if secname_by_idx.get(shndx) == ".data" else CODE
    (add,) = struct.unpack_from("<I", text, r["r_offset"])
    struct.pack_into("<I", text, r["r_offset"], (base + sym["st_value"] + add) & 0xFFFFFFFF)

mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
for base in (LOW, CODE, DATA):
    mu.mem_map(base, MAPSZ)
mu.mem_write(CODE, bytes(text))

RET = CODE + 0xFFF0
mu.mem_write(RET, b"\x00\xbf\x00\xbf")

GLOBALS = DATA + syms["__synth_globals"]
ok = True
for fn, slot in (("f0", 0), ("f1", 1), ("f2", 2)):
    entry = CODE + syms[fn]
    for v in (7, -123456, 0x7FFFFFFF, 0):
        # Fresh instance per call: re-init the .data global slots + zero the LOW
        # reservation, exactly as wasmtime instantiates fresh each invocation.
        mu.mem_write(DATA, bytes(data))
        mu.mem_write(LOW, b"\x00" * MAPSZ)
        mu.reg_write(UC_ARM_REG_R0, v & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R11, 0)  # native deref base = 0
        mu.reg_write(UC_ARM_REG_SP, DATA + 0x8000)  # a real machine SP pad
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        mu.emu_start(entry | 1, RET, timeout=5_000_000)
        got = mu.reg_read(UC_ARM_REG_R0)
        exp = v & 0xFFFFFFFF
        sp_slot = struct.unpack("<i", mu.mem_read(GLOBALS + slot * 4, 4))[0]
        ok_run = got == exp and sp_slot == EXP_SP
        ok &= ok_run
        print(
            f"{fn}({v}) = {got:#x} (expect {exp:#x}), sp{slot} slot after = "
            f"{sp_slot} (expect {EXP_SP})  {'OK' if ok_run else 'MISMATCH'}"
        )

# The immutable `$konst` (slot 3) coincides with sp_init but is NOT a stack
# pointer — the shrink must leave it at its original 4096, and getk() must
# still return 4096 (re-basing it would corrupt a program constant).
mu.mem_write(DATA, bytes(data))
mu.mem_write(LOW, b"\x00" * MAPSZ)
mu.reg_write(UC_ARM_REG_R11, 0)
mu.reg_write(UC_ARM_REG_SP, DATA + 0x8000)
mu.reg_write(UC_ARM_REG_LR, RET | 1)
mu.emu_start((CODE + syms["getk"]) | 1, RET, timeout=5_000_000)
getk = mu.reg_read(UC_ARM_REG_R0)
konst_slot = struct.unpack("<i", mu.mem_read(GLOBALS + 3 * 4, 4))[0]
ok_konst = getk == 4096 and konst_slot == 4096
ok &= ok_konst
print(
    f"getk() = {getk} (expect 4096), konst slot = {konst_slot} (expect 4096, "
    f"immutable — never re-based)  {'OK' if ok_konst else 'MISMATCH'}"
)

print("ORACLE: PASS" if ok else "ORACLE: FAIL")
sys.exit(0 if ok else 1)
