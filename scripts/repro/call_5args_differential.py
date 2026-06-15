#!/usr/bin/env python3
"""#359 differential: a 5-argument call must pass ALL five args (caller/callee agree).

The callee packs each arg into a distinct nibble (a | b<<4 | c<<8 | d<<12 | e<<16),
so ANY dropped / shifted / mis-assigned argument changes the result — unlike a
"return arg1" probe, this catches a wrong outgoing-stack slot or a wrong
incoming-param offset on the 5th arg too.

Compile:
  synth compile scripts/repro/call_5args.wat -o /tmp/c5.o \
        --target cortex-m4f --native-pointer-abi --all-exports --relocatable
Run:
  /tmp/armv2/bin/python scripts/repro/call_5args_differential.py /tmp/c5.o

Ground truth is the wasm semantics (computed directly). Unicorn runs synth's
ARM. Before the #359 fix the caller drops arg1 and never stack-passes arg5, so
the result diverges; after, it matches for every vector.
"""
import struct
import sys

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (
    UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
    UC_ARM_REG_R11, UC_ARM_REG_LR, UC_ARM_REG_SP, UC_ARM_REG_PC,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/c5.o"
CODE, DATA, STK = 0x10000, 0x40000, 0x90000
RET_PAD = CODE + 0x4000  # a mapped, even (ARM) address LR points at; we stop there

e = ELFFile(open(ELF, "rb"))
text = bytearray(e.get_section_by_name(".text").data())
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}


def encode_thm_bl(pc, target):
    """Thumb-2 BL: encode (target - (pc+4)) as the S/J1/J2/imm10/imm11 form."""
    off = target - (pc + 4)
    off &= 0x1FFFFFF  # 25-bit signed range
    s = (off >> 24) & 1
    i1 = (off >> 23) & 1
    i2 = (off >> 22) & 1
    imm10 = (off >> 12) & 0x3FF
    imm11 = (off >> 1) & 0x7FF
    j1 = (~i1 & 1) ^ s
    j2 = (~i2 & 1) ^ s
    hw1 = 0xF000 | (s << 10) | imm10
    hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
    return hw1, hw2


# Resolve the internal THM_CALL (caller -> func_N): patch the BL in place so the
# emulated branch lands on the callee, exactly as `ld` would.
rel = e.get_section_by_name(".rel.text")
for r in rel.iter_relocations():
    t = r["r_info_type"]
    if t in (10, 30):  # R_ARM_THM_CALL / R_ARM_THM_JUMP24
        sym = symtab.get_symbol(r["r_info_sym"])
        target = CODE + (syms[sym.name] & ~1)  # clear thumb bit
        off = r["r_offset"]
        pc = CODE + off
        hw1, hw2 = encode_thm_bl(pc, target)
        struct.pack_into("<HH", text, off, hw1, hw2)
    else:
        raise SystemExit(f"unexpected reloc type {t}; harness only handles THM_CALL")


def run_caller(a, b, c, d, ee):
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    uc.mem_map(CODE, 0x10000)
    uc.mem_map(DATA, 0x10000)
    uc.mem_map(STK, 0x10000)
    uc.mem_write(CODE, bytes(text))
    sp = STK + 0x8000
    # AAPCS: args 1..4 in r0..r3, arg5 (ee) on the incoming stack at [sp].
    sp -= 8  # keep 8-byte alignment; arg5 at [sp+0]
    uc.mem_write(sp, struct.pack("<I", ee & 0xFFFFFFFF))
    uc.reg_write(UC_ARM_REG_SP, sp)
    uc.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R2, c & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R3, d & 0xFFFFFFFF)
    uc.reg_write(UC_ARM_REG_R11, DATA)  # linmem base
    uc.reg_write(UC_ARM_REG_LR, RET_PAD | 1)
    entry = CODE + (syms["caller"] & ~1)
    uc.emu_start(entry | 1, RET_PAD, timeout=0, count=2000)
    return uc.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def expected(a, b, c, d, ee):
    return (a | (b << 4) | (c << 8) | (d << 12) | (ee << 16)) & 0xFFFFFFFF


VECTORS = [
    (1, 2, 3, 4, 5),
    (15, 14, 13, 12, 11),
    (9, 0, 7, 0, 3),
    (0, 0, 0, 0, 1),   # only arg5 set — catches a dropped/zeroed 5th arg
    (1, 0, 0, 0, 0),   # only arg1 set — catches the historical arg1 drop
]

ok = 0
for v in VECTORS:
    got = run_caller(*v)
    exp = expected(*v)
    flag = "OK" if got == exp else "MISMATCH"
    if got == exp:
        ok += 1
    print(f"caller{v} = 0x{got:05X}  (expect 0x{exp:05X})  {flag}")

print(f"\n{ok}/{len(VECTORS)} match")
print("ORACLE: PASS" if ok == len(VECTORS) else "ORACLE: FAIL")
sys.exit(0 if ok == len(VECTORS) else 1)
