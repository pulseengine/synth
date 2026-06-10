#!/usr/bin/env python3
"""#237 shadow-stack differential: the gmutex frame shape under --native-pointer-abi.

Compile:
  synth compile scripts/repro/native_pointer_shadow_stack.wat -o /tmp/np_ss.elf \
        --target cortex-m4 --native-pointer-abi --all-exports --relocatable
Run:
  /tmp/armv/bin/python scripts/repro/native_pointer_shadow_stack_differential.py /tmp/np_ss.elf

Asserts: frame_roundtrip(v) == v (the store through the moved shadow-stack
pointer lands INSIDE __synth_wasm_data, not at 0xFFFFFFF4), and the
__synth_globals SP slot is restored to its init (4096) on return.
"""
import struct, sys
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R11, UC_ARM_REG_LR,
                               UC_ARM_REG_SP, UC_ARM_REG_PC)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/np_ss.elf"
CODE, DATA, STK = 0x10000, 0x40000, 0x90000

e = ELFFile(open(ELF, "rb"))
text = bytearray(e.get_section_by_name(".text").data())
data = bytearray(e.get_section_by_name(".data").data())

syms = {}
for sec in e.iter_sections():
    if sec["sh_type"] == "SHT_SYMTAB":
        for s in sec.iter_symbols():
            syms[s.name] = s["st_value"]

def patch_movwt(code, off, value16):
    hw1, hw2 = struct.unpack_from("<HH", code, off)
    imm4, i = (value16 >> 12) & 0xF, (value16 >> 11) & 1
    imm3, imm8 = (value16 >> 8) & 0x7, value16 & 0xFF
    hw1 = (hw1 & ~0x040F) | (i << 10) | imm4
    hw2 = (hw2 & ~0x70FF) | (imm3 << 12) | imm8
    struct.pack_into("<HH", code, off, hw1, hw2)

# synth labels its Thumb MOVW/MOVT relocations with the ARM32 type numbers
# (43/44) — patch them with the THUMB bit layout (what the encoder emitted).
MOVW_TYPES, MOVT_TYPES = (43, 47), (44, 48)
rel = e.get_section_by_name(".rel.text")
symtab = [sec for sec in e.iter_sections() if sec["sh_type"] == "SHT_SYMTAB"][0]
for r in rel.iter_relocations():
    t = r["r_info_type"]
    if t not in MOVW_TYPES + MOVT_TYPES:
        continue
    sym = symtab.get_symbol(r["r_info_sym"])
    # addend is encoded in the instruction's current imm16 (REL, not RELA)
    hw1, hw2 = struct.unpack_from("<HH", text, r["r_offset"])
    add = ((hw1 & 0xF) << 12) | (((hw1 >> 10) & 1) << 11) | (((hw2 >> 12) & 0x7) << 8) | (hw2 & 0xFF)
    target = DATA + syms[sym.name] + add
    patch_movwt(text, r["r_offset"], (target & 0xFFFF) if t in MOVW_TYPES else (target >> 16) & 0xFFFF)

mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
for base, blob in ((CODE, text), (DATA, data)):
    mu.mem_map(base, 0x10000)
    mu.mem_write(base, bytes(blob))
mu.mem_map(STK, 0x10000)

entry = CODE + syms["frame_roundtrip"]
RET = CODE + 0xFFF0  # mapped pad inside the code mapping (gotcha from #220)
mu.mem_write(RET, b"\x00\xbf\x00\xbf")
ok = True
for v in (7, -123456, 0x7FFFFFFF):
    mu.reg_write(UC_ARM_REG_R0, v & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R11, 0)          # native deref: r11 = 0
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start(entry | 1, RET, timeout=5_000_000)
    got = mu.reg_read(UC_ARM_REG_R0)
    exp = v & 0xFFFFFFFF
    sp_slot = struct.unpack("<i", mu.mem_read(DATA + syms["__synth_globals"], 4))[0]
    line = f"frame_roundtrip({v}) = {got:#x} (expect {exp:#x}), SP slot after = {sp_slot} (expect 4096)"
    print(line)
    ok &= (got == exp) and (sp_slot == 4096)
print("ORACLE: PASS" if ok else "ORACLE: FAIL")
sys.exit(0 if ok else 1)
