#!/usr/bin/env python3
"""VCR-MEM-001 layer-2 (#678) execution differential: inline linmem statics
down-shifted into `.data`/`.bss` under `--native-pointer-abi --shadow-stack-size`.

A buffer-carrying dissolved node reads THREE kinds of static under the shrunk
reservation, all in one function:
  * an initialized `(data)` segment (wit-bindgen `list<u8>` literal) — retargeted
    to `__synth_wasm_seg_0` in `.data`;
  * a zero-init BSS static (`static mut` array) at a non-zero addend in the tail —
    DOWN-SHIFTED `C -> C - (sp_init - budget)` into the `.bss` reservation;
  * a shadow-stack slot reached through `global.get $sp` (addend-0 region base +
    the re-based `__synth_globals` SP slot).

Compile:
  synth compile scripts/repro/mem678_full.wat -o /tmp/mem678_full.o \
        --target cortex-m3 --native-pointer-abi --all-exports --relocatable \
        --shadow-stack-size 512
Run:
  <venv>/bin/python scripts/repro/native_pointer_static_downshift_678.py /tmp/mem678_full.o

Asserts run(p) == 43 + 2*p (wasmtime ground truth) for several p — i.e. the
down-shifted BSS read, the retargeted `.data` segment read, and the re-based SP
slot all land at the correct addresses after the shrink.
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

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/mem678_full.o"
ABS32 = 2

# Distinct bases for each linker-placed region — this is the whole point: the
# `.bss` reservation and the packed `.data` are SEPARATE sections at separate
# addresses (the old single-`.data` harness could not express the down-shift).
BASES = {".text": 0x10000, ".bss": 0x40000, ".data": 0x60000}
MAPSZ = 0x10000

e = ELFFile(open(ELF, "rb"))
secname_by_idx = {i: s.name for i, s in enumerate(e.iter_sections())}
text = bytearray(e.get_section_by_name(".text").data())
data = bytearray(e.get_section_by_name(".data").data())
bss_size = e.get_section_by_name(".bss")["sh_size"]

symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {}
for s in symtab.iter_symbols():
    syms[s.name] = (s["st_shndx"], s["st_value"])

# Relocate every R_ARM_ABS32 literal-pool word in place: final address =
# base(section owning the symbol) + symbol value + in-place addend (REL).
for r in e.get_section_by_name(".rel.text").iter_relocations():
    if r["r_info_type"] != ABS32:
        continue
    sym = symtab.get_symbol(r["r_info_sym"])
    shndx, val = syms[sym.name]
    base = BASES[secname_by_idx[shndx]]
    (add,) = struct.unpack_from("<I", text, r["r_offset"])
    struct.pack_into("<I", text, r["r_offset"], (base + val + add) & 0xFFFFFFFF)

mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
for name, base in BASES.items():
    mu.mem_map(base, MAPSZ)
mu.mem_write(BASES[".text"], bytes(text))
mu.mem_write(BASES[".data"], bytes(data))
# .bss starts zeroed (NOBITS) — exactly wasm's zero-init semantics.

entry = BASES[".text"] + syms["run"][1]
RET = BASES[".text"] + 0xFF0
mu.mem_write(RET, b"\x00\xbf\x00\xbf")

ok = True
for p in (0, 7, 100, -5):
    # Re-zero .bss between runs (fresh wasm instance per wasmtime invocation).
    mu.mem_write(BASES[".bss"], b"\x00" * bss_size)
    mu.reg_write(UC_ARM_REG_R0, p & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R11, 0)  # native deref: fp/base = 0
    mu.reg_write(UC_ARM_REG_SP, BASES[".bss"] + 0x8000)  # a real machine SP pad
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start(entry | 1, RET, timeout=5_000_000)
    got = mu.reg_read(UC_ARM_REG_R0)
    exp = (43 + 2 * p) & 0xFFFFFFFF
    print(f"run({p}) = {got} (expect {exp})")
    ok &= got == exp

print("ORACLE: PASS" if ok else "ORACLE: FAIL")
sys.exit(0 if ok else 1)
