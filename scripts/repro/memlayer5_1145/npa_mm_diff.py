"""Scratch differential: run a --native-pointer-abi --relocatable 2-memory
object under unicorn (R11 = 0 native deref, ABS32 relocs patched to distinct
per-section bases) and compare every export against wasmtime multi-memory."""
import struct, sys
import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import Uc, UcError, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R11, UC_ARM_REG_R10, UC_ARM_REG_LR, UC_ARM_REG_SP

WAT, OBJ = sys.argv[1], sys.argv[2]
import os, json
BASES = json.loads(os.environ.get("BASES", "null")) or {".text": 0x10000, ".bss": 0x100000, ".data": 0x200000, ".synth.wasm_mem_1": 0x400000}
CASES = [("read1_static", []), ("read1_ctrl", []), ("read0_static", []),
         ("read1_dyn", [0x2000]), ("read1_dyn", [0x2004]),
         ("write1_read0", [0x5A5A5A5A]), ("write1_read1", [0x5A5A5A5A])]

def truth(fn, args):
    cfg = wasmtime.Config(); cfg.wasm_multi_memory = True
    eng = wasmtime.Engine(cfg); st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, open(WAT).read()), [])
    return inst.exports(st)[fn](st, *args) & 0xFFFFFFFF

e = ELFFile(open(OBJ, "rb"))
secs = {i: s for i, s in enumerate(e.iter_sections())}
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s for s in symtab.iter_symbols()}
text = bytearray(e.get_section_by_name(".text").data())
nrel = 0
for r in e.get_section_by_name(".rel.text").iter_relocations():
    if r["r_info_type"] != 2:
        print(f"unexpected reloc type {r['r_info_type']}"); sys.exit(2)
    sym = symtab.get_symbol(r["r_info_sym"])
    sname = secs[sym["st_shndx"]].name
    (add,) = struct.unpack_from("<I", text, r["r_offset"])
    struct.pack_into("<I", text, r["r_offset"], (BASES[sname] + sym["st_value"] + add) & 0xFFFFFFFF)
    nrel += 1
print(f"patched {nrel} ABS32 relocs")
mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
for name, base in BASES.items():
    sec = e.get_section_by_name(name)
    size = max(sec["sh_size"], 0x1000) if sec is not None else 0x1000
    mu.mem_map(base, (size + 0xFFFF) & ~0xFFFF)
mu.mem_map(0x800000, 0x10000)  # host stack
RET = BASES[".text"] + 0xFF0
def reset():
    mu.mem_write(BASES[".text"], bytes(text)); mu.mem_write(RET, b"\x00\xbf\x00\xbf")
    for name in (".data", ".synth.wasm_mem_1"):
        mu.mem_write(BASES[name], e.get_section_by_name(name).data())
    b = e.get_section_by_name(".bss"); mu.mem_write(BASES[".bss"], b"\0" * b["sh_size"])
ok = True
for fn, args in CASES:
    exp = truth(fn, args)
    reset()
    for i, a in enumerate(args): mu.reg_write(UC_ARM_REG_R0 + i, a)
    mu.reg_write(UC_ARM_REG_R11, 0); mu.reg_write(UC_ARM_REG_R10, 0x10000)
    mu.reg_write(UC_ARM_REG_SP, 0x80FF00); mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((BASES[".text"] + (syms[fn]["st_value"] & ~1)) | 1, RET, timeout=2_000_000)
        got = mu.reg_read(UC_ARM_REG_R0)
    except UcError as ex:
        print(f"{fn}{tuple(args)} = FAULT {ex}  expect {exp:#x}  <-- MISMATCH"); ok = False; continue
    tag = "" if got == exp else "  <-- MISMATCH"
    print(f"{fn}{tuple(hex(a) for a in args)} = {got:#x}  expect {exp:#x}{tag}"); ok &= got == exp
print("ORACLE: PASS" if ok else "ORACLE: FAIL"); sys.exit(0 if ok else 1)
